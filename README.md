# SimpleFP-v2

A re-do of the SimpleFP repo using de Bruijn index ABTs instead of HOAS.

Each file is also now heavily documented in a literate style, and where applicable, there are formal type theoretic specs for the implemented functionality. The specs are more-or-less the real ones, in that they're real enough to make it clear what's going on, without also writing down every little detail.

The variants should be read in the following order, going from simplest to most complex:

1.  *Simple*

    This variant implements just a very simple programming language with function types and non-parameteric user defined types.

2.  *Poly*

    This variant extends Simple by adding parametric types and polymorphic quantification types.
    
3.  *Dependent*

    This variant implements a dependently typed programming language with only explicit arguments to functions. It's not very user friendly because everything has to be written explicitly.
    
4.  *DependentImplicit*

    This variant extends Dependent with implicit arguments to functions and constructors. This makes it much more user friendly.
    
5.  *Modular*

    This variant extends DependentImplicit by adding a very simple module system. Modules have just names, no parameters, and there's no notion of exports, signatures, or anything more advanced.
    
6.  *Record*

    This variant extends Modular by adding basic anonymous record types. There is no fancy subtyping going on, so records can only be used for precisely the type they're defined at, not any smaller record type.
    
7.  *OpenDefs*

    This variant extends Record by adding open types and open functions.
    
8.  *Quasiquote*

    This variant extends OpenDefs by adding quasiquoting. The type system for this variant is somewhat different than all of the previous ones because quotation requires a different judgmental framework. Whereas previous variants were built out of the judgment `A true`, the Quasiquote variant uses the judgment `A at l`, where `l` is a quotation level/depth. This is based on the temporal logic type theory of Rowan Davies, which you can read [here](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.28.4374).

9.  *Continuations*

    This variant extends Quasiquote by adding delimited continuations. Within a quoted term, it's possible to use shift-reset style delimited continuations to define terms. However, unlike normal shift-reset continuations, shift and reset don't pair up with names. Instead, each shift and reset declares what kind of continuation it's for. Each reset will catch all the maximal shifts inside it's scope, rather than just a single reset.
    
    So, for example, the term `reset k in (shift k. forall x. continue x) < (shift k. exists y. continue y)` would reset to `forall x. exists y. x < y` because both shifts use the same reset point `k`. Resetting is done left-to-right in normal applicative style. Reverse order requires flipping, eg `reset k in flip (<) (shift k. exists y. continue y) (shift k. forall x. continue x)` resets to `exists y. forall x. x < y`.
    
    Additionally, quotes can bind reset points, so that `Quote[k] A` is a quoted `A` that is allowed to use the reset point `k`. So if `k` is a Nat-Nat reset point as in the above examples, the quoted term `` `(shift k. forall x. continue x)`` has the type `Quote[k] Nat`. Unquoting is therefore only possible when the environment of the unquote has appropriate reset points in scope. The term `` `(shift k. forall k. continue k)`` can therefore unquote under at least one reset for `k` but not under 0 unless `k` is again bound by a higher quote.
    
    This variant also comes with a new module `Continuations.Core.Decontinuization` which defines the necessary toolkit to remove continuations from a term that uses continuations. The idea here being, a program of type `Quote A` computes an `A` which might uses continuations. Unwrapping that term removes a quote level, thereby necessitating the removal also of the continuations that it contained. So, given a closed term `M : Quote A at 0`, we know that it must evaluate to `` `N`` for some `N`. But `N` by itself will not be a proof of `A at 0` because it uses continuations. however `decontinuize N` will. Viewed from the perspective of temporal logic, we can take a term at the next moment and step forward in time one moment by unwrapping that term, but in the process we need to decontinuize so that the unwrapped term is still a valid term at the new moment.
    
    Before decontinuization, the unwrapped term is merely quoted (at least formerly so), and so it's not guaranteed to be normal. Indeed, if it contains continuations, it's not yet normalizable. Decontinuization therefore converts a just-unquoted term into something which can be normalized. The demo file shows one such term, of type @Quote Nat@ with no captured reset points, namely
    
        `(reset natR
          in Suc (Suc (shift natR
                       in plus (continue Zero)
                               (continue (Suc Zero)))))
    
    After unwrapping and decontinuizing, this becomes
    
        plus (Suc (Suc Zero))
             (Suc (Suc (Suc Zero)))
    
    which will then normalize to `Suc (Suc (Suc (Suc (Suc Zero))))`. In more readable notation:
    
        `(reset natR
          in 2 + (shift natR in continue 0 + continue 1))
          
    unwrapping and decontinuizing to `(2 + 0) + (2 + 1)` which evaluates to `5`.

10. *Require*
    
    This variant extends the continuation variant with `require` expressions that can be solved after decontinuization. A require is like a let expression, only instead of the programmer supplying the value of a variable, the solver will provide one. So for example, the term `require x : Nat in x` is a `Nat`, provided that the solver can find one in scope to provide. The solver provided in `RequireSolving` will only find solutions in the terms provided upfront as resources, plus whatever is brought into scope by function types, however. It solves by decomposing what's in scope projectors (if the item has a record time), or else leaving it alone, and then by picking an appropriate value, or constructing a record of the right sort, as solutions. It won't use any other elims or intros to solve a require.

Within each variant, the Core files define the language independent of any type checking and elaboration. The Monadic and Unification files define different kinds of type checkers. Monadic (when it exists) doesn't use any sort of unification for equality. This is only possible in simple situations, and even then it's sometimes unpleasant because you need a lot of type annotation. Unification uses a unifier to enforce equality, which makes it possible to use implicit types/data in all sorts of places, making the  languages much more user friendly. It also permits certain things to be inferable that otherwise wouldn't be.

To use any given variant, load its REPL module and run it. For instance:

  Quasiquote.Unification.REPL.replFile "src/Quasiquote/Demo.sfp"

This presents you with a very basic REPL that will parse the input you give  it, infer its type, and then evaluate it. If you use the `replFile` function as above, it loads the specified source file and makes the definitions available for use. In variants with modulars, all the definitions are scoped to the modules, requiring you to use their full `Module.name` form.