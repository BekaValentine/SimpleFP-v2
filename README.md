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

    This variant extends OpenDefs by adding quasiquoting. The type system for this variant is somewhat different than all of the previous ones because quotation requires a different judgmental framework. Whereas previous variants were built out of the judgment `A true`, the Quasiquote variant uses the judgment `A at l`, where `l` is a quotation level/depth. This is based on the temporal logic type theory of Rowan Davies.

Within each variant, the Core files define the language independent of any type checking and elaboration. The Monadic and Unification files define different kinds of type checkers. Monadic (when it exists) doesn't use any sort of unification for equality. This is only possible in simple situations, and even then it's sometimes unpleasant because you need a lot of type annotation. Unification uses a unifier to enforce equality, which makes it possible to use implicit types/data in all sorts of places, making the  languages much more user friendly. It also permits certain things to be inferable that otherwise wouldn't be.

To use any given variant, load its REPL module and run it. For instance:

  Quasiquote.Unification.REPL.replFile "src/Quasiquote/Demo.sfp"

This presents you with a very basic REPL that will parse the input you give  it, infer its type, and then evaluate it. If you use the `replFile` function as above, it loads the specified source file and makes the definitions available for use. In variants with modulars, all the definitions are scoped to the modules, requiring you to use their full `Module.name` form.