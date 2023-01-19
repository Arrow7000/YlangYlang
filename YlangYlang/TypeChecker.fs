module TypeChecker


open ConcreteSyntaxTree
open Lexer


module Cst = ConcreteSyntaxTree



(*

@TODO list

- [ ] resolve named values
    - [ ] in local scopes
    - [ ] from other modules
- [ ] infer types of primitives
- [ ] infer types of values referencing primitives
- [ ] infer types of

- [ ] parse type annotations
- [ ] infer types of values or function params by looking at the functions they are getting passed into
    - [ ] and similarly the types of values passed to operators

- [ ] support flagging up type clashes
    - [ ] and have some way of linking that back to a specific token, or even buffer range?

- [ ] support types with type params, e.g. `List a`
- [ ] support narrowing of types with type params while leaving the type params as generic

- [ ] support a parallel, field-name-and-value-based, type inference system to support typed records as extensible, partially typed things, instead of the all or nothing type system of generics vs explicit types specified above

*)


/// This will probably be used in a nested way for each of the parameters of a type that has type parameters, to achieve gradual typing of its fields
type NamedValueTypeState<'a> =
    | NotTypedYet
    | GenericWithName of UnqualValueIdentifier
    | SpecificTypeConstraint of 'a
    /// Type clash information with references for where and why each type constraint was inferred from
    | TypeClash of 'a list





type ConcreteOrGenericVar<'a> =
    | Generic of UnqualValueIdentifier
    | Concrete of 'a




// Not sure if it makes sense to have these yet, when we haven't yet enforced that the types are consistent...
// Unless... maybe these type getters can return a Result of either consistent types or of conflicting types, which can then be used for type errors or type hinting or somesuch...?
let typeOfPrimitiveLiteralValue =
    function
    | NumberPrimitive num ->
        match num with
        | FloatLiteral _ -> Float
        | IntLiteral _ -> Int
    | CharPrimitive _ -> Char
    | StringPrimitive _ -> String
    | UnitPrimitive _ -> BuiltInPrimitiveTypes.Unit



type BinaryExpr<'a, 'b> =
    | Left of 'a
    | Right of 'b





type ExpressionWithBoundVariables =
    { boundVars : Map<Identifier, ConcreteOrGenericVar<MentionableType>> } // should probably not be limited to mentionable types, but actual types, the difference being that instead of a referenced type by identifier it should be an actual reference to the newtype



//let typeOfCompoundLiteralValue =
//    function
//    | List
