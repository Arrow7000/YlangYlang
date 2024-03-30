module TypeInferTestHelpers


//module S = SyntaxTree
//module Cst = ConcreteSyntaxTree
//module T = TypedSyntaxTree

//open TypedSyntaxTree
//open TypeChecker
//open QualifiedSyntaxTree.Names
//open Errors

//module Acc = Accumulator
//module Aati = Acc.AccAndTypeId




//let makeAccTypeId () =
//    System.Guid.NewGuid () |> AccumulatorTypeId


//let getType (expr : T.Expression) : TypeJudgment =
//    let result = getAccumulatorFromExpr expr

//    Accumulator.convertAccIdToTypeConstraints result.typeId result.acc
//// @TODO: restore the below when we have a good way of checking/testing for type variable constants – probably by implementing substitution properly
////|> Result.map deleteGuidsFromTypeConstraints



///// Lex, parse, type check, and get the typed expression from a string containing an Elm expression!
//let getTypedExprFromElmStr text : Result<Expression, Errors> =
//    Lexer.tokeniseString text
//    |> Result.mapError LexingError
//    |> Result.bind (
//        ExpressionParsing.run ExpressionParsing.parseExpression
//        >> Parser.toResult
//        >> Result.mapError ParsingError
//    )
//    |> Result.map (convertCstToAst List.empty)



//let getTypeFromElmStr text : Result<TypeConstraints, Errors> =
//    getTypedExprFromElmStr text
//    |> Result.bind (getType >> Result.mapError TypeError)


//let getAccFromElmStr text : Result<Accumulator, Errors> =
//    getTypedExprFromElmStr text
//    |> Result.map (getAccumulatorFromExpr >> Aati.getAcc)






//module TypeDsl =
//    (* Helper functions *)

//    /// Make a list of one or more.
//    /// Will fail if this is given fewer items than that.
//    let nel list =
//        match list with
//        | [] -> failwith "NEL needs to have at least one member"
//        | h :: t -> NEL.new_ h t

//    /// Make a list of two or more.
//    /// Will fail if this is given fewer items than that.
//    let tom list =
//        match list with
//        | []
//        | [ _ ] -> failwith "TOM needs to have at least two members"
//        | h :: n :: t -> TOM.new_ h n t

//    /// Make a set
//    let set list : RefConstr set = Set.ofSeq list




//    /// Make a map from a seq of key/value pairs
//    let map keyvals = Map.ofSeq keyvals


//    /// Make type constraints from a definitive type
//    let def = TypeConstraints.fromDefinitive

//    /// Make type constraints from one reference constraint only
//    let cstr cnstraint =
//        TypeConstraints.TypeConstraints (None, Set.singleton cnstraint)

//    /// Make type constraints from reference constraints only
//    let cstrs constraints =
//        TypeConstraints.TypeConstraints (None, set constraints)

//    /// Make type constraints from definitive type and reference constraints
//    let defCstrs def constraints =
//        TypeConstraints.TypeConstraints (Some def, set constraints)

//    /// Make empty type constraints
//    let none = TypeConstraints.empty

//    let any () = TypeConstraints.makeUnspecific ()


//    /// Make a key/value pair for a record
//    let kv k v = RecordFieldName k, v





//    (* Make constraints *)

//    /// Make a constraint based on value name
//    let v = LowerIdent >> LocalLower >> ByValue

//    /// Make a constraint based on type param
//    let tp = LowerIdent >> ByTypeParam

//    /// Make a constraint based on constructor name
//    let ct = LocalUpper >> ByConstructorType




//    /// Make tuple
//    let (=>) a b = a, b



//    (* Make definitive types *)

//    (* Make primitive types *)
//    /// The Float type
//    let f = DtPrimitiveType Float

//    /// The Int type
//    let i = DtPrimitiveType Int
//    /// The String type
//    let s = DtPrimitiveType String
//    /// The Char type
//    let c = DtPrimitiveType Char
//    /// The Bool type
//    let b = DtPrimitiveType Bool

//    (* Make other types *)
//    // The unit type
//    let unit = DtUnitType
//    let tuple list = DtTuple (tom list)
//    let list t = DtList t
//    let recWith keyvals = DtRecordWith (map keyvals)
//    let recExact keyvals = DtRecordExact (map keyvals)
//    //let newType = DtNewType()
//    let arrow a b = DtArrow (a, b)

//    let rec arrowChain (list : TypeConstraints list) : DefinitiveType =
//        match list with
//        | []
//        | _ :: [] -> failwith "Needs to have at least two items to represent the domain and range"
//        | h :: n :: t ->
//            arrow
//                h
//                (match t with
//                 | [] -> n
//                 | first :: rest -> defCstrs (arrowChain (n :: first :: rest)) [])
