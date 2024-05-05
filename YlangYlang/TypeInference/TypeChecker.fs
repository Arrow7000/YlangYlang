module TypeChecker
// Should maybe call this type inference


//open Lexer

module L = Lexer
module Cst = ConcreteSyntaxTree
module S = SyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open Q.Names
open TypedSyntaxTree

module NameRes = TypedNameResolution

module DG = DependencyGraphs
module NR = NameResolution




/// Alias for unqualified value identifier
type ValIdent = Lexer.UnqualValueIdentifier






/// Make a new unification variable
let private makeNewUniVar () = System.Guid.NewGuid () |> T.UnificationVarId

/// Make a new type variable
let private makeNewTypeVar () = System.Guid.NewGuid () |> T.TypeVariableId





module UnificationVariable =
    let getId (uniVar : UnificationVariable) = uniVar.content.Value.id

    /// Make a new unconstrained unification variable
    let makeNewBlank (levelDeclared : uint) (uniVarId : UnificationVarId) =
        { content =
            ref
                { id = uniVarId
                  levelDeclared = levelDeclared
                  constrained = None } }

    /// Make a new type constrained unification variable
    let makeNewConstr (levelDeclared : uint) (uniVarId : UnificationVarId) (constr : PolyTypeContents) =
        { content =
            ref
                { id = uniVarId
                  levelDeclared = levelDeclared
                  constrained = Some (TypeConstr constr) } }

    /// Make a new record constrained unification variable
    let makeNewRecConstraint
        (levelDeclared : uint)
        (uniVarId : UnificationVarId)
        (fields : (LowerIdent * PolyTypeContents) list)
        =
        { content =
            ref
                { id = uniVarId
                  levelDeclared = levelDeclared
                  constrained = Some (TOR.RecordConstr fields) } }



module Types =
    /// Make a polytypecontents into a polytype with no type vars
    let makePoly ptc = { forall = List.empty; typeExpr = ptc }

    let makePolyWith (typeVars : TypeVariable list) (ptc : PolyTypeContents) : PolyType =
        { forall = typeVars; typeExpr = ptc }

    let makeArrowType (from : PolyType) (to_ : PolyType) =
        { forall = from.forall @ to_.forall
          typeExpr = Conc.Arrow (from.typeExpr, to_.typeExpr) |> ConcreteType }


    let rec makeArrowTypeFromParamsAndResult
        (params_ : PolyTypeContents list)
        (result : PolyTypeContents)
        : PolyTypeContents =
        match params_ with
        | [] -> result
        | head :: restOfEarliers ->
            Conc.Arrow (head, makeArrowTypeFromParamsAndResult restOfEarliers result)
            |> ConcreteType






let rec private convertSingleTypeTermToPolyTypeResult
    (ctx : Ctx)
    (singleTerm : S.SingleTypeTerm)
    : Result<PolyType, UnificationError> =
    match singleTerm with
    | S.ConcTypeName (label, typeParams) ->
        let upperNameVal = NR.typeOrModuleIdentToUpperNameVal label

        match Map.tryFind upperNameVal ctx.typeNamesMap with
        | Some polyType ->
            match polyType.forall, typeParams with
            | [], [] -> Ok polyType
            | _, _ ->
                let typeParamZipResult = List.zipList polyType.forall typeParams

                match typeParamZipResult with
                | Ok zipped ->
                    let typeVarsAndPolyTypesResult : Result<(TypeVariable * PolyType) list, UnificationError nel> =
                        zipped
                        |> List.map (Tuple.mapSnd (convertTypeExprToPolyTypeResult ctx))
                        |> Result.traverse (fun (typeVar, polyTypeResult) ->
                            match polyTypeResult with
                            | Ok polyType -> Ok (typeVar, polyType)
                            | Error e -> Error e)


                    match typeVarsAndPolyTypesResult with
                    | Ok typeVarsAndPolyTypes ->
                        let replacedResult =
                            typeVarsAndPolyTypes
                            |> List.fold
                                (fun state (typeVar, polyTypeToInsert) ->
                                    replaceTypeVarWithPolyType typeVar polyTypeToInsert state)
                                polyType

                        Ok replacedResult

                    | Error e -> Error (NEL.head e)

                | Error e ->
                    WrongNumberOfTypeParams (
                        upperNameVal,
                        List.length polyType.forall |> uint,
                        List.length typeParams |> uint
                    )
                    |> Error

        | None -> UndefinedTypeCtor upperNameVal |> Error

    | S.Skolem name ->
        let lowerNameVal = NR.unqualValToLowerIdent name

        if Set.contains lowerNameVal ctx.skolemsInScope then
            PTC.Skolem lowerNameVal |> Types.makePoly |> Ok

        else
            // Generalise this skolem to a type variable if it's not already bound
            let newTypeVar = makeNewTypeVar () |> TypeVariable.createType

            Ok
                { forall = [ newTypeVar ]
                  typeExpr = TypeVariable newTypeVar }


/// @TODO implement
/// Converts a type expression to a PolyType
and convertTypeExprToPolyTypeResult (ctx : Ctx) (typeExpr : S.TypeExpr) : Result<PolyType, UnificationError> =
    failwith "@TODO implement"


/// @TODO implement
/// Also I'm pretty sure this API isn't quite right. It'll need to be refined.
and private replaceTypeVarWithPolyType
    (typeVar : TypeVariable)
    (polyTypeToReplace : PolyType)
    (polyTypeToReplaceItIn : PolyType)
    : PolyType =
    failwith "@TODO implement"











/// Gets all the value names referenced in an expression, for the purpose of creating a name dependency graph.
/// Note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because as far as the higher scopes are concerned those names do not exist.
let rec private getNamesUsedInExpr (namesToLookOutFor : ValIdent set) (expr : S.Expression) : ValIdent set =
    match expr with
    | S.LowerIdentifier ident ->
        match ident with
        | Lexer.QualifiedValue _ -> Set.empty
        | Lexer.UnqualValue unqual ->
            // The heart of this function
            if Set.contains unqual namesToLookOutFor then
                Set.singleton unqual
            else
                Set.empty

    | S.UpperIdentifier _ -> Set.empty
    | S.Primitive _ -> Set.empty
    | S.Function func ->
        let shadowedNames : ValIdent set =
            func.params_
            |> NEL.map S.getNode
            |> Seq.collect getNamesInAssignmentPattern
            |> Set.ofSeq

        getNamesUsedInExpr (Set.difference namesToLookOutFor shadowedNames) func.body.node

    | S.DotGetter _ -> Set.empty
    | S.List exprs -> Set.collect (S.getNode >> getNamesUsedInExpr namesToLookOutFor) exprs
    | S.Expression.Tuple exprs -> Set.collect (S.getNode >> getNamesUsedInExpr namesToLookOutFor) exprs
    | S.Expression.Record fields -> Set.collect (snd >> S.getNode >> getNamesUsedInExpr namesToLookOutFor) fields
    | S.RecordExtension (recordToExtend, additions) ->
        additions
        |> Seq.collect (fun (_, value) -> getNamesUsedInExpr namesToLookOutFor value.node)
        |> Set.ofSeq
        |> Set.union (
            if Set.contains recordToExtend.node namesToLookOutFor then
                Set.singleton recordToExtend.node
            else
                Set.empty
        )


    | S.LetExpression (bindings, inExpr) ->
        let shadowedNames =
            bindings
            |> NEL.map S.getNode
            |> Seq.collect (fun binding -> getNamesInAssignmentPattern binding.bindPattern.node)
            |> Set.ofSeq

        let innerNamesToLookFor = Set.difference namesToLookOutFor shadowedNames

        bindings
        |> NEL.map S.getNode
        |> Seq.collect (fun binding -> getNamesUsedInExpr innerNamesToLookFor binding.value.node)
        |> Set.ofSeq
        |> Set.union (getNamesUsedInExpr innerNamesToLookFor inExpr.node)


    | S.IfExpression (cond, ifTrue, ifFalse) ->
        Set.unionMany
            [ getNamesUsedInExpr namesToLookOutFor cond.node
              getNamesUsedInExpr namesToLookOutFor ifTrue.node
              getNamesUsedInExpr namesToLookOutFor ifFalse.node ]

    | S.CaseMatch (exprToMatch, branches) ->
        let exprNames = getNamesUsedInExpr namesToLookOutFor exprToMatch.node

        let namesFromBranches =
            branches
            |> NEL.map (fun (pattern, branch) ->
                let shadowedNames = getNamesInAssignmentPattern pattern.node
                getNamesUsedInExpr (Set.difference namesToLookOutFor shadowedNames) branch.node)
            |> Set.unionMany

        Set.union exprNames namesFromBranches

    | S.Operator (left, opSequence) ->
        let leftNames = getNamesUsedInExpr namesToLookOutFor left.node

        let rightNames =
            opSequence
            |> NEL.map (fun (op, right) ->
                let opName =
                    match op.node with
                    | L.BuiltInOp _ -> Set.empty
                    | L.OtherOp name -> Set.singleton name

                getNamesUsedInExpr namesToLookOutFor right.node |> Set.union opName)
            |> Seq.collect id
            |> Set.ofSeq

        Set.union leftNames rightNames

    | S.FunctionApplication (funcExpr, params') ->
        let funcNames = getNamesUsedInExpr namesToLookOutFor funcExpr.node

        let paramNames =
            params'
            |> Seq.collect (S.getNode >> getNamesUsedInExpr namesToLookOutFor)
            |> Set.ofSeq

        Set.union funcNames paramNames

    | S.DotAccess (expr, _) -> getNamesUsedInExpr namesToLookOutFor expr.node
    | S.ParensedExpression expr -> getNamesUsedInExpr namesToLookOutFor expr





and private getNamesInAssignmentPattern (assignmentPattern : S.AssignmentPattern) : ValIdent set =
    match assignmentPattern with
    | S.Named name -> Set.singleton name
    | S.Ignored -> Set.empty
    | S.Unit -> Set.empty
    | S.DestructuredPattern destructured -> getNamesInDestructuredPattern destructured
    | S.Aliased (pattern, alias) -> getNamesInAssignmentPattern pattern.node |> Set.add alias.node



and private getNamesInDestructuredPattern (destructuredPattern : S.DestructuredPattern) : ValIdent set =
    match destructuredPattern with
    | S.DestructuredRecord fieldNames -> Seq.map S.getNode fieldNames |> Set.ofSeq
    | S.DestructuredTuple patterns -> Seq.collect (S.getNode >> getNamesInAssignmentPattern) patterns |> Set.ofSeq
    | S.DestructuredCons patterns -> Seq.collect (S.getNode >> getNamesInAssignmentPattern) patterns |> Set.ofSeq
    | S.DestructuredTypeVariant (_, params') ->
        Seq.collect (S.getNode >> getNamesInAssignmentPattern) params' |> Set.ofSeq













let private sortBindingsTopologically
    (namesAndExprs : (S.AssignmentPattern * S.Expression) seq)
    : DG.StronglyConnectedGraph<S.Expression, S.AssignmentPattern> list =

    let nameToBindingPatternMap : Map<ValIdent, S.AssignmentPattern> =
        namesAndExprs
        |> Seq.collect (fun (pattern, _) -> getNamesInAssignmentPattern pattern |> Seq.map (fun name -> name, pattern))
        |> Map.ofSeq

    let allNames = Map.keys nameToBindingPatternMap |> Set.ofSeq

    let getWhichPatternANameIsIn (name : ValIdent) : S.AssignmentPattern =
        match Map.tryFind name nameToBindingPatternMap with
        | Some pattern -> pattern
        | None -> failwith "It shouldn't be possible for us to look for a name that isn't in any assignment pattern"


    let getDependencies ((_, expr) : (_ * S.Expression)) : S.AssignmentPattern seq =
        expr
        |> getNamesUsedInExpr allNames
        |> Set.toSeq
        |> Seq.map getWhichPatternANameIsIn

    DG.getStronglyConnectedComponents<S.AssignmentPattern * S.Expression, S.AssignmentPattern>
        fst
        getDependencies
        namesAndExprs
    |> DG.sortOneOrMoreTopologically fst getDependencies
    |> List.map (DG.SCC.map snd)




/// Add a local names map to a global one
let private addLocalNamesMap (localNamesMap : T.TypedLocalNamesMap) (namesMap : T.TypedNamesMap) : T.TypedNamesMap =
    let newMap = localNamesMap |> Map.mapKeyVal (fun key v -> LocalLower key, v)
    // @TODO: this should really throw an error if there are any name clashes so we don't get silently overwritten names
    Map.merge newMap namesMap













(* Zonking *)




/// Maps a function that operates on PTCs and makes it work for TORs also
let private mapToTypeOrRec (f : PolyTypeContents -> PolyTypeContents) (tor : TypeOrRecordConstr) : TypeOrRecordConstr =
    match tor with
    | TypeConstr ptc -> TypeConstr (f ptc)
    | TOR.RecordConstr fields -> TOR.RecordConstr (List.map (fun (field, value) -> field, f value) fields)


/// Takes a function that operates on PTCs and makes it work for TORs also, and gathers the results together
let private fromTypeOrRec (f : PolyTypeContents -> 'T) (gatherer : 'T list -> 'T) (tor : TypeOrRecordConstr) =
    match tor with
    | TypeConstr ptc -> f ptc
    | TOR.RecordConstr fields -> List.map (snd >> f) fields |> gatherer



//let private getKindFromUniVar (uniVar : UnificationVariable) =
//    uniVar.content.Value.constrained

/// This should get all the univars that need to be replaced by type variables. Constrained univars will be replaced with their contents, so we don't need to gather them here.
let private getAllUnconstrainedUniVars (ptc : PolyTypeContents) : (UnificationVarId * TypeVariableKind) set =

    let getUniVarsFromTuples (tuples : (UnificationVarId * TypeVariableKind) set) : UnificationVarId set =
        Set.map fst tuples



    let rec getter (univarsGathered : UnificationVarId set) ptc =

        let folder getPtcFromItem results row =
            getPtcFromItem row
            |> getter (getUniVarsFromTuples results |> Set.union univarsGathered)
            |> Set.union results

        match ptc with
        | UnificationVar uniVar ->
            let uniVarId = uniVar.content.Value.id

            if Set.contains uniVarId univarsGathered then
                Set.empty
            else
                match uniVar.content.Value.constrained with
                | None -> Set.singleton (uniVarId, Type_)
                | Some constrained ->
                    match constrained with
                    | TypeConstr ptc_ -> getter univarsGathered ptc_
                    | RecordConstr fields ->
                        let kind = TypeVariableKind.Record fields

                        fields |> List.fold (folder snd) Set.empty |> Set.add (uniVarId, kind)


        //fromTypeOrRec getAllUnconstrainedUniVars Set.unionMany constrained

        //| RecordUnificationVar uniVar ->
        //    // If it's a record unification var it's always unconstrained, in the sense that it's not a closed record so it always has the possibility of extra fields
        //    Set.singleton uniVar.content.Value.id

        | TypeVariable typeVar ->
            match typeVar.kind with
            | Type_ -> Set.empty
            | TypeVariableKind.Record fields -> fields |> List.fold (folder snd) Set.empty


        | PTC.Skolem _ -> Set.empty
        | ConcreteType concrete ->
            match concrete with
            | BuiltInPrims _ -> Set.empty
            | Conc.Tuple params_ -> params_ |> TOM.fold (folder id) Set.empty
            | Conc.List param -> getter univarsGathered param
            | Conc.Arrow (fromType, toType) ->
                Set.union (getter univarsGathered fromType) (getter univarsGathered toType)

            | Conc.RecordExact fields -> fields |> List.fold (folder snd) Set.empty
            //| Conc.RecordOpenMaybe fields -> List.map (snd >> getAllUnconstrainedUniVars) fields |> Set.unionMany
            //| Conc.RecordOpenDefinitely (_, fields) -> List.map (snd >> getAllUnconstrainedUniVars) fields |> Set.unionMany

            | CustomType (_, typeParams) -> typeParams |> List.fold (folder id) Set.empty

    getter Set.empty ptc



//(* Attempt to implement a dependent `Vec n a` in F# *)

//type Zero = Z
//type 'Nat succ = | S of 'Nat


//type vec<'a, 'size> =
//    | Nil // of vec<'a, Zero>
//    | Cons of ('a * vec<'a, 'size>) -> vec<'a, 'size succ>



//let rec zip<'a, 'b, 'size> (a : vec<'a, 'size>) (b : vec<'b, 'size>) : vec<'a * 'b, 'size> =
//    match (a, b) with
//    | Nil, Nil -> Nil
//    | Cons (x, xs), Cons (y, ys) -> Cons ((x, y), zip xs ys)






/// This will replace all univars from a higher (more deeply nested) or equal level than the current one. If constrained, it will replace the univar with a concrete type. If unconstrained, it will replace them with new type vars.
/// Note: at this point we are doing no unification, so there should be no clashes, and we can probably take a few little liberties and assumptions that there won't be any clashes between type vars, since all type vars will be deterministically replaced with the same thing for the same univar.
let private zonkPolyTypeContents (ctx : Ctx) (ptc : PolyTypeContents) : PolyType =
    let unconstrainedUniVars = getAllUnconstrainedUniVars ptc
    //let uniVarIdToTvKindMap = Map.ofSeq unconstrainedUniVars

    ///// @TODO what this needs to do, and i'm struggling to figure out, is to traverse all the row kind typevars' fields, and their children recursively, and get typevars for all the univars contained therein. And surface it all into a flat list (eventually to be made into a map) which will then contain all univars and all newly created typevars, so that doing Map.values on that map will return every single typevar referenced therein. Unlike what we have now, which is there being a whole bunch of undeclared typevars referenced inside the row types' fields contents.
    //let rec getUnconstrainedUniVarsToTypeVarsMapping
    //    //(uniVarAndTypeVarKinds : (UnificationVarId * TypeVariableKind) set)
    //    (typeVarKind : TypeVariableKind)
    //    =
    //    uniVarAndTypeVarKinds
    //    |> Set.toSeq
    //    |> Seq.collect (fun (uniVarId, typeVarKind) ->
    //        let typeVarId = makeNewTypeVar ()

    //        let typeVar =
    //            match typeVarKind with
    //            | Type_ -> TypeVariable.createType typeVarId
    //            | TypeVariableKind.Record fields -> TypeVariable.createRecord typeVarId fields

    //        uniVarId, typeVar)


    //let simpleMap : Map<UnificationVarId, TypeVariableKind> =
    //    unconstrainedUniVars |> Map.ofSeq


    //let rec getSingleUniVarToTypeVarMap (uniVarsAndKind : UnificationVarId * TypeVariableKind) =
    //    let uniVarId, typeVarKind = uniVarsAndKind

    //    let typeVar =
    //        match typeVarKind with
    //        | Type_ -> Type_
    //        | TypeVariableKind.Record fields ->
    //            //TypeVariable.createRecord typeVarId fields
    //            fields
    //            |> List.map (snd >> getSingleUniVarToTypeVarMap)

    //    uniVarId, typeVar





    let unconstrainedUniVarsToTypeVarsMap : Map<UnificationVarId, TypeVariable> =
        unconstrainedUniVars
        |> Set.toSeq
        |> Seq.map (fun (uniVarId, typeVarKind) ->
            let typeVarId = makeNewTypeVar ()

            let typeVar =
                match typeVarKind with
                | Type_ -> TypeVariable.createType typeVarId
                | TypeVariableKind.Record fields -> TypeVariable.createRecord typeVarId fields

            uniVarId, typeVar)
        |> Seq.fold
            (fun map (key, v) ->
                match Map.tryFind key map with
                | Some _ -> failwith "We should not have any duplicate univars"
                | None -> Map.add key v map)
            Map.empty

    let rec replaceAndGetTypeVars (ptc : PolyTypeContents) : PolyTypeContents =
        match ptc with
        | UnificationVar uniVar ->
            if uniVar.content.Value.levelDeclared >= ctx.currentLevel then
                match uniVar.content.Value.constrained with
                | None ->
                    match Map.tryFind uniVar.content.Value.id unconstrainedUniVarsToTypeVarsMap with
                    | Some typeVar ->
                        // If unconstrained, this will be a free type variable
                        //TypeVariable typeVar
                        match typeVar.kind with
                        | Type_ -> TypeVariable { id = typeVar.id; kind = Type_ }

                        | TypeVariableKind.Record fields ->
                            let replacedFields = List.map (Tuple.mapSnd replaceAndGetTypeVars) fields

                            TypeVariable
                                { typeVar with
                                    kind = TypeVariableKind.Record replacedFields }

                    | None -> failwith "We should have reserved type variables for all unconstrained unification vars"



                | Some constrained ->
                    // If constrained, replace with the constrained concrete type

                    match constrained with
                    | TypeConstr ptc -> replaceAndGetTypeVars ptc
                    | RecordConstr _ ->
                        match Map.tryFind uniVar.content.Value.id unconstrainedUniVarsToTypeVarsMap with
                        | Some typeVar ->
                            match typeVar.kind with
                            | Type_ -> TypeVariable typeVar

                            | TypeVariableKind.Record fields ->
                                let replacedFields = List.map (Tuple.mapSnd replaceAndGetTypeVars) fields

                                TypeVariable
                                    { typeVar with
                                        kind = TypeVariableKind.Record replacedFields }

                        | None ->
                            failwith "We should have reserved type variables for all unconstrained unification vars"

            //(* @TODO still need to decide how to zonk a Record univar to a type variable *)
            //mapToTypeOrRec replaceAndGetTypeVars constrained

            else
                // This uni var is declared at a higher scope and thus has a lower level and thus shouldn't be removed
                UnificationVar uniVar

        | TypeVariable tv ->
            match tv.kind with
            | Type_ -> PTC.TypeVariable tv
            | TypeVariableKind.Record fields ->
                let swappedFields = List.map (Tuple.mapSnd replaceAndGetTypeVars) fields

                TypeVariable
                    { tv with
                        kind = TypeVariableKind.Record swappedFields }


        | PTC.Skolem name -> PTC.Skolem name
        | ConcreteType concrete ->
            match concrete with
            | BuiltInPrims builtInPrims -> BuiltInPrims builtInPrims |> ConcreteType
            | Conc.Tuple params_ ->
                let replacedParams = TOM.map replaceAndGetTypeVars params_
                Conc.Tuple replacedParams |> PTC.ConcreteType

            | Conc.List param ->
                let replaced = replaceAndGetTypeVars param
                Conc.List replaced |> ConcreteType

            | Conc.Arrow (fromType, toType) ->
                let replacedFrom = replaceAndGetTypeVars fromType
                let replacedTo = replaceAndGetTypeVars toType

                Conc.Arrow (replacedFrom, replacedTo) |> ConcreteType

            | Conc.RecordExact fields ->
                fields
                |> List.map (fun (field, value) -> field, replaceAndGetTypeVars value)
                |> Conc.RecordExact
                |> ConcreteType

            | CustomType (name, typeParams) ->
                let replacedParams = List.map replaceAndGetTypeVars typeParams

                CustomType (name, replacedParams) |> PTC.ConcreteType



    let replacedTypeVars =
        Map.values unconstrainedUniVarsToTypeVarsMap
        |> Seq.map (fun tv ->
            match tv.kind with
            | Type_ -> tv
            | TypeVariableKind.Record fields ->
                { tv with
                    kind = TypeVariableKind.Record (List.map (Tuple.mapSnd replaceAndGetTypeVars) fields) })



    { forall =
        replacedTypeVars
        |> Seq.sortBy (
            _.kind
            >> function
                | Type_ -> 0
                | TypeVariableKind.Record _ -> 1
        )
        |> List.ofSeq
      typeExpr = replaceAndGetTypeVars ptc }






let zonkPolyTypeContentsResult
    (ctx : Ctx)
    (ptcResult : Result<PolyTypeContents, UnificationError>)
    : Result<PolyType, UnificationError> =
    // @TODO we should probably zonk the UnificationError contents also!
    Result.map (zonkPolyTypeContents ctx) ptcResult


//let private zonkPolyType (ctx : Ctx) (type_ : PolyType) : PolyType =
//    // This is fine to replace the whole original polytype because the zonking will include all typevars present in the PTC anyway, so no need to keep hold of the original `forall`s.
//    // @TODO hmm um actually i'm not sure that's actually true? and i don't know why I thought that was true?
//    zonkPolyTypeContents ctx type_.typeExpr


///// @TODO we should probably apply this to the error branch as well
//let private zonkPolyTypeResult
//    (ctx : Ctx)
//    (type_ : Result<PolyType, UnificationError>)
//    : Result<PolyType, UnificationError> =
//    Result.map (zonkPolyType ctx) type_










(* Type inference *)





type OccursCheckResult =
    /// I.e. all good because no circular references to a univar
    | NoOccurs
    /// I.e. it's ok because this is directly equivalent to another univar, which means they can both be unified (along with any intermediate univars) to the same type effectively
    | OccursButIsDirect
    /// This one is the problem because it means that a univar contains a reference to itself in a way which is not simply a direct equality. Which means it's something like ?a = (?x, ?a); that will result in an infinite regress when trying to zonk ?a which will not be able to be resolved. So this one should throw a type error.
    | OccursAndIsIndirect



let rec private inferTypeFromExpr (ctx : Ctx) (expr : S.Expression) : Result<PolyTypeContents, UnificationError> =
    match expr with
    | S.Primitive prim ->
        (match prim with
         | S.FloatLiteral _ -> Float
         | S.IntLiteral _ -> Int
         | S.CharPrimitive _ -> Char
         | S.StringPrimitive _ -> String
         | S.BoolPrimitive _ -> Bool
         | S.UnitPrimitive -> Unit)
        |> BuiltInPrims
        |> ConcreteType
        |> Ok

    | S.Function func ->
        let allParamTypesResults, paramPatternNamesMap =
            func.params_
            |> NEL.foldMap
                (fun oldNamesMap param ->
                    let paramTypeResult, namesMap = inferTypeFromAssignmentPattern ctx param.node

                    paramTypeResult, combineAssignmentNamesMaps ctx namesMap oldNamesMap)
                Map.empty


        let allParamTypesResult = NEL.sequenceResult allParamTypesResults

        match allParamTypesResult with
        | Ok allParamTypes ->
            let ctxForBody =
                { ctx with
                    typedNamesMap =
                        addLocalNamesMap
                            (convertAssignmentNamesMapToTypedLocalNamesMap paramPatternNamesMap)
                            ctx.typedNamesMap }

            let bodyTypeResult = inferTypeFromExpr ctxForBody func.body.node

            match bodyTypeResult with
            | Ok bodyType ->

                let arrowType =
                    Types.makeArrowTypeFromParamsAndResult (NEL.toList allParamTypes) bodyType

                Ok arrowType

            | Error e -> Error e

        | Error e -> Error (NEL.head e)

    | S.DotGetter fieldName ->
        let fieldNameValUniVar =
            makeNewUniVar () |> UnificationVariable.makeNewBlank ctx.currentLevel

        let recordUniVar =
            UnificationVariable.makeNewRecConstraint
                ctx.currentLevel
                (makeNewUniVar ())
                [ NR.unqualValToLowerIdent fieldName, PTC.UnificationVar fieldNameValUniVar ]

        Ok (PTC.UnificationVar recordUniVar)




    | S.UpperIdentifier ident ->
        match Map.tryFind ident ctx.ctorNamesMap with
        | Some value ->
            let instantiated = instantiateCtor ctx value

            Types.makeArrowTypeFromParamsAndResult instantiated.params_ instantiated.result
            |> Ok

        | None ->
            NR.typeOrModuleIdentToUpperNameVal ident
            |> UnificationError.UndefinedTypeCtor
            |> Error

    | S.LowerIdentifier ident ->
        let lowerName = NR.convertValueIdentifierToLowerName ident

        match Map.tryFind lowerName ctx.typedNamesMap with
        | Some polyType -> Result.map (instantiatePolyType ctx) polyType
        | None -> UnificationError.UndefinedName lowerName |> Error

    | S.List items ->
        match items with
        | [] ->
            let uniVar = makeNewUniVar ()

            UnificationVariable.makeNewBlank ctx.currentLevel uniVar
            |> PTC.UnificationVar
            |> Conc.List
            |> ConcreteType
            |> Ok

        | head :: rest ->
            let nel = NEL.new_ head rest

            NEL.map (S.getNode >> inferTypeFromExpr ctx) nel
            |> unifyMultipleTypeContentResults ctx
            |> Result.map (Conc.List >> ConcreteType)

    | S.Expression.Tuple items ->
        TOM.map (S.getNode >> inferTypeFromExpr ctx) items
        |> TOM.sequenceResult
        |> Result.map (Conc.Tuple >> ConcreteType)
        |> Result.mapError NEL.head

    | S.Expression.Record fields ->
        let inferred =
            fields
            |> List.map (fun (fieldName, fieldExpr) ->
                let inferredType = inferTypeFromExpr ctx fieldExpr.node

                match inferredType with
                | Ok inferred -> Ok (NR.unqualValIdentToLowerIdent fieldName.node, inferred)
                | Error e -> Error e)
            |> Result.sequenceList


        match inferred with
        | Ok fieldTypes -> RecordExact fieldTypes |> ConcreteType |> Ok
        | Error e -> Error (NEL.head e)


    | S.Expression.RecordExtension (extendedRecord, extendedFields) ->
        let extendedRecordTypeResult =
            extendedRecord.node
            |> L.UnqualValue
            |> S.LowerIdentifier
            |> inferTypeFromExpr ctx

        let fieldTypeResults =
            extendedFields
            |> NEL.map (fun (fieldName, fieldExpr) ->
                let inferredType = inferTypeFromExpr ctx fieldExpr.node

                match inferredType with
                | Ok inferred -> Ok (NR.unqualValIdentToLowerIdent fieldName.node, inferred)
                | Error e -> Error e)
            |> NEL.sequenceResult


        match fieldTypeResults with
        | Ok fieldTypes ->
            let recordUniVar =
                UnificationVariable.makeNewRecConstraint ctx.currentLevel (makeNewUniVar ()) (NEL.toList fieldTypes)
                |> PTC.UnificationVar

            //let record = fieldTypes |> NEL.toList |> Conc.RecordOpenMaybe |> ConcreteType
            unifyTwoTypeContentsResults ctx extendedRecordTypeResult (Ok recordUniVar)

        | Error e -> Error (NEL.head e)

    | S.LetExpression (bindings, inExpr) -> resolveAllLetBindingsAndBody ctx bindings inExpr



    | S.IfExpression (cond, ifTrue, ifFalse) ->
        /// Not used, but constraint has to be applied
        let condTypeResult =
            inferTypeFromExpr ctx cond.node
            |> unifyTwoTypeContentsResults ctx (BuiltInPrims Bool |> ConcreteType |> Ok)

        let ifTrueTypeResult = inferTypeFromExpr ctx ifTrue.node
        let ifFalseTypeResult = inferTypeFromExpr ctx ifFalse.node

        let returnType = unifyTwoTypeContentsResults ctx ifTrueTypeResult ifFalseTypeResult

        match condTypeResult with
        | Ok _ -> returnType
        | Error e -> Error e


    | S.CaseMatch (exprToMatch, branches) ->
        let exprToMatchTypeResult = inferTypeFromExpr ctx exprToMatch.node

        let branchInformation =
            branches
            |> NEL.map (fun (pattern, branchExpr) ->
                let patternTypeResult, paramPatternNamesMap =
                    inferTypeFromAssignmentPattern ctx pattern.node

                let ctxWithNames =
                    { ctx with
                        typedNamesMap =
                            addLocalNamesMap
                                (convertAssignmentNamesMapToTypedLocalNamesMap paramPatternNamesMap)
                                ctx.typedNamesMap }

                {| patternType = patternTypeResult
                   exprType = inferTypeFromExpr ctxWithNames branchExpr.node |})


        let patternTypes = branchInformation |> NEL.map _.patternType

        let typeOfMatchedExpr =
            patternTypes
            |> NEL.cons exprToMatchTypeResult
            |> unifyMultipleTypeContentResults ctx

        let returnType =
            branchInformation |> NEL.map _.exprType |> unifyMultipleTypeContentResults ctx

        match typeOfMatchedExpr with
        | Ok _ -> returnType
        | Error e -> Error e



    | S.Operator (left, opSeq) -> failwith "@TODO need to implement this with proper operator binary tree construction"


    | S.FunctionApplication (funcExpr, params') ->
        let funcTypeResult = inferTypeFromExpr ctx funcExpr.node

        let paramTypesResult =
            params' |> NEL.map (S.getNode >> inferTypeFromExpr ctx) |> NEL.sequenceResult


        match funcTypeResult, paramTypesResult with
        | Ok funcType, Ok paramTypes ->

            let returnTypeUniVarId = makeNewUniVar ()

            let returnTypeUniVar =
                UnificationVariable.makeNewBlank ctx.currentLevel returnTypeUniVarId
                |> UnificationVar

            let arrowTypeConstraintPolyType =
                Types.makeArrowTypeFromParamsAndResult (NEL.toList paramTypes) returnTypeUniVar

            let unifiedAppliedFuncType =
                unifyTwoTypeContents ctx arrowTypeConstraintPolyType funcType

            match unifiedAppliedFuncType with
            | Ok _ -> Ok returnTypeUniVar
            | Error e -> Error e

        | Error e, _ -> Error e
        | _, Error e -> Error (NEL.head e)


    | S.DotAccess (dottedExpr, dotSeq) ->
        let exprTypeResult = inferTypeFromExpr ctx dottedExpr.node

        let rec makeDottableType fields type_ =
            match fields with
            | [] -> Ok type_
            | firstFieldName :: rest ->
                let fieldNameValUniVar =
                    makeNewUniVar ()
                    |> UnificationVariable.makeNewBlank ctx.currentLevel
                    |> PTC.UnificationVar

                let dottedType =
                    UnificationVariable.makeNewRecConstraint
                        ctx.currentLevel
                        (makeNewUniVar ())
                        [ NR.unqualValToLowerIdent firstFieldName, fieldNameValUniVar ]
                    |> PTC.UnificationVar

                let nested = makeDottableType rest fieldNameValUniVar
                let unified = unifyTwoTypeContents ctx type_ dottedType

                match unified with
                | Ok _ -> nested
                | Error e -> Error e




        match exprTypeResult with
        | Ok exprType ->
            let dotted = makeDottableType (Seq.toList dotSeq.node) exprType
            dotted

        | Error e -> Error e


    | S.ParensedExpression innerExpr -> inferTypeFromExpr ctx innerExpr







/// We return the uniVars so that we can zonk them later
and private inferTypeFromAssignmentPattern
    (ctx : Ctx)
    (pattern : S.AssignmentPattern)
    : Result<PolyTypeContents, UnificationError> * AssignmentNamesMap =
    // @TODO hm I think we may need to return this univar alongside the other gleanings, so that we know when these univars should be zonked. Otherwise we never zonk these univars. And they should be zonked when they're no longer in scope.
    let newUniVarId = makeNewUniVar ()

    match pattern with
    | S.Named name ->
        let type_ =
            UnificationVariable.makeNewBlank ctx.currentLevel newUniVarId |> UnificationVar

        Ok type_, Map.singleton (NR.unqualValToLowerIdent name) (Ok type_)

    | S.Ignored ->
        let type_ =
            UnificationVariable.makeNewBlank ctx.currentLevel newUniVarId |> UnificationVar

        Ok type_, Map.empty

    | S.Unit ->
        let uniVar =
            UnificationVariable.makeNewConstr ctx.currentLevel newUniVarId (BuiltInPrims Unit |> ConcreteType)
            |> UnificationVar

        Ok uniVar, Map.empty

    | S.Aliased (pattern, alias) ->
        let inferredType, localNamesMap = inferTypeFromAssignmentPattern ctx pattern.node

        match inferredType with
        | Ok inferred ->
            let aliasType =
                UnificationVariable.makeNewConstr ctx.currentLevel newUniVarId inferred
                |> UnificationVar

            let aliasAddedToMap =
                localNamesMap |> Map.add (NR.unqualValToLowerIdent alias.node) (Ok aliasType)

            Ok aliasType, aliasAddedToMap

        | Error e -> Error e, localNamesMap



    | S.DestructuredPattern destructurePattern ->
        match destructurePattern with
        | S.DestructuredTuple items ->
            let typedContents, assignmentNamesMap =
                items
                |> TOM.foldMap
                    (fun namesMap item ->
                        let inferred, newMap = inferTypeFromAssignmentPattern ctx item.node
                        inferred, combineAssignmentNamesMaps ctx newMap namesMap)
                    Map.empty

            match TOM.sequenceResult typedContents with
            | Ok contents ->

                let tuple =
                    UnificationVariable.makeNewConstr ctx.currentLevel newUniVarId (Conc.Tuple contents |> ConcreteType)
                    |> UnificationVar

                Ok tuple, assignmentNamesMap

            | Error e -> NEL.head e |> Error, assignmentNamesMap


        | S.DestructuredCons items ->
            // In a list of type `List a`, the last cons pattern has type `List a` and all preceding ones have type `a`
            let (TOM (last, penultimate, rest)) = TOM.reverse items

            let itemTypes, localNamesMap =
                NEL.new_ penultimate rest
                |> NEL.foldMap
                    (fun namesMap item ->
                        let inferred, newMap = inferTypeFromAssignmentPattern ctx item.node
                        inferred, combineAssignmentNamesMaps ctx newMap namesMap)
                    Map.empty

            let typeOfListItem = unifyMultipleTypeContentResults ctx itemTypes

            let lastType, lastLocalNamesMap = inferTypeFromAssignmentPattern ctx last.node

            let lastWithListConstraint =
                unifyTwoTypeContentsResults ctx lastType (Result.map (Conc.List >> ConcreteType) typeOfListItem)

            let combinedNamesMap =
                combineAssignmentNamesMaps ctx lastLocalNamesMap localNamesMap

            lastWithListConstraint, combinedNamesMap



        | S.DestructuredRecord fields ->
            let withUniVars =
                fields
                |> NEL.map (fun fieldName ->
                    NR.unqualValIdentToLowerIdent fieldName.node,
                    makeNewUniVar ()
                    |> UnificationVariable.makeNewBlank ctx.currentLevel
                    |> PTC.UnificationVar)

            let list = withUniVars |> List.ofSeq

            UnificationVariable.makeNewRecConstraint ctx.currentLevel (makeNewUniVar ()) list
            |> PTC.UnificationVar
            |> Ok,
            List.map (Tuple.mapSnd Ok) list |> Map.ofList


        | S.DestructuredTypeVariant (ctor, typeParams) ->
            match Map.tryFind ctor.node ctx.ctorNamesMap with
            | Some foundCtor ->
                let inferredParamPatternsResult
                    : Result<(PolyTypeContents * AssignmentNamesMap) list, UnificationError nel> =
                    typeParams
                    // @TODO we can probably maneuver the names maps out of this so that even if there are some error we still gather all the names that we can
                    |> List.map (S.getNode >> inferTypeFromAssignmentPattern ctx)
                    |> Result.traverse (fun (polyTypeResult, namesMap) ->
                        match polyTypeResult with
                        | Ok polyType -> Ok (polyType, namesMap)
                        | Error e -> Error e)


                match inferredParamPatternsResult with
                | Ok list ->
                    let actualPtcs, namesMap =
                        list
                        |> List.mapFold
                            (fun namesMap (polyTypeContents, newNamesMap) ->
                                polyTypeContents, combineAssignmentNamesMaps ctx newNamesMap namesMap)
                            Map.empty

                    match foundCtor.params_, actualPtcs with
                    | [], [] ->
                        let foundCtorPolyType =
                            { forall = foundCtor.forall
                              typeExpr = foundCtor.result }

                        let instantiatedCtorPtc = instantiatePolyType ctx foundCtorPolyType
                        Ok instantiatedCtorPtc, namesMap

                    | _, _ ->

                        let instantiatedCtor = instantiateCtor ctx foundCtor

                        match List.zipList instantiatedCtor.params_ actualPtcs with
                        | Ok zipped ->
                            let unified =
                                Result.traverse (fun (found, actual) -> unifyTwoTypeContents ctx found actual) zipped

                            match unified with
                            | Ok unifiedCtorParams -> Ok instantiatedCtor.result, namesMap
                            | Error e -> Error (NEL.head e), namesMap

                        | Error _ ->
                            WrongNumberOfTypeParams (
                                NR.typeOrModuleIdentToUpperNameVal ctor.node,
                                List.length foundCtor.params_ |> uint,
                                List.length actualPtcs |> uint
                            )
                            |> Error,
                            namesMap

                | Error e ->
                    Error (NEL.head e),
                    // @TODO we can probably maneuver the names maps out of this so that even if there are some error we still gather all the names that we can
                    Map.empty

            | None ->
                NR.typeOrModuleIdentToUpperNameVal ctor.node
                |> UnificationError.UndefinedTypeCtor
                |> Error,
                Map.empty






and private resolveAllLetBindingsAndBody
    (ctx : Ctx)
    (letBindings : S.CstNode<S.LetBinding> nel)
    (body : S.CstNode<S.Expression>)
    : Result<PolyTypeContents, UnificationError> =
    let levelledUpCtx =
        { ctx with
            currentLevel = ctx.currentLevel + 1u }

    let bindingsResolutionResult =
        letBindings |> NEL.map S.getNode |> resolveNamesTopologically levelledUpCtx

    let combinedNamesMap : Ctx =
        { levelledUpCtx with
            typedNamesMap = addLocalNamesMap bindingsResolutionResult levelledUpCtx.typedNamesMap }

    let bodyResult = inferTypeFromExpr combinedNamesMap body.node
    bodyResult



and private resolveNamesTopologically (ctx : Ctx) (namesAndExprs : S.LetBinding nel) : TypedLocalNamesMap =

    let annotatedNamesMap : TypedLocalNamesMap =
        namesAndExprs
        |> Seq.choose (fun binding ->
            match binding.typeAnnotation with
            | None -> None
            | Some annotation ->
                (*
                    @TODO I think there's some superfluous stuff here, plus it's odd that both checkResult and unifiedAssignmentPatternTypeAndChecked are not used. Not sure if that's right, will need to check again that that logic is right
                *)

                /// The TypeExpr converted to a type
                let typeExprResult = convertTypeExprToPolyTypeResult ctx annotation.node

                let checkResult = check ctx annotation.node binding.value.node

                /// @TODO: carry on here, combine these namesMaps into the main one, and ofc afterwards don't forget to zonk!
                let assignmentPatternResult, namesMap =
                    inferTypeFromAssignmentPattern ctx binding.bindPattern.node


                let unifiedAssignmentPatternTypeAndChecked =
                    assignmentPatternResult
                    |> Result.map Types.makePoly
                    |> unifyTwoTypeResults ctx typeExprResult

                let zonkedNamesMap = zonkAssignmentNamesMap ctx namesMap

                Some zonkedNamesMap)
        |> Seq.fold (combineNamesMaps ctx) Map.empty


    let unAnnotatedBindings : (S.AssignmentPattern * S.Expression) seq =
        namesAndExprs
        |> Seq.choose (fun binding ->
            match binding.typeAnnotation with
            | None -> Some (binding.bindPattern.node, binding.value.node)
            | Some _ -> None)

    let stronglyConnectedAndOrderedUnannotatedBindings
        : DG.StronglyConnectedGraph<S.Expression, S.AssignmentPattern> list =
        sortBindingsTopologically unAnnotatedBindings


    /// If the unified value has an error then all the names arising from the assignment should be replaced with the type error
    let replaceAssignmentMapEntriesIfErr
        (ptcResult : Result<PolyTypeContents, UnificationError>)
        (assignmentMap : AssignmentNamesMap)
        : AssignmentNamesMap =
        match ptcResult with
        | Ok _ -> assignmentMap
        | Error e -> Map.map (fun _ _ -> Error e) assignmentMap


    let localNamesMap =
        stronglyConnectedAndOrderedUnannotatedBindings
        |> List.fold
            (fun localNamesMap stronglyConnectedComponent ->

                /// First we add all the names into the context that this value might reference
                let combinedNamesMapCtx : Ctx =
                    { ctx with
                        typedNamesMap = addLocalNamesMap localNamesMap ctx.typedNamesMap }

                match stronglyConnectedComponent with
                | DG.SingleNonRec (assignmentPattern, expr) ->
                    let inferredTypeFromAssignment, assignmentNamesMap =
                        inferTypeFromAssignmentPattern ctx assignmentPattern

                    let inferredType = inferTypeFromExpr combinedNamesMapCtx expr

                    /// Unified from the inferred type and the inferred shape from the assignment pattern
                    let unified =
                        unifyTwoTypeContentsResults ctx inferredTypeFromAssignment inferredType

                    let withThisBindingAdded : TypedLocalNamesMap =
                        replaceAssignmentMapEntriesIfErr unified assignmentNamesMap
                        |> zonkAssignmentNamesMap ctx
                        |> combineNamesMaps ctx localNamesMap

                    withThisBindingAdded


                | DG.SingleSelfRec (assignmentPattern, expr) ->
                    let inferredTypeFromAssignment, assignmentNamesMap =
                        inferTypeFromAssignmentPattern ctx assignmentPattern

                    let withOwnNamesAddedCtx : Ctx =
                        { ctx with
                            typedNamesMap =
                                combinedNamesMapCtx.typedNamesMap
                                |> addLocalNamesMap (convertAssignmentNamesMapToTypedLocalNamesMap assignmentNamesMap) }

                    let inferredType = inferTypeFromExpr withOwnNamesAddedCtx expr

                    /// Unified from the inferred type and the inferred shape from the assignment pattern
                    let unified =
                        unifyTwoTypeContentsResults ctx inferredTypeFromAssignment inferredType

                    let withThisBindingAdded : TypedLocalNamesMap =
                        replaceAssignmentMapEntriesIfErr unified assignmentNamesMap
                        |> zonkAssignmentNamesMap ctx
                        |> combineNamesMaps ctx localNamesMap

                    withThisBindingAdded


                | DG.MutualRecursive namesAndBindings ->
                    let namesAndBindingsAndUniVars
                        : ((Result<PolyTypeContents, UnificationError> * AssignmentNamesMap) * S.Expression) seq =
                        namesAndBindings
                        |> Seq.map (fun (assignmentPattern, expr) ->
                            inferTypeFromAssignmentPattern ctx assignmentPattern, expr)

                    let withNewUniVarsAdded : Ctx =
                        { ctx with
                            typedNamesMap =
                                namesAndBindingsAndUniVars
                                |> Seq.fold
                                    (fun map ((_, assignmentNamesMap), _) ->
                                        map
                                        |> addLocalNamesMap (
                                            convertAssignmentNamesMapToTypedLocalNamesMap assignmentNamesMap
                                        ))
                                    combinedNamesMapCtx.typedNamesMap }


                    /// Get the assignment names map and univars from all the bindings and combine them
                    let newLocalNamesMap : TypedLocalNamesMap =
                        namesAndBindingsAndUniVars
                        |> Seq.fold
                            (fun namesMap ((inferredTypeFromAssignment, assignmentNamesMap), expr) ->
                                let inferredType = inferTypeFromExpr withNewUniVarsAdded expr

                                /// Unified from the inferred type and the inferred shape from the assignment pattern
                                let unified =
                                    unifyTwoTypeContentsResults ctx inferredType inferredTypeFromAssignment

                                let withThisBindingAdded : TypedLocalNamesMap =
                                    replaceAssignmentMapEntriesIfErr unified assignmentNamesMap
                                    |> zonkAssignmentNamesMap ctx
                                    |> combineNamesMaps ctx namesMap

                                withThisBindingAdded)
                            Map.empty

                    let withThisBindingAdded : TypedLocalNamesMap =
                        combineNamesMaps ctx newLocalNamesMap localNamesMap

                    withThisBindingAdded)

            annotatedNamesMap


    localNamesMap





and private check (ctx : Ctx) (typeExpr : S.TypeExpr) (expr : S.Expression) : Result<unit, UnificationError> =
    failwith "@TODO not implemented checking yet"













/// This converts a PolyType to a PolyTypeContents by swapping out all the type vars for uni vars, but it returns a list of the univars it assigned, so that those can be used to zonk the PolyTypeContents back into a PolyType later
and private instantiatePolyType (ctx : Ctx) (polyType : PolyType) : PolyTypeContents =
    instantiateTypeVarsInPtc ctx polyType.forall polyType.typeExpr

and private instantiatePolyTypeList (ctx : Ctx) (polyTypes : PolyType list) : PolyTypeContents list =
    polyTypes |> List.map (instantiatePolyType ctx)



and private instantiatePolyTypeNel (ctx : Ctx) (polyTypes : PolyType nel) : PolyTypeContents nel =
    polyTypes |> NEL.map (instantiatePolyType ctx)



and private instantiatePolyTypeTom (ctx : Ctx) (polyTypes : PolyType tom) : PolyTypeContents tom =
    polyTypes |> TOM.map (instantiatePolyType ctx)



and private instantiateTypeVarsInPtc
    (ctx : Ctx)
    (typeVars : TypeVariable list)
    (polyTypeContents : PolyTypeContents)
    : PolyTypeContents =
    let typeVarToUniVarMap = getTypeVarReplacementMap ctx typeVars
    let replacedPtc = replaceTypeVarsInPtcFromMap typeVarToUniVarMap polyTypeContents

    replacedPtc





and private getTypeVarReplacementMap
    (ctx : Ctx)
    (typeVars : TypeVariable list)
    : Map<TypeVariableId, UnificationVariable> =
    //let typeVarToUniVarIdsMap =
    //    typeVars |> List.map (fun tv -> tv, makeNewUniVar ()) |> Map.ofSeq

    typeVars
    |> List.map (fun tv ->
        let newUniVarId = makeNewUniVar ()

        let uniVar =
            match tv.kind with
            | Type_ -> UnificationVariable.makeNewBlank ctx.currentLevel newUniVarId
            | TypeVariableKind.Record fields ->
                UnificationVariable.makeNewRecConstraint ctx.currentLevel newUniVarId fields

        tv.id, uniVar)
    |> Map.ofList


and private replaceTypeVarsInPtcFromMap
    (typeVarToUniVarMap : Map<TypeVariableId, UnificationVariable>)
    (polyTypeContents : PolyTypeContents)
    : PolyTypeContents =
    let rec traverser (ptc : PolyTypeContents) : PolyTypeContents =
        match ptc with
        | TypeVariable typeVar ->
            match Map.tryFind typeVar.id typeVarToUniVarMap with
            | Some uniVar ->
                match uniVar.content.Value.constrained with
                | None -> UnificationVar uniVar
                | Some constrained ->
                    match constrained with
                    | TypeConstr ptc ->
                        let replaced = traverser ptc

                        uniVar.content.Value <-
                            { uniVar.content.Value with
                                constrained = Some (TypeConstr replaced) }

                        UnificationVar uniVar

                    | RecordConstr fields ->
                        let replacedFields = List.map (Tuple.mapSnd traverser) fields

                        uniVar.content.Value <-
                            { uniVar.content.Value with
                                constrained = Some (RecordConstr replacedFields) }

                        UnificationVar uniVar


            //UnificationVar uniVar
            | None -> failwith "There should not be any type vars that don't have a uniVar assigned to replace them"

        | PTC.Skolem name -> PTC.Skolem name
        | UnificationVar uniVar ->
            match uniVar.content.Value.constrained with
            | Some constrained ->
                uniVar.content.Value <-
                    { uniVar.content.Value with
                        constrained = Some (mapToTypeOrRec traverser constrained) }

                UnificationVar uniVar

            | None -> UnificationVar uniVar

        //| RecordUnificationVar uniVar ->
        //    let uniVarContents = uniVar.content.Value

        //    uniVar.content.Value <-
        //        { uniVar.content.Value with
        //            fields = uniVarContents.fields |> NEL.map (Tuple.mapSnd traverser) }

        //    RecordUnificationVar uniVar


        | ConcreteType concrete ->
            (match concrete with
             | BuiltInPrims _ -> concrete
             | Conc.Tuple tom -> TOM.map traverser tom |> Conc.Tuple
             | Conc.List item -> traverser item |> Conc.List
             | Conc.Arrow (fromType, toType) -> Conc.Arrow (traverser fromType, traverser toType)
             | Conc.RecordExact fields -> Conc.RecordExact (List.map (Tuple.mapSnd traverser) fields)
             //| Conc.RecordOpenMaybe fields -> Conc.RecordOpenMaybe (List.map (Tuple.mapSnd traverser) fields)
             //| Conc.RecordOpenDefinitely (typeVar, fields) ->
             //    Conc.RecordOpenDefinitely (typeVar, List.map (Tuple.mapSnd traverser) fields)
             //match Map.tryFind typeVar typeVarToUniVarMap with
             //    | Some uniVar ->


             | CustomType (typeName, typeParams) -> CustomType (typeName, List.map traverser typeParams))
            |> ConcreteType

    traverser polyTypeContents



and private getUniVarsFromReplacementMap
    (typeVarToUniVarIdsMap : Map<TypeVariableId, UnificationVariable>)
    : UnificationVarId set =
    typeVarToUniVarIdsMap
    |> Map.values
    |> Seq.map UnificationVariable.getId
    |> Set.ofSeq





and private instantiateCtor
    (ctx : Ctx)
    (ctor : Ctor)
    : {| params_ : PolyTypeContents list
         result : PolyTypeContents
         uniVars : UnificationVarId set |}
    =
    let typeVarToUniVarMap = getTypeVarReplacementMap ctx ctor.forall

    let replacedParamsPtc =
        ctor.params_ |> List.map (replaceTypeVarsInPtcFromMap typeVarToUniVarMap)

    let replacedResultPtc = replaceTypeVarsInPtcFromMap typeVarToUniVarMap ctor.result

    let uniVars = getUniVarsFromReplacementMap typeVarToUniVarMap

    {| params_ = replacedParamsPtc
       result = replacedResultPtc
       uniVars = uniVars |}










(*

    Type unification

*)






and private unifyTwoTypeContents
    (ctx : Ctx)
    (type1 : PolyTypeContents)
    (type2 : PolyTypeContents)
    : Result<PolyTypeContents, UnificationError> =
    match type1, type2 with
    | PTC.TypeVariable _, _
    | _, PTC.TypeVariable _ -> failwith "All type variables should have been swapped out for unification variables!"

    | PTC.ConcreteType concType1, PTC.ConcreteType concType2 ->
        match concType1, concType2 with
        | BuiltInPrims prim1, BuiltInPrims prim2 ->
            if prim1 = prim2 then
                BuiltInPrims prim1 |> ConcreteType |> Ok
            else
                UnificationError.makeClash concType1 concType2 |> Error

        | Conc.List list1, Conc.List list2 ->
            let unifiedListType = unifyTwoTypeContents ctx list1 list2
            unifiedListType |> Result.map (Conc.List >> ConcreteType)

        | Conc.Tuple tuple1, Conc.Tuple tuple2 ->
            match TOM.zip tuple1 tuple2 with
            | Ok combinedTypeParams ->
                let paramsResults =
                    combinedTypeParams
                    |> TOM.map (fun (param1, param2) -> unifyTwoTypeContents ctx param1 param2)

                match TOM.sequenceResult paramsResults with
                | Ok unifiedParams -> Conc.Tuple unifiedParams |> PTC.ConcreteType |> Ok
                | Error errs -> NEL.head errs |> Error

            | Error _ -> UnificationError.makeClash concType1 concType2 |> Error


        | Conc.Arrow (from1, to1), Conc.Arrow (from2, to2) ->
            let unifiedFrom = unifyTwoTypeContents ctx from1 from2
            let unifiedTo = unifyTwoTypeContents ctx to1 to2

            match unifiedFrom, unifiedTo with
            | Ok from, Ok to_ -> Conc.Arrow (from, to_) |> ConcreteType |> Ok
            | Error _, _
            | _, Error _ -> UnificationError.makeClash concType1 concType2 |> Error


        | Conc.CustomType (name1, typeParams1), Conc.CustomType (name2, typeParams2) ->

            // @TODO we need to not only compare exact names but also make sure that if the two names are different aliases or under differently aliased namespaces that they still result as equal
            if name1 = name2 then
                match List.zipList typeParams1 typeParams2 with
                | Ok combinedTypeParams ->
                    let paramsResults =
                        combinedTypeParams
                        |> List.map (fun (param1, param2) -> unifyTwoTypeContents ctx param1 param2)


                    match Result.sequenceList paramsResults with
                    | Ok unifiedParams -> CustomType (name1, unifiedParams) |> PTC.ConcreteType |> Ok
                    | Error errs -> NEL.head errs |> Error

                | Error _ -> UnificationError.makeClash concType1 concType2 |> Error

            else
                UnificationError.makeClash concType1 concType2 |> Error


        | Conc.RecordExact fields1, Conc.RecordExact fields2 ->
            let sorted1 = List.sortBy fst fields1
            let sorted2 = List.sortBy fst fields2

            /// Only used if there is an error
            let clashErr : UnificationError = UnificationError.makeClash concType1 concType2

            match List.zipList sorted1 sorted2 with
            | Ok zipped ->
                let unified =
                    zipped
                    |> List.map (fun ((fieldName1, value1), (fieldName2, value2)) ->
                        if fieldName1 = fieldName2 then
                            match unifyTwoTypeContents ctx value1 value2 with
                            | Ok result -> Ok (fieldName1, result)
                            | Error e -> Error e
                        else

                            Error clashErr)
                    |> Result.sequenceList

                match unified with
                | Ok fields -> Conc.RecordExact fields |> ConcreteType |> Ok
                | Error e -> Error (NEL.head e)

            | Error _ -> Error clashErr


        | _, _ -> UnificationError.makeClash concType1 concType2 |> Error




    | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
        if uniVar1.content.Value.id = uniVar2.content.Value.id then
            Ok (PTC.UnificationVar uniVar1)

        else
            unifyUniVars ctx uniVar1 uniVar2 |> Result.map PTC.UnificationVar



    | PTC.UnificationVar uniVar, PTC.ConcreteType concreteType
    | PTC.ConcreteType concreteType, PTC.UnificationVar uniVar ->

        constrainUniVar ctx uniVar (PTC.ConcreteType concreteType |> TypeConstr)
        |> Result.map PTC.UnificationVar


    | PTC.Skolem name1, PTC.Skolem name2 ->
        if name1 = name2 then
            Ok (PTC.Skolem name1)

        else
            TriedToUnifyDifferentSkolems (name1, name2) |> Error


    | PTC.Skolem name, t
    | t, PTC.Skolem name -> NarrowedSkolem (name, t) |> Error





and private unifyTwoTypesOrRecords
    (ctx : Ctx)
    (typeOrRec1 : TypeOrRecordConstr)
    (typeOrRec2 : TypeOrRecordConstr)
    : Result<TypeOrRecordConstr, UnificationError> =
    match typeOrRec1, typeOrRec2 with
    | TypeConstr type1, TypeConstr type2 -> unifyTwoTypeContents ctx type1 type2 |> Result.map TypeConstr

    | TOR.RecordConstr record1, TOR.RecordConstr record2 ->
        let map1 = Map.ofList record1
        let map2 = Map.ofList record2

        let okifyVals map key v = Map.add key (Ok v) map

        let resultingMap =
            Map.foldAllEntries<LowerIdent, PolyTypeContents, PolyTypeContents, Map<LowerIdent, Result<PolyTypeContents, UnificationError>>>
                okifyVals
                okifyVals
                (fun map key val1 val2 -> Map.add key (unifyTwoTypeContents ctx val1 val2) map)
                map1
                map2
                Map.empty
            |> Map.sequenceResult


        match resultingMap with
        | Ok unifiedMap -> TOR.RecordConstr (Map.toList unifiedMap) |> Ok
        | Error (_, e) -> Error (NEL.head e)


    | TypeConstr type_, TOR.RecordConstr rowFields
    | TOR.RecordConstr rowFields, TypeConstr type_ ->
        match type_ with
        | UnificationVar uniVar ->
            constrainUniVar ctx uniVar (TOR.RecordConstr rowFields)
            |> Result.map (UnificationVar >> TypeConstr)

        | PTC.Skolem skolem -> NarrowedSkolem (skolem, type_) |> Error
        | ConcreteType conc ->
            match conc with
            | RecordExact exactRecFields ->
                let exactMap = Map.ofList exactRecFields
                let openMap = Map.ofList rowFields

                match Map.getOverlap exactMap openMap with
                | Map.MapsOverlap.Exact combinedMap ->
                    let unifiedResult =
                        combinedMap
                        |> Map.map (fun _ (exactVal, openVal) -> unifyTwoTypeContents ctx exactVal openVal)
                        |> Map.sequenceResult

                    match unifiedResult with
                    | Ok unified -> Ok (TOR.RecordConstr (Map.toList unified))
                    | Error (_, e) -> Error (NEL.head e)


                | Map.MapsOverlap.RightHasMore (shared, diffRight) ->
                    let openExcessFields = diffRight |> Map.keys |> Set.ofSeq
                    let exactFields = shared |> Map.keys |> Set.ofSeq

                    OpenRecordHasMoreFieldsThanExactRecord (openExcessFields, exactFields) |> Error

                | Map.MapsOverlap.BothHaveMore (_, shared, diffRight) ->
                    let openExcessFields = diffRight |> Map.keys |> Set.ofSeq
                    let exactFields = shared |> Map.keys |> Set.ofSeq

                    OpenRecordHasMoreFieldsThanExactRecord (openExcessFields, exactFields) |> Error

                | Map.MapsOverlap.LeftHasMore (diffLeft, shared) ->
                    let unifiedResult =
                        shared
                        |> Map.map (fun _ (exactVal, openVal) -> unifyTwoTypeContents ctx exactVal openVal)
                        |> Map.sequenceResult

                    match unifiedResult with
                    | Ok unified ->
                        Map.merge unified diffLeft
                        |> Map.toList
                        |> RecordExact
                        |> ConcreteType
                        |> TypeConstr
                        |> Ok

                    | Error (_, e) -> Error (NEL.head e)

            | _ -> RecordTypeClash (rowFields, conc) |> Error


        | TypeVariable _ -> failwith "There should be no type variables during unification!"

















/// Other than the trivial case of unifying a univar with itself, a univar can't be unified with another type containing itself. Otherwise you'd have an infinitely recursive type. So we need to check that that's not what we're doing here.
///
/// Returns true if the univar is indeed somewhere nested inside the PTC resulting in infinite recursive type if we were to try and unify them
///
/// @TODO: I think what we can do here is maybe pass in a parameter for "is this a direct match or an indirect one" and that will let this function do more than just check "is this bad" but actually it could tell us either i. there is no circular reference here at all, ii. there is a circular reference but it's not a problem because it's a direct match, e.g. univar1 = univar2 = univar1 iii. there is a circular reference and it's a problem because it's an indirect match, e.g. univar1 = (bla, univar1).
and private occursCheck (univar : UnificationVariable) (typeOrRec : TypeOrRecordConstr) : OccursCheckResult =
    /// Is the predicate true for any item in the list
    let forAny pred = Seq.fold (fun state item -> state || pred item) false

    let rec nestedOccursCheckPtc (ptc_ : PolyTypeContents) : bool =
        match ptc_ with
        | UnificationVar innerUniVar -> innerUniVar.content.Value.id = univar.content.Value.id

        | TypeVariable _ -> false
        | PTC.Skolem _ -> false
        | ConcreteType concType ->
            match concType with
            | BuiltInPrims _ -> false
            | Conc.Tuple typeParams -> forAny nestedOccursCheckPtc typeParams
            | Conc.List typeParam -> nestedOccursCheckPtc typeParam
            | Conc.Arrow (fromType, toType) -> nestedOccursCheckPtc fromType || nestedOccursCheckPtc toType
            | Conc.RecordExact fields -> forAny (snd >> nestedOccursCheckPtc) fields
            | Conc.CustomType (_, typeParams) -> forAny nestedOccursCheckPtc typeParams

    and nestedOccursCheckRecord (fields : RowField list) : bool = fields |> forAny (snd >> nestedOccursCheckPtc)



    match typeOrRec with
    | TypeConstr (UnificationVar _) ->
        // I.e. top levels univars being equal to each other is not a problem. It's only nested ones that are a problem.
        // @TODO actually I'm not sure if this logic is correct? feels like we need to actually be checking through the univars
        false

    | TypeConstr ptc_ -> nestedOccursCheckPtc ptc_
    | TOR.RecordConstr record -> nestedOccursCheckRecord record




/// Point two univars to the same thing
/// @TODO need to make sure that if we're unifying two univars that are actually the same by means of an intermediate univar, that we can just unify them all in one go (along with all other univars on the way I suppose)
and private unifyUniVars
    (ctx : Ctx)
    (uniVar1 : UnificationVariable)
    (uniVar2 : UnificationVariable)
    : Result<UnificationVariable, UnificationError> =
    if uniVar1.content.Value.id = uniVar2.content.Value.id then
        Ok uniVar1

    else
        match uniVar1.content.Value.constrained, uniVar2.content.Value.constrained with
        | None, None ->
            let minBy f a b = if f a < f b then (a, b) else (b, a)

            let (lowestLevelUniVar, higherUniVar) =
                minBy (fun v -> v.content.Value.levelDeclared) uniVar1 uniVar2

            lowestLevelUniVar.content.Value <-
                { lowestLevelUniVar.content.Value with
                    constrained = Some (PTC.UnificationVar higherUniVar |> TypeConstr) }

            Ok lowestLevelUniVar

        | Some _, None ->
            uniVar2.content.Value <-
                { uniVar2.content.Value with
                    constrained = Some (PTC.UnificationVar uniVar1 |> TypeConstr) }

            Ok uniVar2


        | None, Some _ ->
            uniVar1.content.Value <-
                { uniVar1.content.Value with
                    constrained = Some (PTC.UnificationVar uniVar2 |> TypeConstr) }

            Ok uniVar1

        | Some result1, Some result2 ->
            if occursCheck uniVar1 result2 then
                InfinitelyRecursiveType (uniVar1, result2) |> Error

            elif occursCheck uniVar2 result1 then
                InfinitelyRecursiveType (uniVar2, result1) |> Error

            else
                let unifiedResult = unifyTwoTypesOrRecords ctx result1 result2

                match unifiedResult with
                | Ok unified ->
                    uniVar2.content.Value <-
                        { uniVar2.content.Value with
                            constrained = Some unified }


                    uniVar1.content.Value <-
                        { uniVar1.content.Value with
                            constrained = Some (PTC.UnificationVar uniVar2 |> TypeConstr) }

                    Ok uniVar1

                | Error e -> Error e





/// Add a constraint to a univar
and private constrainUniVar
    (ctx : Ctx)
    (uniVar : UnificationVariable)
    (constraint_ : TypeOrRecordConstr)
    : Result<UnificationVariable, UnificationError> =
    let content = uniVar.content.Value

    match content.constrained with
    | None ->
        uniVar.content.Value <-
            { uniVar.content.Value with
                constrained = Some constraint_ }

        Ok uniVar

    | Some existingConstraint ->
        if occursCheck uniVar constraint_ then
            InfinitelyRecursiveType (uniVar, constraint_) |> Error

        else

            match unifyTwoTypesOrRecords ctx existingConstraint constraint_ with
            | Ok unified ->
                uniVar.content.Value <-
                    { uniVar.content.Value with
                        constrained = Some unified }

                Ok uniVar

            | Error e -> Error e





and private combineNamesMaps
    (ctx : Ctx)
    (namesMap1 : TypedLocalNamesMap)
    (namesMap2 : TypedLocalNamesMap)
    : TypedLocalNamesMap =
    let merger _ polytype1 polytype2 = unifyTwoTypeResults ctx polytype1 polytype2

    // @TODO hm I don't think we need a merger that does unification, I think we just need to forbid the same name from being inserted in the first place. If we have to occurrences of the name `a` being assigned to different things, we don't fix that by unifying both expressions' types, we just throw an error that shadowing is not allowed!
    Map.mergeSafe merger namesMap1 namesMap2



and private combineAssignmentNamesMaps
    (ctx : Ctx)
    (namesMap1 : AssignmentNamesMap)
    (namesMap2 : AssignmentNamesMap)
    : AssignmentNamesMap =
    let merger _ polytype1 polytype2 = unifyTwoTypeContentsResults ctx polytype1 polytype2
    // @TODO same here as above
    Map.mergeSafe merger namesMap1 namesMap2



/// This one converts *without zonking*
and private convertAssignmentNamesMapToTypedLocalNamesMap : AssignmentNamesMap -> TypedLocalNamesMap =
    Map.map (fun _ -> Result.map Types.makePoly)


and private zonkAssignmentNamesMap (ctx : Ctx) : AssignmentNamesMap -> TypedLocalNamesMap =
    Map.map (fun _ ptcResult -> zonkPolyTypeContentsResult ctx ptcResult)




and private unifyTwoTypes (ctx : Ctx) (type1 : PolyType) (type2 : PolyType) : Result<PolyType, UnificationError> =
    let ptc1 = instantiatePolyType ctx type1
    let ptc2 = instantiatePolyType ctx type2

    unifyTwoTypeContents ctx ptc1 ptc2 |> zonkPolyTypeContentsResult ctx




and private unifyTwoTypeResults
    (ctx : Ctx)
    (typeResult1 : Result<PolyType, UnificationError>)
    (typeResult2 : Result<PolyType, UnificationError>)
    : Result<PolyType, UnificationError> =
    match typeResult1, typeResult2 with
    | Ok type1, Ok type2 -> unifyTwoTypes ctx type1 type2
    | Error e, _
    | _, Error e -> Error e



and private unifyMultipleTypeResults
    (ctx : Ctx)
    (typeResults : Result<PolyType, UnificationError> nel)
    : Result<PolyType, UnificationError> =
    let (NEL (head, rest)) = typeResults
    List.fold (unifyTwoTypeResults ctx) head rest





and private unifyTwoTypeContentsResults
    (ctx : Ctx)
    (typeContentResult1 : Result<PolyTypeContents, UnificationError>)
    (typeContentResult2 : Result<PolyTypeContents, UnificationError>)
    : Result<PolyTypeContents, UnificationError> =
    match typeContentResult1, typeContentResult2 with
    | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents ctx typeContent1 typeContent2

    | Error e, _
    | _, Error e -> Error e



and private unifyMultipleTypeContentResults
    (ctx : Ctx)
    (typeResults : Result<PolyTypeContents, UnificationError> nel)
    : Result<PolyTypeContents, UnificationError> =
    let (NEL (head, rest)) = typeResults
    List.fold (unifyTwoTypeContentsResults ctx) head rest





and private unifyMultipleTypeContents
    (ctx : Ctx)
    (typeResults : PolyTypeContents nel)
    : Result<PolyTypeContents, UnificationError> =
    let (NEL (head, rest)) = typeResults
    List.fold (fun state item -> Result.bind (unifyTwoTypeContents ctx item) state) (Ok head) rest




/// This infers the type of a self contained expression and zonks the result to remove any unsightly unification vars in the result
let topLevelInferExpressionType (expr : S.Expression) : Result<PolyType, UnificationError> =
    let ctx = Ctx.empty

    inferTypeFromExpr ctx expr |> zonkPolyTypeContentsResult ctx









//(*

//@TODO list:

//- [ ] resolve named values
//    - [ ] in local scopes
//    - [ ] from other modules
//- [ ] infer types of primitives
//- [ ] infer types of values referencing primitives
//- [ ] infer types of

//- [ ] parse type annotations
//- [ ] infer types of values or function params by looking at the functions they are getting passed into
//    - [ ] and similarly the types of values passed to operators

//- [ ] support flagging up type clashes
//    - [ ] and have some way of linking that back to a specific token, or even buffer range?

//- [ ] support types with type params, e.g. `List a`
//- [ ] support narrowing of types with type params while leaving the type params as generic

//- [ ] support a parallel, field-name-and-value-based, type inference system to support typed records as extensible, partially typed things, instead of the all or nothing type system of generics vs explicit types specified above

//*)










/////// Converts a "mentionable type" representing a type expression to a TypeConstraints representing our internal type representation.
/////// It has to be a type constraint and not a definitive type because we need to take into consideration type params (which may not be declared) and references to type names (which may not exist)
////let rec mentionableTypeToDefinite (mentionable : Cst.MentionableType) : TypeConstraints =
////    match mentionable with
////    | S.UnitType -> TypeConstraints.fromDefinitive DtUnitType
////    | S.GenericTypeVar unqual ->
////        unqualValToLowerIdent unqual
////        |> ByTypeParam
////        |> TypeConstraints.fromConstraint

////    | S.Tuple { types = types } ->
////        types
////        |> TOM.map (S.getNode >> mentionableTypeToDefinite)
////        |> DtTuple
////        |> TypeConstraints.fromDefinitive

////    | S.Record { fields = fields } ->
////        fields
////        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
////        |> DtRecordExact
////        |> TypeConstraints.fromDefinitive

////    | S.ExtendedRecord { extendedTypeParam = extendedParam
////                         fields = fields } ->
////        // TODO: ensure that we actually try to resolve the extended param at some point so that we type this type expression correctly

////        fields
////        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
////        |> DtRecordWith
////        |> TypeConstraints.fromDefinitive

////    | S.ReferencedType (typeName, typeParams) ->
////        let definiteTypeParams =
////            List.map (S.getNode >> mentionableTypeToDefinite) typeParams

////        //IsOfTypeByName (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
////        //|> TypeConstraints.fromConstraint
////        DtNewType (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
////        |> TypeConstraints.fromDefinitive

////    | S.Arrow (fromType, toTypes) ->
////        DtArrow (
////            mentionableTypeToDefinite fromType.node,
////            NEL.map S.getNode toTypes
////            |> mentionableArrowToDefinite
////        )
////        |> TypeConstraints.fromDefinitive

////    | S.Parensed parensed -> mentionableTypeToDefinite parensed.node


/////// Converts an NEL representing one or more destination types in an arrow type to a single type
////and private mentionableArrowToDefinite (toTypes : Cst.MentionableType nel) : TypeConstraints =
////    let (NEL (first, rest)) = toTypes
////    let convertedFirst = mentionableTypeToDefinite first

////    match rest with
////    | [] -> convertedFirst
////    | head :: tail ->
////        DtArrow (convertedFirst, mentionableArrowToDefinite (NEL (head, tail)))
////        |> TypeConstraints.fromDefinitive







//(*

//    Operator grouping stuff

//*)


////type FlatOpList<'a> =
////    | LastVal of 'a
////    | Op of left : 'a * op : Lexer.BuiltInOperator * right : FlatOpList<'a>


////let rec opSeqToFlatOpList
////    (leftOperand : Cst.Expression)
////    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
////    : FlatOpList<Cst.Expression> =
////    let (NEL ((firstOp, sndExpr), rest)) = opSequence

////    Op (
////        leftOperand,
////        firstOp,
////        (match rest with
////         | [] -> LastVal sndExpr
////         | headOfRest :: restOfRest -> opSeqToFlatOpList sndExpr (NEL.new_ headOfRest restOfRest))
////    )


/////// @TODO: this currently only supports built-in operators, not custom ones
////type OpBinaryTree =
////    { left : BinaryTreeBranch
////      op : Lexer.BuiltInOperator
////      right : BinaryTreeBranch }


////and BinaryTreeBranch =
////    | Branch of OpBinaryTree
////    | Leaf of Cst.Expression




////let updateLastInList updater list =
////    List.rev list
////    |> (function
////    | [] -> []
////    | head :: rest -> updater head :: rest)
////    |> List.rev


////let updateOrAddIfEmpty updater toAdd list =
////    List.rev list
////    |> (function
////    | [] -> [ toAdd ]
////    | head :: rest -> updater head :: rest)
////    |> List.rev


////type ExprWithOpsList<'a> = | ExprWithOpsList of 'a * (BuiltInOperator * 'a) list



////type SplitLists<'a> = ExprWithOpsList<ExprWithOpsList<'a>>


////let newExprWithOpsList a = ExprWithOpsList (a, List.empty)

////let addToExprWithOpsList toAdd (ExprWithOpsList (a, list)) =
////    ExprWithOpsList (a, list @ [  toAdd ])


////let editLastInExprWithOpsList  toAdd (ExprWithOpsList (a, list): SplitLists<Cst.Expression>) =
////    ExprWithOpsList (a, updateOrAddIfEmpty (addToExprWithOpsList  toAdd) list)



////type FoldSuccess<'a> =
////    { lastOperand : 'a
////      listsSoFar : SplitLists<'a>
////      /// This should contain the lowest precedence other than the one we are currently looking at
////      lowestPrecedence : int option
////      associativity : S.InfixOpAssociativity option }



////let rec splitOpList
////    (precedence : int)
////    (firstOperand : Cst.Expression)
////    (opSeq : (Lexer.BuiltInOperator * Cst.Expression) list)
////    =
////    let initState : FoldSuccess<Cst.Expression> =
////        { lastOperand = firstOperand
////          listsSoFar =
////            newExprWithOpsList firstOperand
////            |> newExprWithOpsList
////          lowestPrecedence = None
////          associativity = None }

////    opSeq
////    |> List.fold<_, FoldSuccess<Cst.Expression>>
////        (fun state (op, expr) ->
////            let op_ = NameResolution.getBuiltInInfixOp op

////            if op_.precedence <= precedence then
////                match state.associativity with
////                | Some assoc ->
////                    match assoc with
////                    | S.Non ->
////                        failwith "@TODO: error! can't have more than one operator with non associativity without parens"
////                    | S.Left
////                    | S.Right ->
////                        if op_.associativity = assoc then
////                            let newLists = addToExprWithOpsList op (newExprWithOpsList expr) state.listsSoFar

////                            { lastOperand = expr
////                              listsSoFar = newLists
////                              lowestPrecedence = state.lowestPrecedence
////                              associativity = Some assoc }

////                        else
////                            failwith
////                                "@TODO: can't have more than one operator at the same level with different associativity. Need to group the expressions in parentheses!"

////                | None ->
////                    let newLists = addToExprWithOpsList op (newExprWithOpsList expr) state.listsSoFar

////                    { lastOperand = expr
////                      listsSoFar = newLists
////                      lowestPrecedence = state.lowestPrecedence
////                      associativity = Some op_.associativity }


////            else
////                // add to current list + keep track if operator is lower than the current lowest one?

////                let newLists = editLastInExprWithOpsList

////            )
////        initState



//////let rec processListRecursively firstOperand (opSeq : (Lexer.BuiltInOperator * Cst.Expression) nel)
//////    let splitList = splitOpList 0 opSeq



///////// Splits the operator list according to precedence and associativity
//////let rec splitOpList currPrecedence (opSeq : (Lexer.BuiltInOperator * Cst.Expression) nel) =
//////    match opSeq with
//////    | NEL ((op, expr), []) -> Last (op, expr)
//////    | NEL ((op, expr), head :: rest) ->
//////        let op_ = NameResolution.getBuiltInInfixOp op

//////        let newNel = NEL.new_ head rest

//////        if op_.precedence <= currPrecedence then
//////            New ((op, expr), splitOpList currPrecedence newNel)
//////        else
//////            Continue ((op, expr), splitOpList currPrecedence newNel)



//////let rec splitOpSeqs (currPrecedence : int) (opSeq : FlatOpList<Cst.Expression>) : PartialOrFull<Cst.Expression> =
//////    match opSeq with
//////    | LastVal e -> Leaf e
//////    | Op (left, op, right) ->
//////        let op_ = NameResolution.getBuiltInInfixOp op

//////        if op_.precedence <= currPrecedence then
//////            LastVal left





//////let rec normaliseOpSequence (currPrecedence:int)
//////    (leftOperand : Cst.Expression)
//////    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
//////    : OpBinaryTree =
//////    let (NEL ((firstOp, sndExpr), rest)) = opSequence

//////    let op = NameResolution.getBuiltInInfixOp firstOp

//////    match rest with
//////    | [] ->
//////        { left = Leaf leftOperand
//////          op = firstOp
//////          right = Leaf sndExpr }

//////    | headOfRest :: restOfRest ->
//////        if op.precedence <= currPrecedence then
//////            match op.associativity with
//////            | S.Non ->
//////                { left = normaliseOpSequence
//////                  op = firstOp
//////                  right = normaliseOpSequence


//////let rec normaliseOpSequence
//////    (leftOperand : BinaryTreeBranch)
//////    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
//////    : OpBinaryTree =
//////    let (NEL ((firstOp, sndExpr), rest)) = opSequence
//////    let op = NameResolution.getBuiltInInfixOp firstOp

//////    match leftOperand, rest with
//////    | Leaf leftExpr, [] ->
//////        { left = Leaf leftExpr
//////          op = firstOp
//////          highestPrecedence = op.precedence
//////          right = Leaf sndExpr }

//////    | Leaf leftExpr, headOfRest :: restOfRest ->
//////        { left = Leaf leftExpr
//////          op = firstOp
//////          highestPrecedence = op.precedence
//////          right =
//////            normaliseOpSequence (Leaf sndExpr) (NEL.new_ headOfRest restOfRest)
//////             }

//////    | Branch leftTree, [] ->
//////        { left = Branch leftTree
//////          op = firstOp
//////          highestPrecedence = op.precedence
//////          right = Leaf sndExpr }


//////    | Branch leftTree, headOfRest :: restOfRest ->
//////        let rightTree = normaliseOpSequence (Leaf sndExpr) (NEL.new_ headOfRest restOfRest)

//////        if op.precedence > rightTree.precedence
//////           && op.precedence > leftTree.precedence then
//////            { left = Branch leftTree
//////              op = firstOp
//////              highestPrecedence = op.precedence
//////              right = Branch rightTree }

//////        else if op.precedence < subTree.highestPrecedence then








/////// Creates a binary tree of operations, correctly constructed according to associativity and precedence
//////let createOpBinaryTree (firstExpr : S.CstNode<Q.Expression >) (opExprSeq : (S.CstNode<Q.Operator > * S.CstNode<Q.Expression> ) nel ) : OpBinaryTree =
////// associativity: right is like the (::) operator. I.e. we consider everything to the right to be a single expression before appending the left things to it. Otherwise `a :: b :: []` would be parsed as `(a :: b) :: []`, which is wrong.
////// associativity: left is the opposite. i.e. `a (op) b (op) c` is equivalent to `(a (op) b) (op) c`

















//let rec convertAssignmentPattern (pattern : Cst.AssignmentPattern) : T.AssignmentPattern =
//    match pattern with
//    | S.Named name -> Named (unqualValToLowerIdent name)
//    | S.Ignored -> Ignored
//    | S.Unit -> Unit
//    | S.DestructuredPattern p ->
//        convertDestructuredPattern p
//        |> DestructuredPattern
//    | S.Aliased (p, alias) -> Aliased (convertAssignmentPattern p.node, unqualValToLowerIdent alias.node)


//and convertDestructuredPattern (pattern : Cst.DestructuredPattern) : T.DestructuredPattern =
//    match pattern with
//    | S.DestructuredRecord fields ->
//        NEL.map (S.getNode >> unqualValToRecField) fields
//        |> DestructuredRecord
//    | S.DestructuredTuple items ->
//        TOM.map (S.getNode >> convertAssignmentPattern) items
//        |> DestructuredTuple
//    | S.DestructuredCons items ->
//        TOM.map (S.getNode >> convertAssignmentPattern) items
//        |> DestructuredCons
//    | S.DestructuredTypeVariant (ctor, params_) ->
//        DestructuredTypeVariant (
//            typeOrModuleIdentToUpperNameVal ctor.node,
//            List.map (S.getNode >> convertAssignmentPattern) params_
//        )




//let rec gatherParams (pattern : T.AssignmentPattern) : T.FunctionOrCaseMatchParam =
//    match pattern with
//    | Named ident ->
//        let param_ : Param = { destructurePath = SimpleName }

//        { paramPattern = pattern
//          namesMap = Map.add ident (SOD.new_ param_) Map.empty }

//    | Ignored ->
//        { paramPattern = pattern
//          namesMap = Map.empty }

//    | Unit ->
//        { paramPattern = pattern
//          namesMap = Map.empty }

//    | DestructuredPattern destructured ->
//        { paramPattern = pattern
//          namesMap = gatherDestructuredPattern destructured }

//    | Aliased (aliased, alias) ->

//        let param_ : Param = { destructurePath = SimpleName }

//        let gatheredFromAlias = gatherParams aliased

//        { paramPattern = pattern
//          namesMap =
//            gatheredFromAlias.namesMap
//            |> NameResolution.addNewReference alias param_ }




//and gatherDestructuredPattern (pattern : T.DestructuredPattern) : Map<LowerIdent, SOD<Param>> =
//    /// Adjusts the destructure path of a param to account for the fact that it is contained inside a nested destructuring
//    let adjustDestructurePath (newPath : PathToDestructuredName) (param_ : Param) : Param =
//        { param_ with destructurePath = newPath }


//    match pattern with
//    | DestructuredRecord fields ->
//        fields
//        |> NEL.map (fun recField ->
//            let ident = recFieldToLowerIdent recField

//            ident, { Param.destructurePath = InverseRecord })
//        |> NEL.toList
//        |> SOD.makeMapFromList

//    | DestructuredTuple patterns ->
//        TOM.map gatherParams patterns
//        |> TOM.mapi (fun index tupleItem ->
//            tupleItem.namesMap
//            |> Map.map (fun _ paramsEntries ->
//                paramsEntries
//                |> SOD.map (fun param -> adjustDestructurePath (InverseTuple (uint index, param.destructurePath)) param)))
//        |> TOM.fold NameResolution.combineTwoReferenceMaps Map.empty


//    | DestructuredCons patterns ->
//        patterns
//        |> TOM.map gatherParams
//        |> TOM.mapi (fun index params_ ->
//            params_.namesMap
//            |> Map.map (fun _ paramEntries ->
//                paramEntries
//                |> SOD.map (fun param_ ->
//                    adjustDestructurePath (InverseCons (uint index, param_.destructurePath)) param_)))
//        |> TOM.fold Map.merge Map.empty

//    | DestructuredTypeVariant (ctor, params_) ->
//        params_
//        |> List.map gatherParams
//        |> List.mapi (fun index params__ ->
//            params__.namesMap
//            |> Map.map (fun _ paramEntries ->
//                paramEntries
//                |> SOD.map (fun param_ ->
//                    adjustDestructurePath (InverseTypeVariant (ctor, uint index, param_.destructurePath)) param_)))
//        |> List.fold Map.merge Map.empty




//let typeFuncOrCaseMatchParam : Cst.AssignmentPattern -> FunctionOrCaseMatchParam =
//    convertAssignmentPattern >> gatherParams




//let typeOfPrimitiveLiteral (primitive : S.PrimitiveLiteralValue) : DefinitiveType =
//    match primitive with
//    | S.NumberPrimitive num ->
//        match num with
//        | S.FloatLiteral _ -> DtPrimitiveType Float
//        | S.IntLiteral _ -> DtPrimitiveType Int
//    | S.CharPrimitive _ -> DtPrimitiveType Char
//    | S.StringPrimitive _ -> DtPrimitiveType String
//    | S.UnitPrimitive _ -> DtUnitType
//    | S.BoolPrimitive _ -> DtPrimitiveType Bool





//let refDeftypeOfPrimitiveLiteral (primitive : S.PrimitiveLiteralValue) : RefDefType =
//    match primitive with
//    | S.NumberPrimitive num ->
//        match num with
//        | S.FloatLiteral _ -> RefDtPrimType Float
//        | S.IntLiteral _ -> RefDtPrimType Int
//    | S.CharPrimitive _ -> RefDtPrimType Char
//    | S.StringPrimitive _ -> RefDtPrimType String
//    | S.UnitPrimitive _ -> RefDtUnitType
//    | S.BoolPrimitive _ -> RefDtPrimType Bool





//(*
//    Helpers for replacing bound variables with Guids that represent invariant constraints
//*)


///// This will only return names in the keys and only if they are locally defined, not namespaced ones
//let getLocalValueNames (acc : Accumulator) : LowerIdent set =
//    Map.values acc.refConstraintsMap
//    |> Seq.map snd
//    |> Set.unionMany
//    |> Set.choose (function
//        | ByValue (LocalLower name) -> Some name
//        | _ -> None)


//let makeGuidMapForNames (names : LowerIdent set) : Map<LowerIdent, TypeConstraintId> =
//    Set.toList names
//    |> List.map (fun name -> name, makeTypeConstrId ())
//    |> Map.ofList




//let rec replaceRefConstrInTypeConstraints (switcher : RefConstr set -> RefConstr set) (tc : TypeConstraints) =
//    let (TypeConstraints (defOpt, refs)) = tc

//    TypeConstraints (Option.map (replaceRefConstrInDefType switcher) defOpt, switcher refs)

//and replaceRefConstrInDefType (switcher : RefConstr set -> RefConstr set) (defType : DefinitiveType) =
//    match defType with
//    | DtUnitType -> DtUnitType
//    | DtPrimitiveType p -> DtPrimitiveType p
//    | DtTuple tom -> DtTuple (TOM.map (replaceRefConstrInTypeConstraints switcher) tom)
//    | DtList tc -> DtList (replaceRefConstrInTypeConstraints switcher tc)
//    | DtRecordWith fields -> DtRecordWith (Map.map (fun _ -> replaceRefConstrInTypeConstraints switcher) fields)
//    | DtRecordExact fields -> DtRecordExact (Map.map (fun _ -> replaceRefConstrInTypeConstraints switcher) fields)
//    | DtNewType (typeName, typeParams) ->
//        DtNewType (typeName, List.map (replaceRefConstrInTypeConstraints switcher) typeParams)
//    | DtArrow (fromType, toType) ->
//        DtArrow (replaceRefConstrInTypeConstraints switcher fromType, replaceRefConstrInTypeConstraints switcher toType)



/////
///// Replaces the references to names in the ref constraints with guids
//let singleSwitcher (names : Map<LowerIdent, TypeConstraintId>) (refConstr : RefConstr) =
//    match refConstr with
//    | ByValue (LocalLower ident) ->
//        match Map.tryFind ident names with
//        | Some replacementId -> IsBoundVar replacementId
//        | None -> refConstr

//    //| HasTypeOfFirstParamOf constr' -> HasTypeOfFirstParamOf (singleSwitcher names constr')
//    //| IsOfTypeByName (name, typeParams) ->
//    //    IsOfTypeByName (name, List.map (replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names))) typeParams)
//    | _ -> refConstr




//let replaceValueNamesWithGuidsInTypeConstraints
//    (names : Map<LowerIdent, TypeConstraintId>)
//    (tc : TypeConstraints)
//    : TypeConstraints =
//    replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names)) tc


///// Replaces name references with bound var constraint IDs
//let replaceNameRefsWithBoundVars (names : Map<LowerIdent, TypeConstraintId>) (acc : Accumulator) : Accumulator =
//    let switcher = Set.map (singleSwitcher names)

//    { acc with
//        refConstraintsMap =
//            acc.refConstraintsMap
//            |> Map.map (fun _ (refDefOpt, refConstrs) -> refDefOpt, switcher refConstrs) }



//let replaceValueNamesWithGuidsInTypeJudgment
//    (names : Map<LowerIdent, TypeConstraintId>)
//    (typeJudgment : TypeJudgment)
//    : TypeJudgment =
//    Result.map (replaceValueNamesWithGuidsInTypeConstraints names) typeJudgment









//let rec private deleteAllBoundVarsFromRefConstraints (refConstr : RefConstr) =
//    match refConstr with
//    | IsBoundVar _ -> None
//    | _ -> Some refConstr


//and deleteGuidsFromDefType (defType : DefinitiveType) =
//    match defType with
//    | DtUnitType -> DtUnitType
//    | DtPrimitiveType p -> DtPrimitiveType p
//    | DtTuple tom -> DtTuple (TOM.map (deleteGuidsFromTypeConstraints) tom)
//    | DtList tc -> DtList (deleteGuidsFromTypeConstraints tc)
//    | DtRecordWith fields -> DtRecordWith (Map.map (fun _ -> deleteGuidsFromTypeConstraints) fields)
//    | DtRecordExact fields -> DtRecordExact (Map.map (fun _ -> deleteGuidsFromTypeConstraints) fields)
//    | DtNewType (typeName, typeParams) -> DtNewType (typeName, List.map (deleteGuidsFromTypeConstraints) typeParams)
//    | DtArrow (fromType, toType) ->
//        DtArrow (deleteGuidsFromTypeConstraints fromType, deleteGuidsFromTypeConstraints toType)



///// Delete bound vars with guids from TypeConstraints, for better test comparisons
//and deleteGuidsFromTypeConstraints (tc : TypeConstraints) =
//    let (TypeConstraints (defOpt, refs)) = tc

//    TypeConstraints (Option.map (deleteGuidsFromDefType) defOpt, Set.choose (deleteAllBoundVarsFromRefConstraints) refs)








///// Converts a CST node to an AST node ready for type inference
//let rec convertCstToAst (resolutionChain : LowerIdent list) (expr : Cst.Expression) : T.Expression =

//    match expr with
//    | S.SingleValueExpression singleVal ->
//        match singleVal with
//        | S.ExplicitValue explicit ->
//            match explicit with
//            | S.Primitive primitive ->
//                Primitive primitive
//                |> ExplicitValue
//                |> SingleValueExpression


//            | S.DotGetter dotGetter ->
//                let recFieldName = unqualValToRecField dotGetter

//                DotGetter recFieldName
//                |> ExplicitValue
//                |> SingleValueExpression

//            | S.Compound compound ->
//                match compound with
//                | S.List list ->
//                    let typedList = List.map (S.getNode >> convertCstToAst resolutionChain) list

//                    typedList
//                    |> T.List
//                    |> Compound
//                    |> ExplicitValue
//                    |> SingleValueExpression

//                | S.CompoundValues.Tuple tuple ->
//                    let typedList = TOM.map (S.getNode >> convertCstToAst resolutionChain) tuple

//                    typedList
//                    |> CompoundValues.Tuple
//                    |> Compound
//                    |> ExplicitValue
//                    |> SingleValueExpression

//                | S.CompoundValues.Record record ->
//                    let typedList =
//                        record
//                        |> List.map (fun (key, value) ->
//                            unqualValToRecField key.node, convertCstToAst resolutionChain value.node)

//                    typedList
//                    |> CompoundValues.Record
//                    |> Compound
//                    |> ExplicitValue
//                    |> SingleValueExpression

//                | S.CompoundValues.RecordExtension (extended, additions) ->

//                    let typedList =
//                        additions
//                        |> NEL.map (fun (key, value) ->
//                            unqualValToRecField key.node, convertCstToAst resolutionChain value.node)

//                    CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
//                    |> Compound
//                    |> ExplicitValue
//                    |> SingleValueExpression

//            | S.Function funcVal ->
//                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
//                let typeOfBody = convertCstToAst resolutionChain funcVal.body.node

//                let funcParams : FunctionOrCaseMatchParam nel =
//                    funcVal.params_
//                    |> NEL.map (S.getNode >> typeFuncOrCaseMatchParam)


//                let funcVal : FunctionValue =
//                    { params_ = funcParams
//                      body = typeOfBody }

//                Function funcVal
//                |> ExplicitValue
//                |> SingleValueExpression


//        | S.UpperIdentifier name ->
//            let ctorName = typeOrModuleIdentToUpperNameVal name

//            UpperIdentifier ctorName |> SingleValueExpression

//        | S.LowerIdentifier name ->
//            let lowerNameVal = convertValueIdentifierToLowerName name

//            LowerIdentifier lowerNameVal
//            |> SingleValueExpression

//        | S.LetExpression (declarations, expr) ->

//            let bodyExpr = convertCstToAst resolutionChain expr.node


//            let typedDeclarations : LetBindings =
//                declarations
//                |> NEL.map (fun binding -> binding.node.bindPattern.node, binding.node.value.node)
//                |> NEL.map (fun (bindPattern, bindValue) ->
//                    let param = typeFuncOrCaseMatchParam bindPattern
//                    let boundNames = param.namesMap |> Map.keys |> Seq.toList
//                    let assignedExpr = convertCstToAst (boundNames @ resolutionChain) bindValue

//                    { paramPattern = param.paramPattern
//                      namesMap = param.namesMap
//                      assignedExpression = assignedExpr })

//            LetExpression (typedDeclarations, bodyExpr)
//            |> SingleValueExpression


//        | S.ControlFlowExpression controlFlow ->
//            match controlFlow with
//            | S.IfExpression (cond, ifTrue, ifFalse) ->
//                let conditionalWithBoolConstraint = convertCstToAst resolutionChain cond.node

//                // This is aiming to express the type constraint that both branches of the if expression should have the same type

//                let typedIfTrueBranch = convertCstToAst resolutionChain ifTrue.node
//                let typedIfFalseBranch = convertCstToAst resolutionChain ifFalse.node

//                // This should leave whichever one had the original definitive type unchanged, and only add a definitive constraint to the other one
//                let unifiedTrue = typedIfTrueBranch
//                let unifiedFalse = typedIfFalseBranch

//                IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
//                |> ControlFlowExpression
//                |> SingleValueExpression


//            | S.CaseMatch (exprToMatch, branches) ->
//                let typedExprToMatch = convertCstToAst resolutionChain exprToMatch.node

//                let typedBranches =
//                    branches
//                    |> NEL.map (fun (pattern, branchExpr) ->
//                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
//                          body = convertCstToAst resolutionChain branchExpr.node })

//                CaseMatch (typedExprToMatch, typedBranches)
//                |> ControlFlowExpression
//                |> SingleValueExpression

//    | S.CompoundExpression compExpr ->
//        match compExpr with
//        | S.FunctionApplication (funcExpr, params_) ->
//            let typedFunc = convertCstToAst resolutionChain funcExpr.node

//            let typedParams =
//                params_
//                |> NEL.map (S.getNode >> convertCstToAst resolutionChain)

//            FunctionApplication (typedFunc, typedParams)
//            |> CompoundExpression

//        | S.DotAccess (dottedExpr, dotSequence) ->
//            let rec makeNestedMap (fieldSeq : RecordFieldName list) =
//                match fieldSeq with
//                | [] -> TypeConstraints.empty
//                | head :: rest ->
//                    Map.empty
//                    |> Map.add head (makeNestedMap rest)
//                    |> DtRecordWith
//                    |> TypeConstraints.fromDefinitive

//            let typedExpr = convertCstToAst resolutionChain dottedExpr.node

//            DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
//            |> CompoundExpression

//        | S.Operator (left, opSequence) ->
//            failwith
//                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"

//    | S.ParensedExpression expr -> convertCstToAst resolutionChain expr






















//module Acc = Accumulator
//module Aati = Acc.AccAndTypeId

//type private AccAndTypeId = Acc.AccAndTypeId

///// Just effectively a module alias import
//type private TC = TypeConstraints














///// Map from type names to the actual types
//type TypesInScope = Map<UpperNameValue, UnionType>

///// Map from the constructor names to the variant and type
//type TypeVariantsInScope = Map<UpperNameValue, VariantCase * UnionType>

//type TypesAndVariantsInScope =
//    { types : TypesInScope
//      constructors : TypeVariantsInScope }


//module TypesAndVariantsInScope =

//    let getTypeFromScopes
//        (typeName : UpperNameValue)
//        (scopes : TypesAndVariantsInScope)
//        : Result<UnionType, AccTypeError> =
//        match Map.tryFind typeName scopes.types with
//        | Some union -> Ok union
//        | None -> Error (UnresolvedTypeName typeName)

//    let getVariantFromScopes
//        (ctorName : UpperNameValue)
//        (scopes : TypesAndVariantsInScope)
//        : Result<VariantCase * UnionType, AccTypeError> =
//        match Map.tryFind ctorName scopes.constructors with
//        | Some variantAndUnion -> Ok variantAndUnion
//        | None -> Error (UnresolvedCtorError ctorName)








//(*

//    Helpers for function types and record dotting

//*)


///// Pass in the IDs for the params and return type and this will return an Acc and AccId for the overall arrow type. If the NEL only has one item then it will just be a non-arrow value.
//let rec makeAccIdDestType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =
//    match rest with
//    | [] ->
//        // In other words, it's not actually a function, we just have a value
//        Aati.make first acc

//    | head :: tail ->
//        /// Get the type information from the return type, whether it's an arrow or not
//        let tailResult = makeAccIdDestType (NEL.new_ head tail) acc
//        let refDefType = RefDtArrow (first, tailResult.typeId)

//        // And insert the new arrow type into the Acc
//        Accumulator.addRefDefResOpt (Ok refDefType |> Some) tailResult.acc



///// Pass in the IDs for the params passed to a function and return the arrow type the function expression must be inferred to be
//let rec makeAccIdFuncApplicationType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =

//    let makeArrowType (aati : AccAndTypeId) : AccAndTypeId =
//        let refDefType = RefDtArrow (first, aati.typeId)
//        Accumulator.addRefDefResOpt (Some (Ok refDefType)) aati.acc

//    match rest with
//    | [] ->
//        let unspecific = Accumulator.addRefDefResOpt None acc
//        makeArrowType unspecific

//    | head :: tail ->
//        let tailResult = makeAccIdFuncApplicationType (NEL.new_ head tail) acc
//        makeArrowType tailResult




//let rec makeDottedSeqImpliedType (fields : RecordFieldName nel) acc =
//    let (NEL (first, rest)) = fields

//    let makeDotRecord fieldName (aati : AccAndTypeId) =
//        let refDefType = RefDtRecordWith ([ fieldName, aati.typeId ] |> Map.ofSeq)
//        Accumulator.addRefDefResOpt (Some (Ok refDefType)) aati.acc

//    match rest with
//    | [] ->
//        let unspecific = Accumulator.addRefDefResOpt None acc
//        makeDotRecord first unspecific

//    | head :: tail ->
//        let tailResult = makeDottedSeqImpliedType (NEL.new_ head tail) acc
//        makeDotRecord first tailResult








///// Get type information based on a single assignment pattern – named values, destructurings, and so on.
///// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
//let getAccumulatorFromParam (typeScope : TypesAndVariantsInScope) (param : AssignmentPattern) : AccAndTypeId =
//    let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : AccAndTypeId =
//        match pattern with
//        | Named ident -> Acc.addRefDefResOptWithRefConstrs None (Set.singleton (ByValue (LocalLower ident))) Acc.empty

//        | Ignored -> Acc.addRefDefResOpt None Acc.empty

//        | Unit -> Acc.addRefDefResOpt (Some (Ok RefDtUnitType)) Acc.empty

//        | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured

//        | Aliased (pattern_, alias) ->
//            let nestedAccAndType = getInferredTypeFromAssignmentPattern pattern_

//            let withNameAdded =
//                Acc.addRefDefResOptWithRefConstrs None (Set.singleton (ByValue (LocalLower alias))) nestedAccAndType.acc

//            Acc.unifyTwoAccTypeIds nestedAccAndType.typeId withNameAdded.typeId withNameAdded.acc


//    and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : AccAndTypeId =
//        match pattern with
//        | DestructuredRecord fieldNames ->
//            let fields =
//                fieldNames
//                |> NEL.map (fun recFieldName ->
//                    recFieldName,
//                    Acc.addRefDefResOptWithRefConstrs
//                        None
//                        (Set.singleton (ByValue (LocalLower (recFieldToLowerIdent recFieldName))))
//                        Acc.empty)
//                |> Map.ofSeq

//            let combinedAcc =
//                fields
//                |> Map.fold (fun state _ v -> Acc.combine v.acc state) Acc.empty

//            let refDefType =
//                fields
//                |> Map.map (fun _ v -> v.typeId)
//                |> RefDtRecordWith

//            Acc.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


//        | DestructuredCons consItems ->
//            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern consItems
//            let combinedAcc = Acc.combineAccsFromAatis gatheredItems

//            let unified =
//                combinedAcc
//                |> Acc.unifyManyTypeConstraintIds (TOM.map Aati.getId gatheredItems)

//            let refDefType = RefDtList unified.typeId
//            Acc.addRefDefResOpt (Some (Ok refDefType)) unified.acc


//        | DestructuredTuple tupleItems ->
//            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern tupleItems

//            let combinedAcc = Acc.combineAccsFromAatis gatheredItems

//            let refDefType = RefDtTuple (TOM.map Aati.getId gatheredItems)
//            Acc.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


//        | DestructuredTypeVariant (ctorName, params_) ->
//            let gatheredParams = List.map getInferredTypeFromAssignmentPattern params_
//            let combinedAcc = Acc.combineAccsFromAatis gatheredParams

//            let ctorResult = TypesAndVariantsInScope.getVariantFromScopes ctorName typeScope

//            match ctorResult with
//            | Ok (variant, union) ->

//                match List.map Aati.getId gatheredParams with
//                | [] ->
//                    let newTypeRefDef = RefDtNewType (union, Map.empty)

//                    // I.e. there are no params to add for this variant's constructor
//                    Acc.addRefDefResOptWithRefConstrs (Some (Ok newTypeRefDef)) Set.empty combinedAcc

//                | head :: tail ->
//                    // I.e. there are params


//                    /// Match up the TCIs with the ATIs and return the remaining ones if one of them is longer than the other
//                    let rec matchUpTciWithAtis
//                        (combinedSoFar : (TypeConstraintId * AccumulatorTypeId) list)
//                        (tcis : TypeConstraintId list)
//                        (atis : AccumulatorTypeId list)
//                        =
//                        match tcis, atis with
//                        | [], [] -> combinedSoFar, None
//                        | h :: t, [] -> combinedSoFar, Some (Left (h :: t))
//                        | [], h :: t -> combinedSoFar, Some (Right (h :: t))
//                        | l :: tl, r :: tr -> matchUpTciWithAtis ((l, r) :: combinedSoFar) tl tr

//                    let matchedUp, remaining =
//                        matchUpTciWithAtis List.empty variant.contents (head :: tail)

//                    match remaining with
//                    | None ->
//                        let matchMap = Map.ofList matchedUp

//                        let newTypeRefDef = RefDtNewType (matchMap, union)

//                        Acc.addRefDefResOptWithRefConstrs (Some (Ok newTypeRefDef)) Set.empty combinedAcc

//                    | Some remaining_ ->
//                        let paramLenDiff =
//                            match remaining_ with
//                            | Left tcis -> List.length tcis
//                            | Right atis -> -(List.length atis)

//                        Acc.addRefDefResOptWithRefConstrs
//                            (Some (Error (WrongPatternParamLength paramLenDiff)))
//                            Set.empty
//                            combinedAcc

//            // @TODO: Technically we should be able to type check those constructor params that do match up and separately report an error about the incorrect number of pattern matched params, but that'll have to wait for when we're able to both return a type here and separately return an error also


//            ///// @TODO: I'm not 100% sure that this is the best way to do this, or if there is actually a more consistent way to specify what the relationship of the constructor to the params should be.
//            ///// E.g. one thing which `makeAccIdFuncApplicationType` does *not* capture is the fact that these are not just *some* parameters, but they need to be *all* of the parameters for that type variant. Otherwise should be a type error.
//            //let withFuncRequirement =
//            //    makeAccIdFuncApplicationType (NEL.new_ head tail) combinedAcc

//            //Acc.combine combinedAcc withFuncRequirement.acc
//            //|> Acc.addRefDefResOptWithRefConstrs None (Set.singleton ctorType)

//            | Error e -> Acc.addError e combinedAcc


//    getInferredTypeFromAssignmentPattern param








///// This should: from a binding, derive the type + all the names declared/destructured along with their types in the Accumulator - for use in the let expression body (and of course not outside of it)
//let private getAccumulatorFromBinding (typeScope : TypesAndVariantsInScope) (binding : LetBinding) : AccAndTypeId =
//    getAccumulatorFromParam typeScope binding.paramPattern














//(*
//    Get Accumulator and type from expressions
//*)

///// Return the Accumulator of constrained values along with the type ID of the expression in its entirety
//let rec getAccumulatorFromExpr (typeScope : TypesAndVariantsInScope) (expr : T.Expression) : AccAndTypeId =

//    let recursiveGetAccFromExpr = getAccumulatorFromExpr typeScope

//    let makeOkType = Ok >> Some
//    let getParamFromPattern (pattern : FunctionOrCaseMatchParam) = pattern.paramPattern

//    match expr with
//    | T.SingleValueExpression singleVal ->
//        match singleVal with
//        | T.ExplicitValue explicit ->
//            match explicit with
//            | Primitive primitive ->
//                let refDefType = refDeftypeOfPrimitiveLiteral primitive
//                Accumulator.addRefDefResOpt (makeOkType refDefType) Accumulator.empty


//            | T.DotGetter dotGetter ->

//                //let fields = Map.ofList [ dotGetter, TC.any () ]
//                //let defType = DtArrow (DtRecordWith fields |> TC.fromDef, TC.any ())

//                //Accumulator.convertDefinitiveType defType


//            | T.Compound compound ->
//                match compound with
//                | T.CompoundValues.List list ->
//                    let typedList = List.map recursiveGetAccFromExpr list

//                    let combinedAcc = typedList |> Accumulator.combineAccsFromAatis

//                    let combinedAati =
//                        Accumulator.unifyManyTypeConstraintIds (List.map Aati.getId typedList) combinedAcc

//                    let refDefType = RefDtList combinedAati.typeId
//                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAati.acc



//                | T.CompoundValues.Tuple tuple ->
//                    let typedTom = TOM.map recursiveGetAccFromExpr tuple

//                    let combinedAcc = typedTom |> Accumulator.combineAccsFromAatis

//                    let refDefType = RefDtTuple (TOM.map Aati.getId typedTom)
//                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAcc


//                | T.CompoundValues.Record record ->
//                    let typedKeyVals =
//                        record
//                        |> List.map (fun (key, value) -> key, recursiveGetAccFromExpr value)

//                    let combinedAcc =
//                        typedKeyVals
//                        |> List.map (snd >> Aati.getAcc)
//                        |> Accumulator.combineMany

//                    let refDefType =
//                        typedKeyVals
//                        |> List.map (fun (key, aati) -> key, aati.typeId)
//                        |> Map.ofList
//                        |> RefDtRecordExact

//                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAcc


//                | T.CompoundValues.RecordExtension (extended, additions) ->
//                    let typedKeyVals =
//                        additions
//                        |> NEL.map (fun (key, value) -> key, recursiveGetAccFromExpr value)

//                    let combinedAcc =
//                        typedKeyVals
//                        |> NEL.map (snd >> Aati.getAcc)
//                        |> Accumulator.combineMany

//                    let refDefType =
//                        typedKeyVals
//                        |> NEL.map (fun (key, aati) -> key, aati.typeId)
//                        |> Map.ofSeq
//                        |> RefDtRecordWith


//                    Accumulator.addRefDefResOptWithRefConstrs
//                        (makeOkType refDefType)
//                        (LocalLower extended |> ByValue |> Set.singleton)
//                        combinedAcc




//            | T.Function funcVal ->
//                let typeOfBody : AccAndTypeId = recursiveGetAccFromExpr funcVal.body

//                let funcParamsAccumulatorsAndSelfTypes =
//                    NEL.map
//                        (getParamFromPattern
//                         >> getAccumulatorFromParam typeScope)
//                        funcVal.params_

//                let funcParamsAccumulators =
//                    funcParamsAccumulatorsAndSelfTypes
//                    |> NEL.map Aati.getAcc


//                let funcParamTypes =
//                    funcParamsAccumulatorsAndSelfTypes
//                    |> NEL.map Aati.getId

//                /// Acc that combines the gleaned information about params from their shape and also from the body of the function
//                let combinedAcc =
//                    funcParamsAccumulators
//                    |> Seq.fold Accumulator.combine typeOfBody.acc


//                let paramsAndReturnTypeNel = NEL.appendList funcParamTypes [ typeOfBody.typeId ]
//                let funcAati = makeAccIdDestType paramsAndReturnTypeNel combinedAcc

//                /// This contains all the names defined from each param
//                let combinedNamesDefinedHere =
//                    funcParamsAccumulators
//                    |> NEL.map getLocalValueNames
//                    |> NEL.fold Set.union Set.empty

//                let guidMap = makeGuidMapForNames combinedNamesDefinedHere

//                replaceNameRefsWithBoundVars guidMap funcAati.acc
//                |> Aati.make funcAati.typeId



//        | T.UpperIdentifier name ->
//            match TypesAndVariantsInScope.getVariantFromScopes name typeScope with
//            | Ok (variant, union) ->
//                let params_ =
//                    variant.contents
//                    |> List.map (fun tcId -> tcId, Acc.addRefDefResOpt None Acc.empty)

//                let combinedAcc =
//                    params_
//                    |> List.map snd
//                    |> Acc.combineAccsFromAatis

//                let tcMap =
//                    params_
//                    |> List.map (fun (tcId, aati) -> tcId, aati.typeId)
//                    |> Map.ofSeq

//                let refDefNewType = RefDtNewType (tcMap, union)

//                Acc.addRefDef refDefNewType combinedAcc

//            | Error e -> Acc.addError e Acc.empty



//        | T.LowerIdentifier name -> Accumulator.addSingleRefConstr (ByValue name) Accumulator.empty





//        | T.LetExpression (declarations, expr') ->
//            let bodyExpr = recursiveGetAccFromExpr expr'

//            let typedDeclarations =
//                declarations
//                |> NEL.map (fun binding ->
//                    let bindingAccAndSelf = getAccumulatorFromParam typeScope binding.paramPattern
//                    let assignedExprAccAndSelf = recursiveGetAccFromExpr binding.assignedExpression

//                    let combinedAcc =
//                        Accumulator.combineAccsFromAatis [ bindingAccAndSelf
//                                                           assignedExprAccAndSelf ]

//                    Accumulator.unifyTwoAccTypeIds bindingAccAndSelf.typeId assignedExprAccAndSelf.typeId combinedAcc)


//            let combinedAcc =
//                Accumulator.combineAccsFromAatis typedDeclarations
//                |> Acc.combine bodyExpr.acc

//            /// This contains all the names defined from each param
//            let combinedNamesDefinedHere = getLocalValueNames combinedAcc
//            let guidMap = makeGuidMapForNames combinedNamesDefinedHere


//            replaceNameRefsWithBoundVars guidMap combinedAcc
//            |> Aati.make bodyExpr.typeId



//        | T.ControlFlowExpression controlFlow ->
//            match controlFlow with
//            | T.IfExpression (cond, ifTrue, ifFalse) ->
//                let condAccAndOwn = recursiveGetAccFromExpr cond

//                let boolRefDef = RefDtPrimType BuiltInPrimitiveTypes.Bool

//                let withBoolConstrAdded =
//                    Accumulator.addRefDefConstraintForAccId
//                        (makeOkType boolRefDef)
//                        condAccAndOwn.typeId
//                        condAccAndOwn.acc

//                let ifTrueAccAndOwn = recursiveGetAccFromExpr ifTrue
//                let ifFalseAccAndOwn = recursiveGetAccFromExpr ifFalse

//                let combinedAcc =
//                    Accumulator.combineMany [ withBoolConstrAdded.acc
//                                              ifTrueAccAndOwn.acc
//                                              ifFalseAccAndOwn.acc ]

//                Accumulator.unifyTwoAccTypeIds ifTrueAccAndOwn.typeId ifFalseAccAndOwn.typeId combinedAcc



//            | T.CaseMatch (exprToMatch, branches) ->
//                let matchExprAccAndSelf = recursiveGetAccFromExpr exprToMatch

//                let accsAndSelvesOfPatterns =
//                    branches
//                    |> NEL.map (fun branch ->
//                        let matchPatternAccAndSelf =
//                            getAccumulatorFromParam typeScope (getParamFromPattern branch.matchPattern)

//                        let combinedNamesDefinedHere = getLocalValueNames matchPatternAccAndSelf.acc
//                        let guidMap = makeGuidMapForNames combinedNamesDefinedHere

//                        let branchBodyExpr = recursiveGetAccFromExpr branch.body

//                        {| patternAccAndId =
//                            replaceNameRefsWithBoundVars guidMap matchPatternAccAndSelf.acc
//                            |> Aati.make matchPatternAccAndSelf.typeId
//                           bodyAccAndId =
//                            replaceNameRefsWithBoundVars guidMap branchBodyExpr.acc
//                            |> Aati.make branchBodyExpr.typeId |})


//                let combinedAcc =
//                    accsAndSelvesOfPatterns
//                    |> NEL.map (fun pattern -> Accumulator.combine pattern.patternAccAndId.acc pattern.bodyAccAndId.acc)
//                    |> Accumulator.combineMany
//                    |> Accumulator.combine matchExprAccAndSelf.acc

//                let withMatchExprAndPatternsCombined =
//                    combinedAcc
//                    |> Accumulator.unifyManyTypeConstraintIds (
//                        accsAndSelvesOfPatterns
//                        |> NEL.map (fun pattern -> pattern.patternAccAndId.typeId)
//                        |> Set.ofSeq
//                        |> Set.add matchExprAccAndSelf.typeId
//                    )

//                let withReturnTypesCombined =
//                    withMatchExprAndPatternsCombined.acc
//                    |> Accumulator.unifyManyTypeConstraintIds (
//                        accsAndSelvesOfPatterns
//                        |> NEL.map (fun pattern -> pattern.bodyAccAndId.typeId)
//                        |> Set.ofSeq
//                    )

//                withReturnTypesCombined




//    | T.CompoundExpression compExpr ->
//        match compExpr with
//        | T.FunctionApplication (funcExpr, params_) ->
//            let paramsAccAndSelves = params_ |> NEL.map recursiveGetAccFromExpr

//            let paramsAcc =
//                paramsAccAndSelves
//                |> Accumulator.combineAccsFromAatis

//            /// The Acc based on the parameters and the type that the function must be compatible with based on the parameters that have been applied to the function
//            let requiredFuncAccAndId =
//                makeAccIdFuncApplicationType (NEL.map Aati.getId paramsAccAndSelves) paramsAcc

//            let funcExprAccAndSelf = recursiveGetAccFromExpr funcExpr

//            let combinedAcc =
//                Accumulator.combine requiredFuncAccAndId.acc funcExprAccAndSelf.acc

//            combinedAcc
//            // @TODO: no no no no no, this is wrong. The applied parameters don't need to impose constraints on the function expression; they just need to not clash with them! In other words, we want to maintain let polymorphism!
//            // So how to do this... hmmm. Well I think instead of just unifying the thing back to the function expression, we want to... just ensure there is no clash? Hm not sure exactly how to approach this.
//            |> Accumulator.unifyTwoAccTypeIds funcExprAccAndSelf.typeId requiredFuncAccAndId.typeId


//        | T.DotAccess (dottedExpr, dotSequence) ->
//            let exprAccAndSelf = recursiveGetAccFromExpr dottedExpr

//            let withImpliedRecordType = makeDottedSeqImpliedType dotSequence exprAccAndSelf.acc

//            Accumulator.unifyTwoAccTypeIds exprAccAndSelf.typeId withImpliedRecordType.typeId withImpliedRecordType.acc


//        | T.Operator (left, op, right) ->
//            // @TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes
//            failwith
//                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"
















///// Just a container to ferry the type and declarations to the TST module type
//type private TypeAndDeclarations =
//    { name : UpperIdent
//      declaration : T.TypeDeclaration
//      ctors : T.VariantConstructor list }







///// Get the mentioned type parameters from a type expression
//let rec private getTypeParams (mentionableType : T.MentionableType) : TypeConstraintId set =
//    match mentionableType with
//    | MentionableType.GenericTypeVar name -> Set.singleton name
//    | MentionableType.UnitType -> Set.empty
//    | MentionableType.Tuple mentionables -> Set.collect getTypeParams mentionables

//    | MentionableType.Record fields
//    | MentionableType.ExtendedRecord fields ->
//        Map.toSeq fields
//        |> Set.collect (snd >> getTypeParams)

//    | MentionableType.ReferencedType (_, typeParams) -> Set.collect getTypeParams typeParams
//    | MentionableType.Arrow (fromType, toType) -> Set.union (getTypeParams fromType) (getTypeParams toType)






//let private getTypeAndDeclaration
//    (typeName : S.CstNode<UnqualTypeOrModuleIdentifier>)
//    (decl : Cst.TypeDeclaration)
//    : TypeAndDeclarations =
//    match decl with
//    | S.Alias aliasDecl ->
//        let typeParamsList =
//            aliasDecl.typeParams
//            |> List.map (S.getNode >> unqualValToLowerIdent)

//        let typeDeclaration : T.TypeDeclarationContent =
//            mentionableTypeToDefinite aliasDecl.referent.node
//            |> T.Alias

//        let typeDecl : T.TypeDeclaration =
//            { typeParamsMap =
//                typeParamsList
//                |> List.map (fun typeParam -> typeParam, ())
//                |> SOD.makeMapFromList
//              typeParamsList = typeParamsList
//              typeDeclaration = typeDeclaration }

//        let typeIdent = unqualTypeToUpperIdent typeName.node

//        { name = typeIdent
//          declaration = typeDecl
//          ctors = List.empty }

//    | S.Sum sumDecl ->
//        let typeParamsList =
//            sumDecl.typeParams
//            |> List.map (S.getNode >> unqualValToLowerIdent)

//        let typeParamsMap =
//            typeParamsList
//            |> List.map (fun typeParam -> typeParam, ())
//            |> SOD.makeMapFromList

//        let variantCases =
//            sumDecl.variants
//            |> NEL.map (fun variantCase ->
//                let contents =
//                    variantCase.node.contents
//                    |> List.map (S.getNode >> mentionableTypeToDefinite)

//                { label = unqualTypeToUpperIdent variantCase.node.label.node
//                  contents = contents })

//        let typeDeclaration = T.Sum variantCases

//        let typeIdent = unqualTypeToUpperIdent typeName.node

//        let variantConstructors : T.VariantConstructor nel =
//            variantCases
//            |> NEL.map (fun variantCase ->
//                { typeParamsList = typeParamsList
//                  typeParamsMap = typeParamsMap
//                  variantCase = variantCase
//                  allVariants = variantCases
//                  typeName = typeIdent })


//        let typeDecl : T.TypeDeclaration =
//            { typeParamsMap = typeParamsMap
//              typeParamsList = typeParamsList
//              typeDeclaration = typeDeclaration }

//        { name = typeIdent
//          declaration = typeDecl
//          ctors = NEL.toList variantConstructors }



///// @TODO: hm not sure this makes sense anymore if we don't store the type of the expressions inside the record itself but it's computed by a function
//let typeCheckModule (ylModule : Cst.YlModule) : T.YlModule =
//    /// @TODO: Hmm looks we don't really do anything with the type constructors yet. Need to make sure we're using them to resolve any referenced constructors in the values.
//    let typesAndConstructors =
//        ylModule.declarations
//        |> List.choose (
//            S.getNode
//            >> function
//                | S.TypeDeclaration (typeName, decl) -> getTypeAndDeclaration typeName decl |> Some
//                | _ -> None
//        )

//    let typesNames =
//        typesAndConstructors
//        |> List.map (fun typeAndCtor -> typeAndCtor.name, typeAndCtor.declaration)
//        |> SOD.makeMapFromList

//    let infixOps =
//        ylModule.declarations
//        |> List.choose (
//            S.getNode
//            >> function
//                | S.InfixOperatorDeclaration infixOp ->
//                    Some (
//                        unqualValToLowerIdent infixOp.name,
//                        { associativity = infixOp.associativity
//                          precedence = infixOp.precedence
//                          value = convertCstToAst List.empty infixOp.value.node }
//                    )
//                | _ -> None
//        )
//        |> SOD.makeMapFromList


//    let imports =
//        ylModule.declarations
//        |> List.choose (
//            S.getNode
//            >> function
//                | S.ImportDeclaration import -> Some import
//                | _ -> None
//        )

//    let values =
//        ylModule.declarations
//        |> List.choose (
//            S.getNode
//            >> function
//                | S.ValueDeclaration valDecl ->
//                    let ident = unqualValToLowerIdent valDecl.valueName.node

//                    Some (
//                        ident,
//                        // @TODO: make sure we're actually passing in the names required for resolution here
//                        convertCstToAst [ ident ] valDecl.value.node
//                    )
//                | _ -> None
//        )
//        |> SOD.makeMapFromList

//    let valueTypes : T.ValueTypeDeclarations =
//        ylModule.declarations
//        |> List.choose (
//            S.getNode
//            >> function
//                | S.ValueTypeAnnotation annotation ->
//                    let ident = unqualValToLowerIdent annotation.valueName.node

//                    Some (LocalLower ident, mentionableTypeToDefinite annotation.annotatedType.node)
//                | _ -> None
//        )
//        |> SOD.makeMapFromList


//    { moduleDecl = ylModule.moduleDecl
//      imports = imports
//      types = typesNames
//      values = values
//      valueTypes = valueTypes
//      infixOperators = infixOps }
