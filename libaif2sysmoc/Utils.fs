
//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//

namespace Averest.Synthesis.SysMoc

open Averest.Core
open Averest.Core.AIFIO
open Averest.Core.Properties
open Averest.Core.Names
open Averest.Core.Declarations
open System.Collections.Generic
open Averest.Core.Actions
open Averest.Core.Expressions

module Utils =

    // AIF component is the input object used to construct an instance of Efsm.
    type AIFComponent = {
        name: Averest.Core.Names.Index;
        iface: Averest.Core.Declarations.Interface;
        locals: Averest.Core.Declarations.Interface;
        ctrlFlow: GrdAction list;
        dataFlow: GrdAction list;
        abbrevs: GrdAction list}
    
    // Returns AIFComponent elements of an AIF system, which can be used as an input to construct an Efsm object instance.
    let AIFComponentOfAIFSystem (aifsys: Averest.Core.AIF.AIFSystem) =
        let result = {
            AIFComponent.name = aifsys.name;
            AIFComponent.iface = aifsys.iface;
            AIFComponent.locals = aifsys.locals;
            AIFComponent.ctrlFlow = aifsys.ctrlFlow;
            AIFComponent.dataFlow = aifsys.dataFlow;
            AIFComponent.abbrevs = aifsys.abbrevs}
        (result)

    // Adapts an AIF system driver to be an AIFComponent suitable for input to an actor network topology
    //   input ports are rewritten to be output ports.
    let AIFComponentOfAIFSystemDriver (iface:Declarations.Interface,aifsys: Averest.Core.AIF.SystemPart) =
        let rewrittenOutputs:Declarations.Interface = 
                    iface|> List.filter (fun (x,y) -> y.flow = Averest.Core.Declarations.Flow.Input) 
                         |> List.map(fun (qname, decl) -> 
                                        let ndecl = {flow = Declarations.Output;storage= decl.storage;qtype=decl.qtype}
                                        (qname,ndecl))      
        let result = {
            AIFComponent.name = aifsys.name;
            AIFComponent.iface = rewrittenOutputs;
            AIFComponent.locals = aifsys.locals;
            AIFComponent.ctrlFlow = aifsys.ctrlFlow;
            AIFComponent.dataFlow = aifsys.dataFlow;
            AIFComponent.abbrevs = aifsys.abbrevs}
        (result)

    let isAssignmentAction(inaction:Action) =        
        match inaction with
        | AssignNow (_) | AssignNxt(_) -> true
        | _ -> false

    // Returns true if given action is an immediate action
    let isAssignNowAction (inaction:Action) =
        match inaction with
        | AssignNow (_)-> true
        | _ -> false

    // Returns true if the action of given guarded action is a an immediate action
    let isAssignNowGAction (grdaction:GrdAction) = 
        isAssignNowAction (snd(grdaction))
    
    // Returns true if given action is a delayed action
    let isAssignNextAction (inaction:Action) =
        match inaction with
        | AssignNxt (_)-> true
        | _ -> false
 
    // Bounds of numerical types are represented as boolean list. This function
    // converts them back to an integer.
    let ConvertBoolListToNat(blist: bool list) =
        let result:uint32 ref = ref(0u)
        blist
            |> List.iter(fun (bit) -> 
                let value = (if bit then 1u else 0u)
                result := ((!result <<< 1) ||| value) )

        (!result)

    // Bounds of numerical types are represented as boolean list. This function
    // converts them back to a Long.
    let ConvertBoolListToLong(blist: bool list) =
        let result:uint64 ref= ref(0UL)
        blist
            |> List.iter(fun (bit) -> 
                let value = (if bit then 1UL else 0UL)
                result := ((!result <<< 1) ||| value) )

        (!result)
  
  
    // Bounds of numerical types are represented as boolean list. This function
    // converts them back to an integer.
    let ConvertBoolListToInt(blist: bool list) =
        let result = ref(0)
        blist
            |> List.iter(fun (bit) -> 
                let value = (if bit then 1 else 0)
                result := ((!result <<< 1) ||| value) )

        (!result)



    // Returns true if the action of given guarded action is a delayed action
    let isAssignNextGAction (grdaction:GrdAction) = 
        isAssignNextAction (snd(grdaction))

    // Returns the left hand side Qname of a given action
    let LhsQnameofAction (inaction:Action) =
        match inaction with
        | AssignNow(lhs,_,_) |AssignNxt (lhs,_,_) -> 
            match lhs with
            | Expressions.LhsVar (qname,_) ->  (qname, None)
            | Expressions.LhsArrAcc (lhsexpr, natexpr) ->
                match lhsexpr with
                | Expressions.LhsVar (qname,_) -> 
                    match natexpr with
                    | NatConst (boollist) ->
                        (qname, Some(ConvertBoolListToInt(boollist)))                                    
                    | (other) -> (qname, Some 0)
                | (other) -> failwith "LhsQnameofAction: compound types are not supported in arrays"
            | Expressions.LhsTupAcc (lhsexpr,index) -> 
                match lhsexpr with
                | Expressions.LhsVar (qname,_) ->  (qname, Some index)
                | (other) -> failwith "LhsQnameofAction: compound types are not supported in tuples"
        | _ -> failwith "LhsQnameofAction: action is not assignment"

    // Returns the left hand side (Qname,Qtype) of a given action
    let LhsVarofAction (inaction:Action) =
        match inaction with
        | AssignNow(lhs,_,_) |AssignNxt (lhs,_,_) -> 
            match lhs with
            | Expressions.LhsVar (qname, qtype) -> Some (qname, qtype)
            | _ -> None 
        | _ -> None
    
    // Returns the right hand side expression of a given action
    let RhsExpressionOfAction (inaction:Action) =
        match inaction with
        | AssignNow(_,_,expr) |AssignNxt (_,_,expr) -> 
            Some expr
        | _ -> None
        
    let  RemoveRedundantBoolTerms (boolexp:Expressions.BoolExpr) = 

        // finds all disjuncted terms, i.e flattens the disjunction hierarchy
        let rec FindInnerDisjuntions (boolexp:Expressions.BoolExpr) =

            match boolexp with
            | (BoolDisj (exp1, exp2)) -> List.append (FindInnerDisjuntions exp1) (FindInnerDisjuntions exp2)
            | (exp) -> [exp]
        
        // finds all conjunction terms, i.e flattens the conjuntion hierarchy
        let rec FindInnerConjunctions (boolexp:Expressions.BoolExpr) =

            match boolexp with
            | (BoolConj (exp1, exp2)) -> List.append (FindInnerConjunctions exp1) (FindInnerConjunctions exp2)
            | (exp) -> [exp]
        
        // Builds a disjunction of a list of boolean expressions
        let rec BuildDisjunctionOfList (boolexplist:Expressions.BoolExpr list) =
            match boolexplist with
            |head::tail ->  if (tail.IsEmpty) then RemoveRedundantTerms(head) else BoolDisj (RemoveRedundantTerms(head), BuildDisjunctionOfList(tail))
            |[] -> BoolConst false
        
        // Builds a conjunction of a list of boolean expressions
        and BuildConjunctionOfList (boolexplist:Expressions.BoolExpr list) =
            match boolexplist with
            |head::tail  -> if (tail.IsEmpty) then RemoveRedundantTerms(head) else BoolConj (RemoveRedundantTerms(head), BuildConjunctionOfList(tail))
            |[] -> BoolConst true
       
        // Removes terms that are redundant in a boolean expression and replaces them with 
        //   single occurance of the term , e.g. term "x" in x&y&z&x is replaced, so the result is x&y&z
        and RemoveRedundantTerms (boolexp:Expressions.BoolExpr) = 
            match boolexp with
            | (BoolDisj (_)) -> 
                    let reducedTerms = Set.toList((Set.ofList(FindInnerDisjuntions(boolexp))).Remove(BoolConst false))
                    BuildDisjunctionOfList(reducedTerms|>List.sort)

            | (BoolConj (_)) ->
                    let reducedTerms = Set.toList((Set.ofList(FindInnerConjunctions(boolexp))).Remove(BoolConst true))
                    BuildConjunctionOfList(reducedTerms|>List.sort)
            | (BoolNeg (BoolNeg exp)) -> RemoveRedundantTerms(exp)
            | (exp) -> exp

        RemoveRedundantTerms(boolexp)

    let atomIndex = ref (1000)

    let rec GetBoolVarsAndAtoms (boolexp:Expressions.BoolExpr) = 

        match boolexp with
        | BoolVar (qname) -> 
            ([qname], [])

        | BoolConst (value) ->
            ([], [])
                                
        | BoolNeg (expr) ->
            GetBoolVarsAndAtoms(expr)
      
        | BoolConj (expr1, expr2)  | BoolDisj (expr1, expr2)  | BoolImpl (expr1, expr2) 
        | BoolEqu  (expr1, expr2) ->

            let ( qlist1, atomlist1) = GetBoolVarsAndAtoms(expr1)
            let ( qlist2, atomlist2) = GetBoolVarsAndAtoms(expr2)
            ((List.append qlist1 qlist2), (List.append atomlist1 atomlist2))

        | (expr) -> 

            ([], [expr])



    let rec BoolExpRewriteAtomWithQName (boolexp:Expressions.BoolExpr, atomRewrite:Map<Expressions.BoolExpr, Names.QName>) = 

        match boolexp with
        | BoolVar (qname) -> 
                (BoolVar (qname))
                                
        | BoolNeg (expr) ->
            (BoolNeg (BoolExpRewriteAtomWithQName(expr, atomRewrite)))

        | BoolConj (expr1, expr2) -> 
            (BoolConj (BoolExpRewriteAtomWithQName(expr1, atomRewrite), BoolExpRewriteAtomWithQName(expr2, atomRewrite))) 

        | BoolDisj (expr1, expr2) ->
            (BoolDisj (BoolExpRewriteAtomWithQName(expr1, atomRewrite), BoolExpRewriteAtomWithQName(expr2, atomRewrite))) 

        | BoolImpl (expr1, expr2) ->
            (BoolImpl (BoolExpRewriteAtomWithQName(expr1, atomRewrite), BoolExpRewriteAtomWithQName(expr2, atomRewrite))) 

        | BoolEqu (expr1, expr2) ->
            (BoolEqu (BoolExpRewriteAtomWithQName(expr1, atomRewrite), BoolExpRewriteAtomWithQName(expr2, atomRewrite))) 

        | (expr) -> 
            if (atomRewrite.ContainsKey(expr)) then
                (BoolVar (atomRewrite.Item (expr)))
            else
                expr
            
    let rec BoolExpRewriteQnameWithAtom (boolexp:Expressions.BoolExpr, qnameRewrite: Map<Names.QName, Expressions.BoolExpr> ) = 

        match boolexp with
        | BoolVar (qname) -> 
            if (qnameRewrite.ContainsKey(qname)) then
                (qnameRewrite.Item qname)
            else 
                (BoolVar qname)    
                                
        | BoolNeg (expr) ->
            BoolNeg (BoolExpRewriteQnameWithAtom(expr, qnameRewrite))

        | BoolConj (expr1, expr2) -> 
            BoolConj (BoolExpRewriteQnameWithAtom(expr1, qnameRewrite), BoolExpRewriteQnameWithAtom(expr2, qnameRewrite))

        | BoolDisj (expr1, expr2) ->
            BoolDisj (BoolExpRewriteQnameWithAtom(expr1, qnameRewrite), BoolExpRewriteQnameWithAtom(expr2, qnameRewrite))

        | BoolImpl (expr1, expr2) ->
            BoolImpl (BoolExpRewriteQnameWithAtom(expr1, qnameRewrite), BoolExpRewriteQnameWithAtom(expr2, qnameRewrite))

        | BoolEqu (expr1, expr2) ->
            BoolEqu (BoolExpRewriteQnameWithAtom(expr1, qnameRewrite), BoolExpRewriteQnameWithAtom(expr2, qnameRewrite))

        | (expr) -> expr
        
    let BoolExpGetBoolVarsAndRewriteAtoms (boolexp:Expressions.BoolExpr) =

        let (qnameList, atomList) = GetBoolVarsAndAtoms(boolexp)
        let uniqueQnames = Set.toList(Set.ofList(qnameList))

        if not(atomList.IsEmpty) then
            let uniqueAtoms = Set.toList(Set.ofList(atomList))
            let qnameAtomList = uniqueAtoms|> List.map( fun (atom) -> (Names.NewLocalName(), atom))
            let qnameMap = Map.ofList(qnameAtomList)
            let atomMap = Map.ofList(qnameAtomList|>List.map(fun (qname, atom) -> (atom, qname)))
            
            let rewrittenBoolExp = BoolExpRewriteAtomWithQName(boolexp, atomMap)

            let joinedQnames = List.append uniqueQnames (qnameAtomList|>List.map (fun (qname, atom) -> qname))

            (rewrittenBoolExp, joinedQnames|> List.sort, qnameMap)

        else
            (boolexp, uniqueQnames|>List.sort, Map.ofList([]))


    let rec SimplifyBoolExpression(boolexp: Expressions.BoolExpr, valueRewrite : Map<Names.QName, bool>) =
        match boolexp with
        | BoolVar (qname) -> 
            if (valueRewrite.ContainsKey(qname)) then
                (BoolConst (valueRewrite.Item qname), Set.ofList([]))
            else 
                (BoolVar (qname), Set.ofList([qname]))    
                                
        | BoolConst (boolconst) -> (BoolConst (boolconst), Set.ofList([]) )
        | BoolNeg (expr) ->
            let (result, varlist) = SimplifyBoolExpression(expr, valueRewrite)
            match result with
            | BoolConst(value) -> (BoolConst(not(value)), varlist)
            | BoolNeg (bexpr) -> (bexpr, varlist)
            | (other) -> (BoolNeg(other), varlist)

        | BoolConj (expr1, expr2) ->
            let (result1, varlist1) = SimplifyBoolExpression(expr1, valueRewrite)
            let (result2, varlist2) = SimplifyBoolExpression(expr2, valueRewrite)
            match (result1, result2) with
            | (BoolConst false, bexpr) -> (BoolConst false, Set.ofList([]))
            | (bexpr, BoolConst false) -> (BoolConst false, Set.ofList([]))
            | (BoolConst true, bexpr) -> (bexpr, varlist2)
            | (bexpr, BoolConst true) -> (bexpr, varlist1)
            | (bexpr1, bexpr2) ->
                if (bexpr1 = bexpr2) then
                    (bexpr1, varlist1)
                else
                    (BoolConj(bexpr1, bexpr2), Set.union varlist1 varlist2)

        | BoolDisj (expr1, expr2) ->
            let (result1, varlist1) = SimplifyBoolExpression(expr1,valueRewrite)
            let (result2, varlist2) = SimplifyBoolExpression(expr2,valueRewrite)
            match (result1, result2) with
            | (BoolConst true, bexpr) -> (BoolConst true, Set.ofList([]))
            | (bexpr, BoolConst true) -> (BoolConst true, Set.ofList([]))
            | (BoolConst false, bexpr) -> (bexpr, varlist2)
            | (bexpr, BoolConst false) -> (bexpr, varlist1)
            | (bexpr1, bexpr2) ->
                if (bexpr1 = bexpr2) then
                    (bexpr1, varlist1)
                else
                    (BoolDisj(bexpr1, bexpr2), Set.union varlist1 varlist2)

        | BoolImpl (expr1, expr2) ->            
            let translatedExpr = BoolDisj(BoolNeg(expr1), expr2)
            SimplifyBoolExpression (translatedExpr, valueRewrite)

        | BoolEqu (expr1, expr2) ->
            let (result1, _) = SimplifyBoolExpression(expr1,valueRewrite)
            let (result2, _) = SimplifyBoolExpression(expr2,valueRewrite)
            (BoolConst(result1=result2), Set.ofList([]))
        | (expr) ->
            (expr, Set.ofList([]))

    let  MakeCanonicalBoolExpr (boolexp:Expressions.BoolExpr) = 
        
        let rec Canonicalizer (depth:int, boolexp:Expressions.BoolExpr, knownVars:Map<QName,bool>, unknownvarList:(QName) list) =
            
            
            let currentPos = (unknownvarList.Head, true)
            let currentNeg = (unknownvarList.Head, false)

            let newKnownVarsPos = knownVars.Add(currentPos)
            let newKnownVarsNeg = knownVars.Add(currentNeg)
                
            let (exprPos, varlistPos) = SimplifyBoolExpression (boolexp, newKnownVarsPos)
            let (exprNeg, varlistNeg) = SimplifyBoolExpression (boolexp, newKnownVarsNeg )
    
            let qnameExp = BoolExpr.BoolVar (unknownvarList.Head)
            

            if unknownvarList.Tail.Length > 0 then
        
                match (exprPos, exprNeg) with
                | (BoolExpr.BoolConst false, BoolExpr.BoolConst false) -> 
                        BoolExpr.BoolConst false
                            
                | (BoolExpr.BoolConst true, BoolExpr.BoolConst true) -> 
                        BoolExpr.BoolConst true
                
                | ( BoolExpr.BoolConst true, BoolExpr.BoolConst false) ->
                        qnameExp                    

                | (BoolExpr.BoolConst false, BoolExpr.BoolConst true) -> 
                        BoolExpr.BoolNeg (qnameExp)
 
                | (BoolExpr.BoolConst true, resultexp ) ->
                   
//                        printfn "Canonicalizer depth %s option %s Var %s with expression %s " (depth.ToString()) ("1") (unknownvarList.Head.ToString()) (resultexp.ToString())
                        let result = Canonicalizer (depth + 1, resultexp, newKnownVarsNeg, Set.toList(varlistNeg)|>List.sort)
                        match result with 
                        | BoolConst (true) -> BoolConst (true)
                        | BoolConst (false) -> qnameExp
                        | (exp) -> BoolDisj  (qnameExp, exp)

                | (BoolExpr.BoolConst false, resultexp) -> 
//                        printfn "Canonicalizer depth %s option %s Var %s with expression %s " (depth.ToString()) ("2") (unknownvarList.Head.ToString()) (resultexp.ToString())
                        let result = Canonicalizer (depth + 1, resultexp, newKnownVarsNeg, Set.toList(varlistNeg)|>List.sort)
                        match result with 
                        | BoolConst (true) -> (BoolNeg qnameExp)
                        | BoolConst (false) ->(BoolConst (false))
                        | (exp) -> BoolConj ((BoolNeg qnameExp), exp)

                | (resultexp, BoolExpr.BoolConst false) ->
//                        printfn "Canonicalizer depth %s option %s Var %s with expression %s " (depth.ToString()) ("3") (unknownvarList.Head.ToString()) (resultexp.ToString())
                        let result = Canonicalizer (depth + 1, resultexp, newKnownVarsPos, Set.toList(varlistPos)|>List.sort)
                        match result with 
                        | BoolConst (true) -> qnameExp
                        | BoolConst (false) ->BoolConst (false)
                        | (exp) -> BoolConj ( qnameExp, exp)


                | (resultexp, BoolExpr.BoolConst true) -> 
//                        printfn "Canonicalizer depth %s option %s Var %s with expression %s " (depth.ToString()) ("4") (unknownvarList.Head.ToString()) (resultexp.ToString())
                        
                        let result = Canonicalizer (depth + 1, resultexp, newKnownVarsPos, Set.toList(varlistPos)|>List.sort)
                        match result with 
                        | BoolConst (true) -> BoolConst (true)
                        | BoolConst (false) -> BoolNeg qnameExp
                        | (exp) -> BoolDisj (BoolNeg qnameExp, exp)
                    
                | (resultexp1, resultexp2) -> 
//                        printfn "Canonicalizer depth %s option %s Var %s with two expressions %s $ %s" (depth.ToString()) ("5") (unknownvarList.Head.ToString()) (resultexp1.ToString()) (resultexp2.ToString())

                        let termPos = Canonicalizer (depth + 1, resultexp1, newKnownVarsPos, Set.toList(varlistPos)|>List.sort)
                        let termNeg = Canonicalizer (depth + 1, resultexp2, newKnownVarsNeg, Set.toList(varlistNeg)|>List.sort)
 
                        if termPos = termNeg then
                            termPos
                        else
                            BoolDisj (BoolConj (qnameExp, termPos) , BoolConj ((BoolNeg qnameExp), termNeg))
           
            else
                match (exprPos, exprNeg) with
                | (BoolExpr.BoolConst false, BoolExpr.BoolConst false) -> 
                        BoolExpr.BoolConst false
                            
                | (BoolExpr.BoolConst true, BoolExpr.BoolConst true) -> 
                        BoolExpr.BoolConst true
                
                | ( BoolExpr.BoolConst true, BoolExpr.BoolConst false) ->
                        qnameExp                    

                | (BoolExpr.BoolConst false, BoolExpr.BoolConst true) -> 
                        BoolExpr.BoolNeg (qnameExp)
 
                | (BoolExpr.BoolConst true, resultexp ) ->
                        BoolDisj (qnameExp, resultexp)
                        
                | (BoolExpr.BoolConst false, resultexp) -> 
                        BoolConj ((BoolNeg qnameExp), resultexp)
  
                | (resultexp, BoolExpr.BoolConst false) ->
                        BoolConj (qnameExp, resultexp)

                | (resultexp, BoolExpr.BoolConst true) -> 
                        BoolDisj (BoolNeg qnameExp, resultexp)
                    
                | (resultexp1, resultexp2) -> 
                        if resultexp1 = resultexp2 then
                            resultexp1
                        else
                            BoolDisj (BoolConj (qnameExp, resultexp1), BoolConj ((BoolNeg qnameExp), resultexp2))
 
        // Body of MakeCanonicalBool

        // Rewrite all atoms to Qnames and get the mapping
        let (rewrittenExp, boolVarList, atomMap) = BoolExpGetBoolVarsAndRewriteAtoms (boolexp)

        printfn "Start make canonical expression %s" (boolexp.ToString())

        // Make sure that we actually have boolean operations in expression
        if not(boolVarList.IsEmpty) then              
            let resultexpr = Canonicalizer (0, rewrittenExp, Map.ofList [] , boolVarList)
            printfn "Finish make canonical expression %s" (resultexpr.ToString())
            if not(atomMap.IsEmpty) then
                BoolExpRewriteQnameWithAtom(resultexpr, atomMap)
            else
                resultexpr
        else
//            let resultexpr = RemoveRedundantBoolTerms boolexp
//            printfn "Finish make canonical expression %s" (resultexpr.ToString())
            boolexp

     
    // Splits data grdactions to immediate actions and delayed actions
    let SplitDataGrdActions(dataActions:Actions.GrdAction list) =
        let assignNowActions = dataActions 
                                |>List.filter(fun (boolexp, action) -> (isAssignNowAction(action)))

        let assignNextActions = dataActions
                                |>List.filter(fun (boolexp, action) -> (isAssignNextAction(action)))

        (assignNowActions, assignNextActions)

   
    let rec ReadVarsofNatExpression(inexpr: Expressions.NatExpr) =
        match inexpr with
        | NatVar (qname, _) ->
            Set.ofList([(qname, None)])

        | NatConst (boollist) ->
            Set.ofList([])

        | NatLog2 (expr) ->
            (ReadVarsofNatExpression(expr))   

        | NatAdd (expr1, expr2) | NatSub (expr1, expr2)  | NatMul (expr1, expr2) | NatDiv (expr1, expr2) 
        | NatMod (expr1, expr2) | NatExp (expr1, expr2) ->
            (Set.union (ReadVarsofNatExpression(expr1)) (ReadVarsofNatExpression(expr2)))
        
        | NatOfBtv (btvexpr) ->
            (ReadVarsofBVExpression(btvexpr)) 
        
        | IntAbs (intexpr) ->
            (ReadVarsofIntExpression(intexpr))  

        | NatArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                match natexpr with
                | NatConst (boollist) ->
                    Set.ofList([qname, Some(ConvertBoolListToInt(boollist))])                                    
                | (other) -> (ReadVarsofNatExpression (other))
                
            |(other) -> Set.ofList([])
 
        | NatTupAcc (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                Set.ofList([qname, Some(index)])

            |(other) -> Set.ofList([])

        | (expr) -> Set.ofList([])
            

    and ReadVarsofIntExpression(inexpr: Expressions.IntExpr) =
        match inexpr with
        | IntVar (qname, _) ->
            Set.ofList([(qname, None)])

        | IntConst (boollist) ->
            Set.ofList([])

        | IntOfNat (natexp) ->
            (ReadVarsofNatExpression(natexp))

        | IntOfBtv (btvexpr) ->
            (ReadVarsofBVExpression(btvexpr)) 

        | IntAdd (expr1, expr2) | IntSub (expr1, expr2)  | IntMul (expr1, expr2) | IntDiv (expr1, expr2) | IntMod (expr1, expr2) ->
            (Set.union (ReadVarsofIntExpression(expr1)) (ReadVarsofIntExpression(expr2)))
        
        | IntArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                match natexpr with
                | NatConst (boollist) ->
                    Set.ofList([qname, Some (ConvertBoolListToInt(boollist))])                                    
                | (other) -> (ReadVarsofNatExpression (other))
                
            |(other) -> Set.ofList([])
 
        | IntTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                Set.ofList([qname, Some index])

            |(other) -> Set.ofList([])

        | (expr) ->
            Set.ofList([])
    
    and ReadVarsofBVExpression(inexpr: Expressions.BtvExpr) =
        match inexpr with
        | BtvVar (qname, _ ) -> 
            Set.ofList([qname, None])
        | BtvConst (boollist) ->
            Set.ofList([])
        | BtvOfNat (natexpr, index) ->
            (ReadVarsofNatExpression(natexpr))
        | BtvOfInt (intexpr, index) ->
            (ReadVarsofIntExpression(intexpr))
        | BtvNeg (btvexpr) ->
            (ReadVarsofBVExpression(btvexpr))

        | BtvConj  (btvexpr1, btvexpr2) | BtvDisj (btvexpr1, btvexpr2) | BtvImpl (btvexpr1, btvexpr2) 
        | BtvEqv (btvexpr1, btvexpr2)   | BtvAppend (btvexpr1, btvexpr2) ->
            (Set.union (ReadVarsofBVExpression(btvexpr1)) (ReadVarsofBVExpression(btvexpr2)))

        | BtvSegment (btvexpr, high, low) ->
            (ReadVarsofBVExpression(btvexpr)) 

        | BtvReverse (btvexpr) ->
            (ReadVarsofBVExpression(btvexpr)) 

        | BtvArrAcc (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                match natexpr with
                | NatConst (boollist) ->
                    Set.ofList([qname, Some(ConvertBoolListToInt(boollist))])                                    
                | (other) -> (ReadVarsofNatExpression (other))
                
            |(other) -> Set.ofList([])
  
        | BtvTupAcc (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                Set.ofList([qname, Some(index)])

            |(other) -> Set.ofList([])
 
        |(other) -> Set.ofList([])
            
   
    let rec ReadVarsofRealExpression(inexpr: Expressions.RealExpr) =
        match inexpr with
        | RealVar (qname) ->
            Set.ofList([(qname, None)])

        | RealConst (boollist) ->
            Set.ofList([])

        | RealOfNat (natexp) ->
            (ReadVarsofNatExpression(natexp))
     
        | RealOfInt (intexp) ->
            (ReadVarsofIntExpression(intexp))

        | RealAdd (expr1, expr2) | RealSub (expr1, expr2)  | RealMul (expr1, expr2) | RealDiv (expr1, expr2) | RealExp (expr1, expr2) ->
            (Set.union (ReadVarsofRealExpression(expr1)) (ReadVarsofRealExpression(expr2)))
        
        | RealSin(expr)| RealCos(expr)| RealLog2(expr) ->       
            (ReadVarsofRealExpression(expr))
        
        | RealArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                match natexpr with
                | NatConst (boollist) ->
                    Set.ofList([qname, Some(ConvertBoolListToInt(boollist))])                                    
                | (other) -> (ReadVarsofNatExpression (other))
                
            |(other) -> Set.ofList([])
 
        | RealTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                Set.ofList([qname, Some index])

            |(other) -> Set.ofList([])

        | (expr) -> Set.ofList([])
            
    
    let rec ReadVarsofArrExpression(inexpr: Expressions.ArrExpr) =
        match inexpr with
        | ArrVar (qname, _) ->
            Set.ofList([(qname, None)])
        |(other) -> Set.ofList([])
  
    let rec ReadVarsofTupExpression(inexpr: Expressions.TupExpr) =
        match inexpr with
        | TupVar (qname, _) ->
            Set.ofList([(qname, None)])
        |(other) -> Set.ofList([])

    let rec ReadVarsofBoolExpression(inexpr: Expressions.BoolExpr) =
        match inexpr with
        | BoolVar (qname) -> Set.ofList[(qname, None)]
                                
        | BoolConst (boolconst) -> Set.ofList []
           
        | BoolNeg (expr) ->
            ReadVarsofBoolExpression(expr)

        | BoolConj (expr1, expr2)  | BoolDisj (expr1, expr2) | BoolImpl (expr1, expr2) | BoolEqu (expr1, expr2) ->
            (Set.union (ReadVarsofBoolExpression(expr1)) (ReadVarsofBoolExpression(expr2)))

        | BtvEqu  (expr1, expr2) ->
            (Set.union (ReadVarsofBVExpression(expr1)) (ReadVarsofBVExpression(expr2)))

        // Thanks to using C++ structs, the equality of two structs is overiddin by te compiler.
        | TupEqu  (expr1, expr2) ->
            (Set.union (ReadVarsofTupExpression(expr1)) (ReadVarsofTupExpression(expr2)))
  
        | NatEqu (expr1, expr2) | NatLes  (expr1, expr2) | NatLeq  (expr1, expr2) ->
            (Set.union (ReadVarsofNatExpression(expr1)) (ReadVarsofNatExpression(expr2)))


        | IntEqu  (expr1, expr2) | IntLes  (expr1, expr2) | IntLeq  (expr1, expr2) ->
            (Set.union (ReadVarsofIntExpression(expr1)) (ReadVarsofIntExpression(expr2)))


        | RealEqu (expr1, expr2) | RealLes (expr1, expr2) | RealLeq (expr1, expr2)->
            (Set.union (ReadVarsofRealExpression(expr1)) (ReadVarsofRealExpression(expr2)))

        | BoolBitOfBtv (btvexpr, index) ->
            match btvexpr with
            | BtvVar (qname, _) ->
                Set.ofList[(qname, None)]
            |(other) -> ReadVarsofBVExpression (btvexpr)
   
        | BoolArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                match natexpr with
                | NatConst (boollist) ->
                    Set.ofList([qname, Some(ConvertBoolListToInt(boollist))])                                    
                | (other) -> (ReadVarsofNatExpression (other))
                
            |(other) -> Set.ofList([])
 
        | BoolTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                Set.ofList([qname, Some index])
            |(other) -> Set.ofList([])

        | (expr) -> Set.ofList([])
          

  
    let ReadVarsofExpression(inexpr: Expressions.Expr) =
        match inexpr with
        | Ebool (boolexpr) ->
            ReadVarsofBoolExpression(boolexpr)
        | Enat  (natexpr) ->
            ReadVarsofNatExpression(natexpr)
        | Eint (intexpr) ->
            ReadVarsofIntExpression(intexpr)
        | Ereal (realexpr) ->
            ReadVarsofRealExpression(realexpr)
        | Ebtv (bvexpr) ->
            ReadVarsofBVExpression(bvexpr)
        | Earr (arrexpr) ->
            ReadVarsofArrExpression(arrexpr)
        | Etup (tupexpr) ->
            ReadVarsofTupExpression(tupexpr)
        | (expr) -> Set.ofList([])
            

    // Returns a list of tuples (wrVar, rdVars, grdaction), where wrVar is the variable written to
    //  and rdVars are the variables readable by the guarded action.
    // For better performance, wrVars and RdVars of all guarded actions are parsed 
    //   before dependency analysis and topological sorting takes place.

    let ParseVariablesOfGrdActions(grdactions: Actions.GrdAction list) =
        let result = ref ([])
        grdactions|>
            List.iter(fun (guard, action) ->
                if isAssignmentAction(action) then
                    let expr = (RhsExpressionOfAction(action)).Value
                    let wrVar = (LhsQnameofAction(action))
                    let guardRdVars = ReadVarsofBoolExpression(guard)
                    let exprRdVars = ReadVarsofExpression(expr)
                    let resultGrdAction:GrdAction = (guard, action)
                    let item = (wrVar, (Set.union guardRdVars exprRdVars), resultGrdAction)
                    result := List.Cons (item, !result))
        (result.Value)
        
    // For building action dependency graph, adds an action to the adjancy list of an action.
    let AddToAdjList((key, value):(GrdAction*GrdAction), depGraph: Dictionary<GrdAction, GrdAction list>) =
        if (depGraph.ContainsKey(key)) then
            let tempAdjList = depGraph.Item key
            ignore(depGraph.Remove(key))
            depGraph.Add(key, List.Cons (value, tempAdjList))
        else
            depGraph.Add(key, [value])
        
    // Finds a total order preserving the partial order relation of nodes.
    // TODO: this function can be easily generalized to any type.
    let TopologicalSort(startGrdActions:GrdAction list, depGraph: Dictionary<GrdAction, GrdAction list>)=
    
        let rec TraverseDepthFirst(grdAction:GrdAction, markedActions:Set<GrdAction> ref, alreadyfinished:Set<GrdAction> ref) =

            if (not ((!alreadyfinished).Contains(grdAction))) then   
                if ((!markedActions).Contains(grdAction)) then
                    failwith (" No static schedule could be generated, graph is not a DAG at action:" + (grdAction.ToString()))
                    
                // If current grdaction is a leaf node then return it
                if (not(depGraph.ContainsKey(grdAction))) then
                    alreadyfinished:=(!alreadyfinished).Add grdAction
                    [grdAction]
                else  
                    // Mark current node to detect cyclic dependencies.                                 
                    markedActions:= (!markedActions).Add grdAction
                    let adjList = depGraph.Item grdAction
                    let result = ref([])
                    adjList 
                        |> List.iter(fun gaction ->
                            result := List.append (!result) (TraverseDepthFirst(gaction, markedActions, alreadyfinished)))
                    markedActions := (!markedActions).Remove grdAction
                    alreadyfinished:=(!alreadyfinished).Add grdAction
                    (List.append (!result) ([grdAction]))
            else
                []
                                                                               
        let finalOrderedList = ref([]) // Result of toplogical sort ordering.
        let orderedItemsPerStartNode = ref (Set.ofList([])) // Actions that has been already ordered.

        startGrdActions
            |> List.iter(fun grdAction ->  
                            let markedActions = ref (Set.ofList []) // Actions that have been visited put not added to the final order yet
                            finalOrderedList:= List.append (!finalOrderedList) (TraverseDepthFirst(grdAction, markedActions, orderedItemsPerStartNode)) 
                        )

        (!finalOrderedList)
 