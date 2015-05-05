//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//


namespace Averest.Synthesis.SysMoc.Efsm
open Averest.Synthesis.SysMoc

open Averest.Core
open Averest.Core.AIFIO
open Averest.Tools.CommandLine
open Averest.Core.Properties
open Averest.Core.Names
open Averest.Core.Printer
open Averest.Core.Declarations
open System.Collections.Generic
open Averest.Core.Expressions


type LabelGuardTuple = QName * BoolExpr
type StateLabels = Names.QName list


//
//
//  A class representing a single state in an EFSM
//

type EFSMState (id: int, labels: Names.QName list) = 
    inherit EqualityComparer<EFSMState>()
    // Label list is sorted to make sure it's unique 
    let _labels = List.sort labels
    let _id = id

    member this.Labels 
        with get() = _labels

    member this.Id
        with get() = _id

    override this.Equals(first:EFSMState, second:EFSMState) =
        first.Equals(second)

    override this.GetHashCode(obj:EFSMState) =
        this.Labels.GetHashCode()
        
    interface System.IComparable<EFSMState> with
        member this.CompareTo(other) =
            this.Labels.GetHashCode() - other.Labels.Length.GetHashCode()

    static member op_GreaterThan (first:EFSMState, second:EFSMState) =
        first.Labels.GetHashCode() > second.Labels.GetHashCode()
 
    static member op_GreaterThanOrEqual (first:EFSMState, second:EFSMState) =
        first.Labels.GetHashCode() >= second.Labels.GetHashCode()

    static member op_LessThan (first:EFSMState, second:EFSMState) =
        first.Labels.GetHashCode() < second.Labels.GetHashCode()
 
    static member op_LessThanOrEqual (first:EFSMState, second:EFSMState) =
        first.Labels.GetHashCode() <= second.Labels.GetHashCode()

    interface System.IEquatable<EFSMState> with
        member this.Equals(other:EFSMState) = 
            if (this.Labels.Length = other.Labels.Length) then
                if (List.forall2 (fun qname1 qname2 -> qname1 = qname2) _labels (List.sort other.Labels)) then true else false 
            else false       
    
 
    override this.Equals(other) =
        match other with
        | :? EFSMState as castedOther -> 
                if (this.Labels.Length = castedOther.Labels.Length) then
                    if (List.forall2 (fun qname1 qname2 -> qname1 = qname2) _labels (List.sort castedOther.Labels)) then true else false 
                else false       

        | _ -> false

    override this.GetHashCode() =
        this.Labels.GetHashCode()

    override this.ToString() =
        "Id: " + this.Id.ToString() + ", Labels:" + this.Labels.ToString()

//
//
//  A class representing a single state transition in an EFSM
//

type EFSMTransition (nextState: EFSMState, guard: Expressions.BoolExpr) = 
    let _guard = guard
    let _nextState = nextState

    member this.Guard
        with get() = _guard
    member this.NextState
        with get() = _nextState
    
    interface System.IEquatable<EFSMTransition> with
    // Equals definition ignores that guards and focuses on states only.
        member this.Equals(other:EFSMTransition) = 
            if this.NextState.Equals(other.NextState) then true else false

    override this.ToString() =
        "Grd: " + this.Guard.ToString() + ", Next:" + this.NextState.ToString()

//
//
//  A class representing an EFSM graph consisting of states and transitions
//

type EFSMGraph() =

    [<DefaultValue>]
    val mutable StartState:EFSMState

    let _graph= new Dictionary<Names.QName list, EFSMState * EFSMTransition list>()
    let _attachedDataGrdAction = new Dictionary<Names.QName list, Actions.GrdAction list>()

  
    member this.Add (state:EFSMState, transitions: EFSMTransition list) =
        _graph.Add(List.sort state.Labels, (state, transitions))

    member this.AddReplace (state:EFSMState, transitions: EFSMTransition list) =
        ignore (_graph.Remove(state.Labels))
        _graph.Add(List.sort state.Labels, (state, transitions))

    member this.Exists(state:EFSMState) =
        _graph.ContainsKey(state.Labels)

    member this.ExistsStateLabels(stateLabels:Names.QName list) =
        _graph.ContainsKey(List.sort stateLabels)

    member this.Remove(state:EFSMState) =
        ignore (_graph.Remove(state.Labels))
        
    member this.GetTransitions (state:EFSMState) =
        snd(_graph.Item state.Labels)
    
    member this.SetTransitions (state:EFSMState, transitions: EFSMTransition list) =
        _graph.Item state.Labels <- (state, transitions)

    member this.AddTransition (state:EFSMState, transition: EFSMTransition) =
        let newTransitions = List.Cons (transition, this.GetTransitions(state))
        this.AddReplace(state,newTransitions)

    member this.GetMatchState(state:EFSMState) =
        fst(_graph.Item state.Labels)

    member this.GetMatchStateLabels(stateLabels:Names.QName list) =
        fst(_graph.Item (List.sort stateLabels))

    member this.GetDataGrdActions(state:EFSMState) =
        _attachedDataGrdAction.Item state.Labels

    member this.AttachDataGrdActions(state:EFSMState, dataActions: Actions.GrdAction list) =
        _attachedDataGrdAction.Add(state.Labels, dataActions)

    member this.GetEnumerator () =
        _graph.GetEnumerator()
        
//
//
//  A class for building an EFSM out of an AIFComponent.
//
//  
            
    
type Efsm (Name:string, aifsys:Utils.AIFComponent )=  
    let checkForInOut =  
        aifsys.iface 
        |> List.iter (fun (x,y) -> 
            if y.flow = Averest.Core.Declarations.Flow.InOut then 
                failwith "AIFComponent has In-Out ports ! Please modify the system to use In and/or Out ports excusively!!")
    
    let _inPorts = Set.ofList(List.filter (fun (x,y) -> y.flow = Averest.Core.Declarations.Flow.Input) aifsys.iface)
    let _outPorts = Set.ofList(List.filter (fun (x,y) -> y.flow = Averest.Core.Declarations.Flow.Output) aifsys.iface)
    let _labels = List.sort(List.filter (fun (x,y) -> y.flow = Averest.Core.Declarations.Flow.Label) aifsys.locals 
                                            |> List.map (fun (x,y) -> (x,BoolConst false)))
    let _locals =  Set.ofList(List.filter (fun (x,y) -> y.flow = Averest.Core.Declarations.Flow.LocVar) aifsys.locals)

    let _labelValsMap = Map.ofList(_labels) 

    let _name = Name

    let mutable _stateIndex = 1

    let _finalState = new EFSMState(0 , [])

    let _abbrevDict =  new Dictionary<Names.QName, Expressions.BoolExpr>()

    let _efsmGraph = new EFSMGraph()

    // Used to group multiple guards in CGAs that affect a single label
    let _labelGuardDict = new Dictionary<QName, Expressions.BoolExpr>()
    
    // Get the label of the Start state.
    let _startLabel = 
        aifsys.ctrlFlow|> 
        List.find(fun (x,y) -> 
        match x with
            |Averest.Core.Expressions.BoolConst (true) -> true
            | _ -> false)
        |> (fun (x,y) ->  fst(Utils.LhsQnameofAction(y)))

    let mutable _instanceInitialized = false
    let mutable _instanceControlGraphBuilt = false

//  Getter-Setter for the unique value used to index states
    member private this.StateIndex
        with get() = _stateIndex
        and  set(value) = _stateIndex <- value

//    member this.GetLabelsinGrdAction (grdAction:Actions.GrdAction) =
//        let expvarnames = Expressions.FVarsBoolExpr(fst(grdAction)) |> Set.map( fun (x,y) -> x)
//        Set.intersect expvarnames _labels

    member private this.Islabel (qname:QName) =
        _labelValsMap.ContainsKey(qname)

//
//  Expands abbreviations found in a boolean expression.
//      expansion is based on the values available in _abbrevDict.
//
//
    member private this.ExpandBoolExp (boolexp:Expressions.BoolExpr) =
        let rec expander boolexp =
            match boolexp with
            |BoolVar (qname) ->  if _abbrevDict.ContainsKey(qname) then
                                    _abbrevDict.Item qname
                                 else
                                    BoolVar qname
            |BoolConst (value) -> BoolConst value
            |BoolNeg  (value) -> BoolNeg (expander value)
            |BoolConj (value1, value2) -> BoolConj (expander value1, expander value2)
            |BoolDisj (value1, value2) -> BoolDisj (expander value1, expander value2)
            |BoolImpl (value1, value2) -> BoolImpl (expander value1, expander value2)
            |BoolEqu  (value1, value2) -> BoolEqu (expander value1, expander value2)
            |(var:BoolExpr) -> var
            
        expander boolexp

    member private this.MakeState (labelList:QName list) =         
        let result = new EFSMState(this.StateIndex, Efsm.NormalizeLabels labelList)
        this.StateIndex <- this.StateIndex + 1

        result
 
    // Returns a complete label environment where the given labels are set to True, and everything else is set to false.    
    member private this.SetLabelValuesToTrue (inlabels:QName list) =
        let labels =  Set.ofList inlabels
            
        _labelValsMap|> Map.map(fun qname value -> 
                                if labels.Contains(qname) || qname = _startLabel then
                                    (Expressions.Ebool (Expressions.BoolConst true))
                                else
                                    (Expressions.Ebool (Expressions.BoolConst false)))

    member this.InputPorts
        with get() = Set.toList(_inPorts)
 
    member this.OutputPorts
        with get() = Set.toList(_outPorts)

    member this.LocalVars
        with get() = Set.toList(_locals)
 
    member this.Graph
        with get() = _efsmGraph   

    member this.Name
        with get() = _name

    static member IsFinalState(state: EFSMState) =
        state.Labels.IsEmpty
       
    static member private NormalizeLabels(labelList:QName list) = 
        List.sort (Set.toList (Set.ofList labelList))

    //
    //  Initializes constructs needed for building Efsm
    //
    //
    member this.Initialize () = 

        // Returns a boolean expression expanded by replacing all abbreviations with their original values.
        let ExpandAbbrev (expr:Expressions.Expr) =            
            match expr with
            // Assumes that for an abbreviation to be expanded, its referenced abbreviations are already in _abbrevDict
            | Expressions.Ebool (boolexp) -> this.ExpandBoolExp(boolexp)
            | _ -> failwith "Abbreviation table is corrupted: No valid boolean expression"

        // Initializes the abbreviation directory, abbreviations are used in reduce the size of boolean expressions.
        let InitializeAbbrevDict = 
            aifsys.abbrevs |> 
            List.iter (
                fun (boolexp,action) -> 
                    match action with
                    |Actions.AssignNow(lhs,_,exp) ->
                        match lhs with
                        |Expressions.LhsVar (name, _) ->
                            //_abbrevDict.Add(name, Utils.MakeCanonicalBoolExpr(ExpandAbbrev(exp)))
                            _abbrevDict.Add(name, ExpandAbbrev(exp))

                        | _ -> failwith "Abbreviation table is corrupted: No valid Qname"
                    | _ -> failwith "Abbreviation table is corrupted: Abbreviations are not direct assignment" )

        

        // Initializes a dictionary that maps Labels to Guards (boolexpr). This dict is used to group all GrdAction in 
        //  control flow that assigns values to the same label.
        let InitializeLabelGuards = 

            let tempLabelDict = new Dictionary<QName, Expressions.BoolExpr>()

            // Assumes that the first grdAction is the start label action and removes it 
            //  since its boolexp is always True.
            let normalizedControlFlow = 
                match aifsys.ctrlFlow with
                | [] -> []
                | head::tail -> tail

            let buildLabelDict (grdaction:Actions.GrdAction) =
                let qname = fst(Utils.LhsQnameofAction(snd(grdaction)))
                let boolexp = fst(grdaction)
                if tempLabelDict.ContainsKey(qname) then
                    let currentExpr = tempLabelDict.Item qname
                    ignore (tempLabelDict.Remove(qname))
                    // Multiple guards in a CGA are grouped with a disjoin
                    tempLabelDict.Add(qname, BoolDisj (boolexp, currentExpr))                   
                else
                    tempLabelDict.Add(qname, boolexp)
            
            normalizedControlFlow|> List.iter(buildLabelDict)

            let mutable labelEnum = tempLabelDict.GetEnumerator()

            while labelEnum.MoveNext() do
                // Boolean expressions in temporary dict are expanded and canonicalized and added to the final
                //  dict for grouping a single label with multiple guards
                let expandedGuard = Utils.MakeCanonicalBoolExpr(this.ExpandBoolExp labelEnum.Current.Value)
//                let expandedGuard = this.ExpandBoolExp labelEnum.Current.Value
//                printfn "CGA Label %s, Guard %s " (labelEnum.Current.Key.ToString()) (expandedGuard.ToString()) 

                _labelGuardDict.Add(labelEnum.Current.Key, expandedGuard) 
        
        // Initializes the mapping between abbreviations and their guards    
        //InitializeAbbrevDict
        // Maps each label to combined guard consisting of all CGAs writing to that label.
        //InitializeLabelGuards

        _instanceInitialized <- true
    //
    //  Builds the graph of Efsm
    //
    //
    member this.BuildControlGraph = 
        
        if not(_instanceInitialized) then
            failwith "Build control graph failed, instance not initialized"

        // In a list of labels and guards, all labels with the same guard are grouped together
        let ConditionalLabelsGroup (conditionalLabelsSeperated: (QName*BoolExpr) list) =
  
            let exprLabelsMap = ref (Map.ofList([]))
 
            conditionalLabelsSeperated
                |>List.iter(fun (clabel, boolexp) -> 
                    if (!exprLabelsMap).ContainsKey(boolexp) then
                        let oldlabels = (!exprLabelsMap).Item boolexp
                        exprLabelsMap := (!exprLabelsMap).Add(boolexp, Efsm.NormalizeLabels (List.Cons(clabel,oldlabels)))
                    else
                        exprLabelsMap := (!exprLabelsMap).Add(boolexp, [clabel]))

            (Map.toList (!exprLabelsMap))




        // Rewrites guards in such a way that they are orhagonal to each other i.e. result of conjuncting any two guards is false.
        //   this rewriting preserves the behavior but makes it deterministic.
            
        let GenerateWellFormedConditionalTransitions (conditionalLabels: (BoolExpr * QName list) list, generateFinalStateTransition:bool) = 

            let rec ConditionalLabelsGenerator (currentBoolExpr:BoolExpr, fixedLabels:  QName list, unfixedconditionalTransitions: (BoolExpr * QName list) list) = 
  
                match unfixedconditionalTransitions with
                | [] -> 
                    if generateFinalStateTransition then
                        [(currentBoolExpr, fixedLabels)]
                    else 
                        if not(fixedLabels.IsEmpty) then
                            [(currentBoolExpr, fixedLabels)]
                        else 
                            []

                | head::tail ->
                    let (currentGuard, currentLabels) = head
                    
                    let evalPositive = Utils.MakeCanonicalBoolExpr(BoolConj (currentGuard, currentBoolExpr))
                    let evalNegative = Utils.MakeCanonicalBoolExpr(BoolConj (BoolNeg (currentGuard), currentBoolExpr))
                    
                    let resultPosEval = 
                        if not (evalPositive = (BoolConst false)) then
                            ConditionalLabelsGenerator(evalPositive, (List.append currentLabels fixedLabels), tail)
                        else 
                            []
    
                    let resultNegEval = 
                        if not (evalNegative = (BoolConst false)) then
                            ConditionalLabelsGenerator(evalNegative, fixedLabels, tail)
                        else 
                            []

                    (List.append resultPosEval resultNegEval)

//            printfn ""
//            printf "BEGIN handling transition list : "
//            conditionalLabels
//                |> List.iter (fun (guard, labels) ->
//                        printfn ""
//                        printf "Guard :%s, Labels: " (guard.ToString()) 
//                        labels|>List.iter(fun x -> printf "%s," (x.ToString())))
            

            let result = ConditionalLabelsGenerator(BoolConst true, [], conditionalLabels)

            result

//            printfn ""
//            printf "FINISHED handling transition list : "
//            result
//                |> List.iter (fun (guard, labels) ->
//                        printfn ""
//                        printf "Guard :%s, Labels: " (guard.ToString()) 
//                        labels|>List.iter(fun x -> printf "%s," (x.ToString())))
                
//            let transitionsToNormalStates = 
//                result
//                |>List.filter (fun (guard, qnameList) -> not(qnameList.IsEmpty))
//                |>List.map (fun (guard, qnameList) -> (guard, Efsm.NormalizeLabels qnameList))
//
//            if not(generateFinalStateTransition) then
//                transitionsToNormalStates
//
//            else
//
//                let combinedGuardToFinalState = ref (BoolConst false)
//
//                result
//                |> List.filter (fun (guard, qnameList) -> qnameList.IsEmpty)
//                |> List.iter (fun (guard, _) -> 
//                                    combinedGuardToFinalState := (BoolDisj (guard, !combinedGuardToFinalState)))
//
//                let canonicalGuardToFinalState = Utils.MakeCanonicalBoolExpr(!combinedGuardToFinalState)
//
//                if not(canonicalGuardToFinalState = (BoolConst false)) then
//
//                    let combinedTransitionToFinalState = (canonicalGuardToFinalState, [])
//                    List.Cons (combinedTransitionToFinalState, transitionsToNormalStates)
//                else                                
//                    transitionsToNormalStates

//        let rec ConditionalLabelsWellForm (conditionalLabels: (BoolExpr * QName list) list) = 
//            
//            let GetOrthagonalityTransitionLists(basetrans:(BoolExpr * QName list) , conditionalLabels: (BoolExpr * QName list) list) = 
//            
//            
//                let (hguard, hqlist) = basetrans
//
//                let orthCondList = ref ([])
//                let notorthCondList = ref ([])
//                conditionalLabels|> List.iter(fun (guard, qlist) ->
//                                            let conjGuard = Utils.MakeCanonicalBoolExpr(BoolConj (hguard, guard))
//                                            if  (conjGuard = (BoolConst false)) then
//                                                orthCondList := List.Cons ((guard, qlist), !orthCondList)
//                                            else
//                                                notorthCondList:= List.Cons (((conjGuard), Efsm.NormalizeLabels (List.append hqlist qlist)), !notorthCondList))
//                (!orthCondList, !notorthCondList) 
//
//
//            match conditionalLabels with
//            |head::tail ->
//                if tail.Length <= 1 then
//                    // if we have two element (or one), they must be orthagonal i.e. well formed by definition of Quartz semantics
//                    (conditionalLabels)
//                else
//                    let (orthTransList, notOrthTransList) = GetOrthagonalityTransitionLists(head, tail)
//                    if (notOrthTransList.IsEmpty) then
//                        (List.Cons (head, ConditionalLabelsWellForm(orthTransList)))
//                    else
//                        (List.append (ConditionalLabelsWellForm(orthTransList)) (ConditionalLabelsWellForm(notOrthTransList)))
//                
//            |[] -> ([])

        // Given an input label environment, labels (and their guards) that are valid in the next step are generated.
        let GetNextTransitionsLabels (currentLabelValueMap:Map<QName, Expressions.Expr>) =

            let mutable labelEnum = _labelGuardDict.GetEnumerator()
            let mutable unconditionalLabels = []
            let mutable conditionalLabelsSeperated = []

            while labelEnum.MoveNext() do
                let result = Expressions.SubstBool currentLabelValueMap labelEnum.Current.Value
                match result with
                | BoolConst (value) -> if value then 
                                        unconditionalLabels <- List.Cons (labelEnum.Current.Key, unconditionalLabels)
                                        ()
                | (expr) -> conditionalLabelsSeperated <- List.Cons ((labelEnum.Current.Key, Utils.MakeCanonicalBoolExpr(expr)), conditionalLabelsSeperated)
            

            if conditionalLabelsSeperated.IsEmpty then
                [], Efsm.NormalizeLabels unconditionalLabels
            else
                // Mutiple labels with the same condition should be grouped
                let conditionalLabelsGrouped = ConditionalLabelsGroup(conditionalLabelsSeperated)


                if unconditionalLabels.IsEmpty then
                    // For state transitions to be well formed, the conjunction of any two guards should be false 
                    //  otherwise the Efsm well be non-deterministic.
                    let conditionalLabelsWellFormed = GenerateWellFormedConditionalTransitions (conditionalLabelsGrouped, true)
                    conditionalLabelsWellFormed, []   

                else
                    let conditionalLabelsWellFormed = GenerateWellFormedConditionalTransitions (conditionalLabelsGrouped, false)   
                    conditionalLabelsWellFormed, Efsm.NormalizeLabels unconditionalLabels   
        
        // Given an EfsmState, all state transitions are generated i.e. next states and their guards.     
        let GetNextTransitionStateList (currentState:EFSMState) = 
            if (Efsm.IsFinalState currentState) then 
                []
            else
                let currentLabelValueMap = this.SetLabelValuesToTrue(currentState.Labels)
                let (condLabels, uncondLabels) = GetNextTransitionsLabels(currentLabelValueMap)

                if condLabels.IsEmpty then

                    if uncondLabels.IsEmpty then
                        [(_finalState, BoolConst true)]
                    else
                        // If all labels are visited without condition, then all unconditional labels are
                        //  grouped in a single next state.
                
                        if (not(_efsmGraph.ExistsStateLabels(uncondLabels))) then
                            if not(uncondLabels = currentState.Labels) then
                                let newState = this.MakeState uncondLabels
                                [(newState, BoolConst true)] 
                                    
                            else
                                [(currentState, BoolConst true)]
                        
                        else 
                            let existingState = _efsmGraph.GetMatchStateLabels(uncondLabels)
                            [(existingState, BoolConst true)]               

                else
                    let transitionList= condLabels|> 
                                        List.map(fun (expr, clabels) -> 
                                            let newLabels =  Efsm.NormalizeLabels (List.append clabels uncondLabels)  
                                            if newLabels.IsEmpty then
                                                (_finalState, expr)                                         
                                            else 
                                                // Check if it's a transition to an already visited state                                                                           
                                                if (not(_efsmGraph.ExistsStateLabels(newLabels)))then
                                                    // Check if then a transition to self
                                                    if currentState.Labels = newLabels then
                                                        (currentState, expr)
                                                
                                                    else
                                                        // It's a transition to a new state then
                                                        let newState = this.MakeState(newLabels)
                                                        (newState, expr)                                             
                                                 else 
                                                    // These transitions will only be added.
                                                    let existingState = _efsmGraph.GetMatchStateLabels(newLabels)
                                                    (existingState, expr)) 
                    transitionList                                                   
                                                                              
        // Generates the Efsm based on a breadth-first search of next states
        let rec GenerateGraph (currentStateList: EFSMState list) =
            if currentStateList.Length > 0 then
                
                // Collects all unique states that should be visited next
                
                let markedStates = ref (Map.ofList([]))

                // This map is used when determining the unique unvisited states that should be visited next
                let currentStateMap = Map.ofList(currentStateList|> List.map(fun state -> (state.Labels, state)))
                
                // Starting for all states at current depth level, generate all transitions for those states and
                //  get the unique states that should be visited next.
                currentStateList  
                    |> List.iter(fun currentState ->   
                        let currentTransitionsList = GetNextTransitionStateList(currentState)
                        let normalizedTransitions = currentTransitionsList
                                                        |> List.map (fun (state, guard) -> 
                                                                        if currentStateMap.ContainsKey(state.Labels) then
                                                                            // If a state in the current state list is referenced it should 
                                                                            //  be mapped in the transition.
                                                                            let toBeVisited = currentStateMap.Item state.Labels
//                                                                            printfn "WARNING: State %s replaced with %s" (state.Id.ToString()) (toBeVisited.Id.ToString())
                                                                            (new EFSMTransition (toBeVisited, guard))

                                                                        else
                                                                            // Marking has been introduced to get the unique states that should be visited                                                
                                                                            if not((!markedStates).ContainsKey(state.Labels)) then
                                                                                if  not (_efsmGraph.Exists(state)) then 
                                                                                    // Gets the unique states that should be visited next                                                                               
                                                                                    markedStates := Map.add state.Labels state !markedStates

                                                                                (new EFSMTransition (state, guard))

                                                                                else                                                                
                                                                                (new EFSMTransition ((!markedStates).Item state.Labels, guard)))

                        _efsmGraph.Add(currentState, normalizedTransitions ))
                           
                
                GenerateGraph (Map.toList(!markedStates)|> List.map(fun (key,value) -> value))
            ()
    
        // Generating Efsm based on a depth first search. This one is still bugus.
//        let rec GenerateGraphDFS (currentState:EFSMState) = 
//
//            let currentLabelValueMap = this.SetLabelValuesToTrue(currentState.Labels)
//            let (condLabels, uncondLabels) = GetNextTransitionsLabels(currentLabelValueMap)
//            if condLabels.IsEmpty then
//                let newState = this.MakeState(uncondLabels)
//                if (not(_efsmGraph.Exists(newState))) then
//                    if not(newState = currentState) then
//                        let transition = new EFSMTransition(newState, BoolConst true)               
//                        _efsmGraph.Add(currentState, [transition])                   
//                        GenerateGraphDFS(newState)
//                    else
//                        let transition = new EFSMTransition(currentState, BoolConst true)               
//                        _efsmGraph.Add(currentState, [transition])                                           
//                else 
//                    let existingState = _efsmGraph.GetMatchState(newState)
//                    let transition = new EFSMTransition(existingState, BoolConst true)               
//                    _efsmGraph.Add(currentState, [transition])
//            else
//                let transitionList= condLabels|> 
//                                    List.map(fun (expr, clabels) -> 
//                                        let newState = this.MakeState(List.append clabels uncondLabels)
//                                        if (not(_efsmGraph.Exists(newState)))then
//                                            // These transitions will be visited next.
//                                            if currentState = newState then
//                                                let transition = new EFSMTransition(currentState, expr)
//                                                (transition,false)
//                                            else
//                                                let transition = new EFSMTransition(newState, expr)
//                                                (transition,true)
//                                         else 
//                                            // These transitions will only be added.
//                                            let existingState = _efsmGraph.GetMatchState(newState)
//                                            let transition = new EFSMTransition(existingState, expr)
//                                            (transition,false))               
//                                                                              
//                let transitionsListOnly = transitionList |> List.map(fun (tlist, valid) -> tlist)
//                _efsmGraph.Add(currentState, transitionsListOnly)
//                transitionList
//                    |> List.filter (fun (tlist, valid) -> valid)
//                    |> List.iter(fun (transition,valid) ->  GenerateGraphDFS(transition.NextState))

        // Startes generating the Efsm and sets the starting state of the Efsm.
        let GenerateGraphInit = 

            let currentState = this.MakeState([_startLabel])
            _efsmGraph.StartState <- currentState
            let currentState = _efsmGraph.StartState
            // For the start state we need a label environment of all false
            let currentLabelValueMap = _labelValsMap |> Map.map(fun qname boolexp -> Ebool (boolexp))
            let (condLabels, uncondLabels) = GetNextTransitionsLabels(currentLabelValueMap)
            if condLabels.IsEmpty then
                let newState = this.MakeState(uncondLabels)
                let transition = new EFSMTransition(newState, BoolConst true)               
                _efsmGraph.Add(currentState, [transition])
                GenerateGraph([newState])
            else
                let transitionList= condLabels|> 
                                            List.map(fun (expr, clabels) -> 
                                                let newState = this.MakeState(List.append clabels uncondLabels)                                           
                                                let transition = new EFSMTransition(newState, expr)
                                                transition) 
                
                _efsmGraph.Add(currentState, transitionList)

                GenerateGraph (transitionList|>List.map(fun transition -> transition.NextState))
                                   
        //GenerateGraphInit
        _instanceControlGraphBuilt <- true
                        
    member this.BuildAttachedDataGrdActions = 

        if not(_instanceControlGraphBuilt) then
            failwith "Build attached data guarded action to a control graph failed, control graph not built"

        let visited = new Dictionary<EFSMState, bool>()

        let expandedDataFlow = 
            aifsys.dataFlow |> List.map (fun (guard, action) -> 
                                                let expandedGrdAction:Actions.GrdAction = (this.ExpandBoolExp guard, action)                                                
                                                expandedGrdAction)

//        expandedDataFlow |> List.iter(fun (grdAction) -> printfn "DGA assign next %s " (grdAction.ToString()))

        let AttachGrdActionsToStartState =

            // Maps a Map of type <QName, BoolExpr> to type <QName, Expr>
            let labelenv = _labelValsMap |> Map.map(fun qname boolexp -> Ebool (boolexp))
            let attachedActions = ref ([])

            expandedDataFlow |> List.iter (fun (guard,action) -> 
                                            let result = Expressions.SubstBool labelenv guard
                                            if not (result = (BoolConst false)) then
                                                let grdAction:Actions.GrdAction = (result,action)
                                                attachedActions := List.Cons (grdAction, !attachedActions))
            (!attachedActions)

        let AttachGrdActionsToState(state:EFSMState) =
 
            let labelenv = this.SetLabelValuesToTrue(state.Labels)
            let attachedActions = ref ([])

            if not(Efsm.IsFinalState (state)) then
                expandedDataFlow |> List.iter (fun (guard,action) -> 
                                                let result = Expressions.SubstBool labelenv guard
                                                if not (result = (BoolConst false)) then
                                                    let grdAction:Actions.GrdAction = (result,action)
                                                    attachedActions := List.Cons (grdAction, !attachedActions))
            (!attachedActions)


        let rec AttachDataGrdActionsToStateList (currentStateList:EFSMState list) = 
            
            if not (currentStateList.IsEmpty) then

                let toBeVisited = ref( Map.ofList([]))

                let currentStateMap = currentStateList|>List.map (fun x -> (x.Labels,true))|> Map.ofList

                currentStateList |> List.iter (fun currentState ->
                                                    visited.Add(currentState, true)
                                                    _efsmGraph.AttachDataGrdActions(currentState, AttachGrdActionsToState(currentState))
                                                    _efsmGraph.GetTransitions(currentState)
                                                                |> List.iter(fun transition ->
                                                                                    if      not (currentStateMap.ContainsKey(transition.NextState.Labels)) // state won't be visited in the current iteration
                                                                                         && not ((!toBeVisited).ContainsKey(transition.NextState.Labels))  // state is not duplicate of state that should be visited next
                                                                                         && not (visited.ContainsKey(transition.NextState)) then            // state not visited before
                                                                                        toBeVisited := Map.add transition.NextState.Labels transition.NextState !toBeVisited ))
                                                
                AttachDataGrdActionsToStateList( Map.toList(!toBeVisited) |> List.map(fun (key,value) -> value))    
                
        _efsmGraph.AttachDataGrdActions(_efsmGraph.StartState, AttachGrdActionsToStartState)   
        AttachDataGrdActionsToStateList(_efsmGraph.GetTransitions(_efsmGraph.StartState)|>List.map (fun transition -> transition.NextState))

        ()
                                                                
    member this.Result = 

        Set.toList(_inPorts) |> List.iter (fun (x,y) -> printfn "Input Qname:%s Type %s " (x.ToString()) (y.qtype.ToString())) 
        Set.toList(_outPorts) |> List.iter (fun (x,y) -> printfn "Output Qname:%s Type %s " (x.ToString()) (y.qtype.ToString())) 
        _labels |> List.iter (fun (x,y) -> printfn "Labels Qname:%s " (x.ToString()) ) 
        Set.toList(_locals) |> List.iter (fun (x,y) -> printfn "Locals Qname:%s Type %s " (x.ToString()) (y.qtype.ToString())) 
        let mutable expandedAbrev = _abbrevDict.GetEnumerator()
        while expandedAbrev.MoveNext() do
            printfn "Expanded Abbreviation Qname:%s Expre %s" (expandedAbrev.Current.Key.ToString()) (expandedAbrev.Current.Value.ToString()) 

   // Simply prints the current Efsm on the command-line.
    member this.PrintEFSM =

        let PrintState (state:EFSMState) =
            printf "State Id:%s, Labels:" (state.Id.ToString()) 
            state.Labels|>List.iter(fun x -> printf "%s," (x.ToString()))
            printfn "end."
            
        let visited = new Dictionary<EFSMState, bool>()

        let rec PrintGraph (currentStateList:EFSMState list) = 
            
            if not (currentStateList.IsEmpty) then

                let toBeVisited = ref( Map.ofList([]))

                let currentStateMap = currentStateList|>List.map (fun x -> (x.Labels,true))|> Map.ofList

                currentStateList |> List.iter (fun currentState ->
                                                    visited.Add(currentState, true)
                                                    PrintState currentState
                                                    _efsmGraph.GetTransitions(currentState)
                                                                |> List.iter(fun transition ->
                                                                                    if      not (currentStateMap.ContainsKey(transition.NextState.Labels)) // state won't be visited in the current iteration
                                                                                         && not ((!toBeVisited).ContainsKey(transition.NextState.Labels))  // state is not duplicate
                                                                                         && not (visited.ContainsKey(transition.NextState)) then            // state not visited before
                                                                                        toBeVisited := Map.add transition.NextState.Labels transition.NextState !toBeVisited
                                                                                    printf "    Guard, %s , Next" (transition.Guard.ToString()) 
                                                                                    PrintState transition.NextState))
                                                
                PrintGraph( Map.toList(!toBeVisited) |> List.map(fun (key,value) -> value))       

        PrintGraph([_efsmGraph.StartState])
            

        
