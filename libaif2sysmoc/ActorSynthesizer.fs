//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//



namespace Averest.Synthesis.SysMoc.Synthesis

open Averest.Synthesis.SysMoc.Efsm
open Averest.Synthesis.SysMoc

open Averest.Core
open Averest.Core.Expressions
open Averest.Core.AIFIO
open Averest.Core.Names
open Averest.Core.Declarations
open System.Collections.Generic
open Averest.Core.Actions
open System.IO
 

type ActorSynthesizer(synEfsm:Efsm, detachedOutputPorts: Set<QName>) =
    
    // Default clock period in NS
    let mutable _defaultClk = 10 

    // Declaration text of input ports of actor
    let _inputPortDecl = 
        let syscDecl = new StringWriter()
        synEfsm.InputPorts
            |> List.iter (fun (qname, qdecl) -> 
                    syscDecl.WriteLine()
                    syscDecl.Write ("   smoc_port_in< "+ SysMocDefs.GetSysCTypeName(qdecl.qtype)+" > " + SysMocDefs.GetVarName(qname) + " ;"))

        syscDecl.ToString()

    // Declaration text of output ports of actor
    let _outPortDecl =
        let syscDecl = new StringWriter()
        synEfsm.OutputPorts
            |> List.iter (fun (qname, qdecl) ->  
                // No definition of output port is generated for detached outputs.
                if not(detachedOutputPorts.Contains(qname)) then                                                                     
                    syscDecl.WriteLine()
                    syscDecl.Write ("   smoc_port_out< "+ SysMocDefs.GetSysCTypeName(qdecl.qtype)+" > " + SysMocDefs.GetVarName(qname) + " ;"))

        syscDecl.ToString()

    // Declaration text of local variables      
    let _localDecl =
        let syscDecl = new StringWriter()

        synEfsm.LocalVars|> List.iter (fun (qname, declaration) ->
                                            syscDecl.WriteLine()  
                                            syscDecl.Write ("   " + SysMocDefs.GenSysCDeclWithCarryAndNextFlag(qname, declaration.qtype)))

        // Generating local declarations of output port carry variables
        syscDecl.WriteLine()
        syscDecl.Write("   // local declaration of output port carry variables ")
        synEfsm.OutputPorts|> List.iter (fun (qname, qdecl) ->  
                                            syscDecl.WriteLine()
                                            syscDecl.Write ("   " + SysMocDefs.GenSysCDecl(qname,qdecl.qtype, AuxName.Carry) )
                                            // Only event output vars need a next flag, the dependyncy analysis of delayed output
                                            //    actions will produce the correct next value of memorized output variables
                                            if (qdecl.storage = Event) then
                                                syscDecl.Write ("   " + SysMocDefs.GenSysCDecl(qname, qdecl.qtype, AuxName.NextFlag)))
        syscDecl.ToString()

    // Synthsizes text of smoc state declarations
    let _stateDecl =
        let syscDecl = new StringWriter()
        let mutable stateEnumerator = synEfsm.Graph.GetEnumerator()

        while stateEnumerator.MoveNext() do
            syscDecl.WriteLine()
            syscDecl.Write("   smoc_firing_state " +  (SysMocDefs.GetStateName (fst(stateEnumerator.Current.Value)))+ " ;")
            
        syscDecl.ToString() 
    
    // Mapping Input/Output qnames to their corresponding variable name in synthesized text.   
    //   needed for variable rewriting. 
    let _portNameMap =
        let inputPortNameList = synEfsm.InputPorts |> List.map(fun (qname,decl) -> (qname, SysMocDefs.GetPortVar(qname))) 
        let outputPortNameList = synEfsm.OutputPorts |> List.map(fun (qname,decl) -> (qname, SysMocDefs.GetCarryVarName(qname))) 
        (Map.ofList(List.append inputPortNameList outputPortNameList))
    
    // Mapping each local variables in the delayed actions to its corresponding carry variable.
    //  needed of variable rewriting. It's also used to split DGAs assigning to local variables from DGAs 
    //  assigning to output variables.
    let _delayedLocalVarMap =             
        Map.ofList(synEfsm.LocalVars|>List.map (fun (qname, decl) -> (qname, SysMocDefs.GetCarryVarName(qname))))

    // Set of output variables of storage type Event.
    let _eventOutputVars = 
        Set.ofList(synEfsm.OutputPorts|>List.filter(fun (qname, decl)-> (decl.storage = Event))|>List.map(fun (qname,decl)-> qname))

    //  We collect arrays in the actor for a future work. Having arrays in readVars causes problems for dependency analysis used f
    //  or topological sorting of actions.
    //  Note that tuples can be handled considering that their variable is identified with a qname and a static nat.
    //  However, array vars are identified with a qname and a natexpr. Natexpr can be resolved only at runtime and therefore 
    //  we do not fully support it for the timebeing.
    let _arraysVars = 
        let result = ref([])
        (synEfsm.LocalVars) 
            |> List.iter(fun (qname, decl)-> 
                match decl.qtype  with
                |Types.Qarr (_, _) ->
                    result := List.Cons (qname, !result)
                |(_) -> ())
        Set.ofList(!result)
                    

    // Text to set the default value of local vars in the actor constructor.    
    let _reset_next_flag_vals = 
        let writer = new StringWriter()
        // local vars of Efsm need a Var, CarryVar, and Next flag.
        synEfsm.LocalVars
            |> List.iter (fun (qname, decl) -> 
                            writer.WriteLine()
                            writer.Write ("    " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.NextFlag)))
                            
        // Output vars of Efsm need a local var and if it's of Event type it needs also a Next flag.
        synEfsm.OutputPorts |> List.iter(fun (qname, decl) ->
                            if (decl.storage = Event) then
                                writer.WriteLine()
                                writer.Write ("    " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.NextFlag)))                            

        (writer.ToString())
   

    // Text to set the default value of local vars in the actor constructor.    
    let _local_default_vals = 
        let writer = new StringWriter()
        // local vars of Efsm need a Var, CarryVar, and Next flag.
        synEfsm.LocalVars
            |> List.iter (fun (qname, decl) -> 
                            writer.WriteLine()
                            writer.Write ("   " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.Self))
                            writer.Write ("   " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.Carry))
                            writer.Write ("   " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.NextFlag)))
                            
        // Output vars of Efsm need a local var and if it's of Event type it needs also a Next flag.
        synEfsm.OutputPorts |> List.iter(fun (qname, decl) ->
                            writer.WriteLine()
                            writer.Write ("   " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.Carry))
                            if (decl.storage = Event) then
                                writer.Write ("   " + SysMocDefs.GenSetDefaultVal(qname, decl.qtype, AuxName.NextFlag)))                            

        (writer.ToString())

    
    // Text placed after immediate guarded actions to propagate the values
    // in carry vars of output ports to output ports.
    let _actorActionPropagteOutput = 
        let writer = new StringWriter()
        writer.WriteLine()
        writer.Write("    // Assigning output carry variables to output port values")
        synEfsm.OutputPorts|>List.iter(fun (qname,decl) -> 
                                        writer.WriteLine()
                                        // We do not set output port value if the output port is detached
                                        if not(detachedOutputPorts.Contains(qname)) then                                                                                                                 
                                            writer.Write("    "+SysMocDefs.GetPortVar(qname)+ " = " + SysMocDefs.GetCarryVarName(qname)+ " ;")
                                        writer.Write(SysMocDefs.GenActorDebugMsg(" OUTPUT", SysMocDefs.GetPortVar(qname), SysMocDefs.GetCarryVarName(qname)))
                                       )
        (writer.ToString())

    // Declarations of state transitions.
    let _stateTransitionDecl = new StringWriter()

    // Definitions of actor actions.
    let _actionDefs = new StringWriter()

    // Definitions of guards on state definitions.
    let _guardDefs = new StringWriter()

    // Definitions of state transitions.
    let _transitionsDefs = new StringWriter()


    // Generating code text of setting the reaction to absence. This text is placed at the beginning
    //    of all actor actions.
    let _genActorActionPreamble =
        let preWriter = new StringWriter()
        preWriter.WriteLine()
        preWriter.Write("    // A shared reaction to absence between different actions to save code size.")
        synEfsm.LocalVars 
            |> List.iter(fun (qname, decl) ->
                                    preWriter.WriteLine() 
                                    preWriter.Write(SysMocDefs.GenReactionToAbsence(qname, decl))                                                                                     
                                )
 
        synEfsm.OutputPorts 
            |> List.iter(fun (qname, decl) -> 
                                    preWriter.WriteLine()                               
                                    preWriter.Write(SysMocDefs.GenReactionToAbsence(qname, decl))                                                                                     
                                )
 
        (preWriter.ToString())                               

    // Splits delayed grdaction to actions assigning to local variables and actions assigning to output variables
    let SplitDelayedDataGrdAction(delayDataActions:Actions.GrdAction list) =

        // Delayed actions that assign to local variables
        let assignLocalVarActions = delayDataActions 
                                        |>List.filter(fun (boolexp, action)  ->                                                             
                                                    let lhsQname = (Utils.LhsQnameofAction(action))
                                                    // Check that the assignment is to a local variable
                                                    (_delayedLocalVarMap.ContainsKey(fst(lhsQname))) )                              
 
        // Delayed actions that assign to output variables                                            
        let assigntOutputVarActions = delayDataActions 
                                        |>List.filter(fun (boolexp, action) -> 
                                                    let lhsQname = (Utils.LhsQnameofAction(action))
                                                    // Check that the assignment is not to a local variable
                                                    //  and thus it should be to an output variable.
                                                    not (_delayedLocalVarMap.ContainsKey(fst(lhsQname))) )                                    
                                                            
        (assignLocalVarActions, assigntOutputVarActions)


    let GenerateImmediateActionText(immediateActions: Actions.GrdAction list, bodyWriter: StringWriter) =
        let parsedGrdActions = Utils.ParseVariablesOfGrdActions(immediateActions)
        let depGraph = new Dictionary<GrdAction, GrdAction list>()
        // Initially all guards are assumed indpendent of each other.
        let startGuardedActions = ref (Set.ofList(immediateActions))
               
        // Build true dependency graph (inversed) 
        parsedGrdActions
            |> List.iter(fun (currentWrVar, currentRdVars, currentgAction) ->                                 
                            parsedGrdActions
                                |> List.iter( fun (wrVar, rdVars, vgrdaction) ->
                                    // There is a true dependency between the two grdactions
                                    //  we store an inverse edge in the graph so that topological 
                                    //  sorting using DFS produces a list in the correct order.
                                    if (rdVars.Contains(currentWrVar)) then
                                        startGuardedActions := (!startGuardedActions).Remove(currentgAction)
                                        Utils.AddToAdjList((vgrdaction, currentgAction), depGraph)

                                    )
                            )
        // End of building true dependency graph

        let orderGrdAction = Utils.TopologicalSort(Set.toList !startGuardedActions, depGraph)
        orderGrdAction
            |> List.iter(fun (guard, action) ->
                                        let condition = SysMocDefs.SynthesizeBoolExp (guard, _portNameMap)
                                        let ifbody = SysMocDefs.SynthesizeAction(action, _portNameMap, Some(_eventOutputVars), ActionType.Immediate) 
                                        bodyWriter.Write(SysMocDefs.GenSysCIfClause(condition,ifbody)))      
        ()                 


    let GenerateDelayedOutputActionText(delayOutActions: Actions.GrdAction list, bodyWriter: StringWriter) =
        let parsedGrdActions = Utils.ParseVariablesOfGrdActions(delayOutActions)
        let depGraph = new Dictionary<GrdAction, GrdAction list>()
        let startGuardedActions = ref (Set.ofList(delayOutActions))
               
        // Build anti-dependency graph (inversed) 
        // Assuming that no guarded action appears twice in the action list
        parsedGrdActions
            |> List.iter(fun (currentWrVar, currentRdVars, currentgAction) ->                                 
                            parsedGrdActions
                                |> List.iter( fun (wrVar, rdVars, vgrdaction) ->
                                    // There is an anti-dependency (WAR) between the two grdactions
                                    //   reading action should be placed before writing action.
                                    if ((currentgAction <> vgrdaction) && (rdVars.Contains(currentWrVar))) then
                                        startGuardedActions := (!startGuardedActions).Remove(vgrdaction)
                                        Utils.AddToAdjList((currentgAction, vgrdaction),depGraph)                                            
                                    )
                            )
        // End of building dependency graph

        let orderGrdAction = Utils.TopologicalSort(Set.toList !startGuardedActions, depGraph)
        orderGrdAction
            |> List.iter(fun (guard, action) ->
                                        let condition = SysMocDefs.SynthesizeBoolExp (guard, _portNameMap)
                                        let ifbody = SysMocDefs.SynthesizeAction(action, _portNameMap, Some(_eventOutputVars), ActionType.Delayed) 
                                        bodyWriter.Write(SysMocDefs.GenSysCIfClause(condition,ifbody)))      
        ()                 


    // A constructor for the case that set detached output ports is empty.            
    new (synEfsm:Efsm) = ActorSynthesizer(synEfsm, Set.ofList([]))

    // Property to Get/Set default clk period
    member this.ClkPeriod
        with get() =  _defaultClk
        and set(period) = _defaultClk <- period


    // Generates text of transition definitions and corresponding guard definitions.
    member private this.GenerateTransitionsAndGuards(state:EFSMState, transitions:EFSMTransition list, inputPortGuards:string, outputPortGuards:string) =
        if not (transitions.IsEmpty) then
            let initial_transition =  ref (true)
            let initial_text =    "   " + SysMocDefs.GetStateName(state) + @" =  TILL(ev) >>"
            _transitionsDefs.WriteLine()
            transitions 
                |> List.iter (fun current -> 

                    if (!initial_transition) then
                        initial_transition := false
                        _transitionsDefs.Write (initial_text)
                    else
                        _transitionsDefs.Write(" | TILL(ev) >> ")

                    if (current.Guard = (Expressions.BoolConst (true))) then  

                        let modifiedInputGuards = 
                            if not(inputPortGuards.Length = 0) then     
                                inputPortGuards + ">>"
                            else 
                                inputPortGuards
                                             
                        let trantext = SysMocDefs.GenTransitionText(
                                            SysMocDefs.GetStateName state,
                                            modifiedInputGuards,
                                            outputPortGuards,
                                            synEfsm.Name+"::"+ SysMocDefs.GetActionName(state),
                                            SysMocDefs.GetStateName(current.NextState))
                        _transitionsDefs.Write(trantext)
                    else
                        let guardName = SysMocDefs.GetTransitionGuardName(state, current.NextState) 

                        let combinedGuards = 
                            if not(inputPortGuards.Length = 0) then     
                                "(" + inputPortGuards + "&& (GUARD (" 
                                                + synEfsm.Name + "::"
                                                + guardName  + ")))>>"
                            else 
                                "(GUARD (" + synEfsm.Name + "::"
                                                + guardName  + "))>>"


                        _guardDefs.Write(SysMocDefs.GenGuardText(guardName, SysMocDefs.SynthesizeBoolExp(current.Guard, _portNameMap))) 
                        
                        let trantext = SysMocDefs.GenTransitionText(
                                            SysMocDefs.GetStateName state,
                                            combinedGuards,
                                            outputPortGuards,
                                            synEfsm.Name+"::"+ SysMocDefs.GetActionName(state),
                                            SysMocDefs.GetStateName(current.NextState))
                        _transitionsDefs.Write(trantext))
            _transitionsDefs.Write(";")
            _transitionsDefs.WriteLine()

        ()


    // Generates text of actor action corresponding to the dataGrdAction of a given state. 
    member private this.GenerateActorAction(state:EFSMState) =

        if not(Efsm.IsFinalState state) then
       
            let dataActions = synEfsm.Graph.GetDataGrdActions(state)
       
            let bodyWriter = new StringWriter()

            
            // Note that we support only assignemnt actions, other types of actions are removed 
            //  in the following step.
               
            // Immediate DGA are topologically sorted and synthesized seperately from delayed DGAs.
            let (immediateActions, delayedActions) = Utils.SplitDataGrdActions dataActions
            
            // First: preamble of actor action is synthesized
            // This part has been shared between different actions in a seperate inline void.
            bodyWriter.WriteLine("    // Assigning delayed values and handling reaction to absence for event variables");
            bodyWriter.WriteLine("    ReactionToAbsence();");

            // Second: immediate actions are synthesized
            bodyWriter.WriteLine("    // Generating immediate guarded actions.")
            if not(immediateActions.IsEmpty) then
                GenerateImmediateActionText(immediateActions, bodyWriter)        
            
            // Third: Reset the next flags and propagte output port values.
            bodyWriter.WriteLine("    // Resetting next flags")
            bodyWriter.WriteLine("    ResetNextFlags();");
            
            bodyWriter.WriteLine("    // Propagate output values")
            bodyWriter.WriteLine("    PropagateOutput();");
 
            // DGA on local variables are seperated from DGAs on output variables.
            let (delayedLocalVarActions, delayedOutVarActions) = SplitDelayedDataGrdAction(delayedActions)

            // Fourth: Delayed actions of local variables is generated
            //    Note that local variable values has to be preserved for checking condition at the next reaction
            //    therefore, these delayed values are assigned to the corresponding carry variable of each local variable.
    
            bodyWriter.WriteLine("    // Generating delayed actions of local variables.")
            delayedLocalVarActions
                |> List.iter(fun (guard, action) ->
                                            let condition = SysMocDefs.SynthesizeBoolExp (guard, _portNameMap)
                                            let ifbody = SysMocDefs.SynthesizeActionLhsRewrite(action, _portNameMap, _delayedLocalVarMap, None)                                              
                                            bodyWriter.Write(SysMocDefs.GenSysCIfClause(condition,ifbody)))      
        
            // Fifth: finally the delayed guarded actions assigning to output variables are generated.
            bodyWriter.WriteLine()
            bodyWriter.Write("    // Generating delayed guarded actions of output variables.")
            if not(delayedOutVarActions.IsEmpty) then
                GenerateDelayedOutputActionText(delayedOutVarActions, bodyWriter)
                                                                       
            _actionDefs.Write(SysMocDefs.GenActionText(SysMocDefs.GetActionName(state), bodyWriter.ToString()))
                                        
        ()

    // Initializes internal contructs of the actor instance
    //   which allows it to be synthesized mutliple times with Synthesize() method.

    member this.Initialize() =

        // Due to synchronous MoC, an actor action can't fire until there is 
        //   a valid token on all input ports AND there is a one token space on 
        //   all output ports. This function build the corresponding condition text.

        let rec BuildPortGuard(portNames: Names.QName list) = 
            match portNames with
            |head::tail -> if (tail.IsEmpty) then
                                (head.ToString()+ @"(1)")
                            else
                                (head.ToString()+ @"(1) && " + BuildPortGuard(tail))
            | [] -> ""
        
        // Guard text that checks that a value is availalbe on all input ports.  
        //  reactions need to consume tokens from each input port.
        let inputPortGuards = 
            if synEfsm.InputPorts.Length = 0 then 
                "" 
            else 
                let ports = synEfsm.InputPorts|> List.map(fun (x,y) -> x)
                "(" + BuildPortGuard(ports) + ")" 

        // Guard text that checks that there is one token space on all  output ports. 
        //   reactions need to produce a token on each output port.
        let outputPortGuards = 
            if synEfsm.OutputPorts.Length = 0 then 
                "" 
            else 
                let ports = synEfsm.OutputPorts
                                |> List.filter( fun (qname,decl) -> not(detachedOutputPorts.Contains(qname)))
                                |> List.map(fun (qname,decl) -> qname)
                if ports.Length = 0 then
                    ""
                else
                    "(" + BuildPortGuard(ports) + ")>>"

        let mutable stateEnumerator = synEfsm.Graph.GetEnumerator()        
        // Iterates through all states in the Efsm graph.
        while stateEnumerator.MoveNext() do
            let (currentState, transitions) = stateEnumerator.Current.Value
            
            // Generates an actor action text corresponding to attached DGAs of an EFSM state.
            this.GenerateActorAction(currentState)

            //  Generates transitions and transition gurads text.
            this.GenerateTransitionsAndGuards(currentState, transitions, inputPortGuards, outputPortGuards)                  

        ()


    // Synthesizes actor instance to a string representing corresponding SysteMoC actor defintion
    //   Prerequisite: initialization of the instance.
        
    member this.Synthesize() =
        SysMocDefs.GenActorText
                (synEfsm.Name
                , this.ClkPeriod.ToString()
                , _inputPortDecl+_outPortDecl
                , _localDecl
                , _stateDecl
                , _local_default_vals
                , SysMocDefs.GetStateName (synEfsm.Graph.StartState)
                , _transitionsDefs.ToString()
                , _genActorActionPreamble
                , _reset_next_flag_vals
                , _actorActionPropagteOutput
                , _actionDefs.ToString()
                , _guardDefs.ToString())


