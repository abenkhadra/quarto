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
open Averest.Core.Names
open Averest.Core.Actions
open System.Collections.Generic

open System.IO

type AuxName =
    | Self 
    | Carry 
    | NextFlag 

type ActionType =
    | Immediate
    | Delayed
    
type SysMocDefs() =


    static member IsBasicType (qtype:Types.QType) =
        match qtype with
        |Types.Qbool |Types.Qnat (_) |Types.Qint (_) |Types.Qreal (_)|Types.Qbtv(_) -> true
        | (_) ->  false

    static member GetVarName(qname:Names.QName) =
        ((((qname.ToString()).Replace('@', '_')).Replace('.','_')).Replace('<', '_')).Replace('>', '_')

    static member GetCarryVarName(qname:Names.QName) =
        SysMocDefs.GetVarName(qname) + "_carry"

    // Returns the name of the nextflag variable corresponding to the given variable.
    static member GetNextFlagVar(qname:Names.QName) =
        (SysMocDefs.GetVarName(qname) + "_nextflag")

    static member GetVarName(qname:Names.QName, auxVar:AuxName) =
        match auxVar with
        | AuxName.Self -> SysMocDefs.GetVarName(qname)
        | AuxName.Carry -> SysMocDefs.GetCarryVarName(qname)
        | AuxName.NextFlag -> SysMocDefs.GetNextFlagVar(qname)


    static member GetPortVar(qname:Names.QName) =
        SysMocDefs.GetVarName(qname)+"[0]"

    static member GetSysCTypeName(inType:Types.QType) =
        match inType with
        |Types.Qbool -> "bool"
        |Types.Qnat (_) -> "unsigned long"
        |Types.Qint (_) -> "long"
        |Types.Qreal (_) -> "double"
        |Types.Qbtv (size) ->
            if size.IsSome then
                "sc_bv<" +  size.Value.ToString() + ">"
            else
                failwith "GenSysCType: unbounded bitvectors are not supported"  
        | Types.Qarr(_, qtype) -> (SysMocDefs.GetSysCTypeName(qtype))
        | Types.Qtup(typelist) -> (DynamicDataTypes.GenTupleTypeName (typelist))

    // Generates a declaration of a local variable.
    static member GenSysCDecl(qname:Names.QName, inType: Types.QType, auxVar: AuxName) =       
        if SysMocDefs.IsBasicType(inType) then
            let var = SysMocDefs.GetVarName(qname, auxVar)

            if (auxVar = AuxName.NextFlag) then
                // generate a declaration for a next flag
                (SysMocDefs.GetSysCTypeName(Types.Qbool) + " " + var +  ";")

            else
                // generate a declaration for a carry or main variable
                (SysMocDefs.GetSysCTypeName(inType) + " " + var +  ";")

        else 
            (SysMocDefs.GenSysCDeclCompoundType(qname, inType, auxVar))           

    static member private GenSysCDeclCompoundType(qname:Names.QName, inType: Types.QType, auxVar: AuxName) =
        match inType with
        | Types.Qtup (typelist) ->
            let var = SysMocDefs.GetVarName(qname, auxVar)

            if (auxVar = AuxName.NextFlag) then
                
                // generate a declaration for a next flag
                (SysMocDefs.GetSysCTypeName(Types.Qbool) + " " + var + "[" + typelist.Length.ToString() + "];")

            else
                // generate a declaration for a carry or main variable
                (SysMocDefs.GetSysCTypeName(inType) + " " + var +  ";")

        | Types.Qarr (length, itemType) ->
            if SysMocDefs.IsBasicType(itemType) then

                let var = SysMocDefs.GetVarName(qname, auxVar)

                if (auxVar = AuxName.NextFlag) then
                    (SysMocDefs.GetSysCTypeName(Types.Qbool) + " " + var + "[" + length.ToString() + "];")    
                else
                    (SysMocDefs.GetSysCTypeName(itemType) + " " + var + "[" + length.ToString() + "];")    

            else
                failwith "GenSysCDeclCompoundType: arrays of compunds is not supported "    
                
        | (_) -> failwith "GenSysCDeclCompoundType: type unsupported"
    

    static member GetDefaultValue(inType: Types.QType) =
        match inType with
        |Types.Qbool -> "false"
        |Types.Qnat (_) | Types.Qint (_) -> "0"
        |Types.Qreal (_) -> "0.0"
        |Types.Qbtv (_) -> "0"
        |other -> failwith "GetDefaultValue: type is not a basic type"

    static member GenSetDefaultVal(qname:Names.QName, inType: Types.QType, auxVar: AuxName) =
        match inType with
        |Types.Qbool -> 
            SysMocDefs.GetVarName(qname, auxVar) + " = false;" 
        |Types.Qnat (_) | Types.Qint (_) -> 
            if (auxVar = AuxName.NextFlag) then
                SysMocDefs.GetVarName(qname, auxVar) + " = false;"    
            else 
                SysMocDefs.GetVarName(qname, auxVar) + " = 0;" 

        |Types.Qreal (_) -> 
            if (auxVar = AuxName.NextFlag) then
                SysMocDefs.GetVarName(qname, auxVar) + " = false;"    
            else         
                SysMocDefs.GetVarName(qname, auxVar) + " = 0.0;" 
        |Types.Qbtv (size) ->
            if size.IsNone then failwith "GenSetDefaultVal: unbounded bitvictors are not supported"

            if (auxVar = AuxName.NextFlag) then
                SysMocDefs.GetVarName(qname, auxVar) + " = false;"    
            else         
                SysMocDefs.GetVarName(qname, auxVar) + " = 0;" 
            
        |Types.Qarr (size, itemType) ->
            let arrayName = SysMocDefs.GetVarName(qname, auxVar)
            if (auxVar = AuxName.NextFlag) then           
                let loopbody = "    " + arrayName + "[i] = false;"    
                SysMocDefs.GenSysCIncreasingForLoop(size, loopbody)  
            else         
                let loopbody = "    " + arrayName + "[i] = " + SysMocDefs.GetDefaultValue(itemType) + ";"    
                SysMocDefs.GenSysCIncreasingForLoop(size, loopbody)  

        | Types.Qtup (typelist) -> 
            
            let tupleName = SysMocDefs.GetVarName(qname, auxVar)
            if (auxVar = AuxName.NextFlag) then       
                // An array of boolean next flags is set to its default values.    
                let loopbody = "    " + tupleName + "[i] = false;"    
                (SysMocDefs.GenSysCIncreasingForLoop(typelist.Length, loopbody)) 

            else
                let definitionBody = new StringWriter()
                let count = ref(0)
                definitionBody.WriteLine()
                definitionBody.Write("// Tuple " + tupleName + " is set to its default values")
                definitionBody.WriteLine()
                definitionBody.Write("    ")
                typelist|> List.iter (fun (itemtype) ->
                    definitionBody.Write(DynamicDataTypes.GetTupleItemDefName(tupleName, count.Value) + " = " + SysMocDefs.GetDefaultValue(itemtype) + "; ")
                    count:= (count.Value) + 1 )
                (definitionBody.ToString())
                
    
    static member GenSetNextFlag (qname:Names.QName, inType:Types.QType, index:int option) =
        if SysMocDefs.IsBasicType(inType) then
            (SysMocDefs.GetNextFlagVar(qname) + "= true;")
        else
        match inType with
        |Types.Qarr (size, itemType) ->
            (SysMocDefs.GetNextFlagVar(qname) + "[" + index.Value.ToString() + "]= true;")
        | Types.Qtup(_) ->
            (SysMocDefs.GetNextFlagVar(qname) + "[" + index.Value.ToString() + "]= true;")

        | (_) -> ""
        
    static member GenUnsetNextFlag (qname:Names.QName, inType:Types.QType, index:int option) =
        if SysMocDefs.IsBasicType(inType) then
            (SysMocDefs.GetNextFlagVar(qname) + "= false;")
        else
        match inType with
        |Types.Qarr (size, itemType) ->
            (SysMocDefs.GetNextFlagVar(qname) + "[" + index.Value.ToString() + "]= false;")
        | Types.Qtup(_) ->
            (SysMocDefs.GetNextFlagVar(qname) + "[" + index.Value.ToString() + "]= false;")

        | (_) -> ""

    // Handy abbreviation for the two calls
    static member GenCarryVarWithNextFlagDecl(qname:Names.QName, inType: Types.QType) =
            (SysMocDefs.GenSysCDecl(qname, inType, AuxName.Carry) + "  " + SysMocDefs.GenSysCDecl(qname, inType, AuxName.NextFlag))
   
    // Handy abbreaviation for the three different calls.
    static member GenSysCDeclWithCarryAndNextFlag(qname:Names.QName, inType: Types.QType) =
        (SysMocDefs.GenSysCDecl(qname, inType, AuxName.Self) + "  " 
        + SysMocDefs.GenCarryVarWithNextFlagDecl(qname, inType))
        
            
    static member GenSysCIfClause(condition:string, ifbody:string) =
        @"
    if ("+ condition + @")
    {
       " + ifbody + @"
    }"


    static member GenSysCIfThenElseClause(condition:string, ifbody:string, elsebody:string) =
        @"
    if ("+ condition + @")
    {
    " + ifbody + @"
    }else{ 

    " + elsebody + @"
    }"

    // pre-requisite, the loop index in the loop body should be 'i'
    static member GenSysCIncreasingForLoop(iterationlimit: int, loopBody:string) =
        @"
    for (int i = 0; i < "+ iterationlimit.ToString() + @"; i++)
    {
       " + loopBody + @"
    }"

    static member GenActionText (name:string, body:string) =
        @"
   void " + name + @"() {
      "+ body + @"
      ev.reset();     
   }
"
    static member GenGuardText (name:string, body:string) =
        @"
   bool " + name + @"() const   
      {  return ("+ body + @") ;}
"

    static member GenTransitionText (currentState:string
                , inputGuards:string
                , outputGuard:string
                , action:string
                , nextState:string) =
        @"
    " + inputGuards + @"
    " + outputGuard + @" 
    CALL(" + action + @") >> " + nextState
      
    static member GetStateName(state:EFSMState) =
        ("state_"+ state.Id.ToString()) 

    static member GetActionName(state:EFSMState) =
        ("action_" + SysMocDefs.GetStateName(state))

    static member GetTransitionGuardName(state:EFSMState, nextstate:EFSMState) =
        ("guard_" + state.Id.ToString()+"_to_"+ nextstate.Id.ToString())

    static member GetDummyStateName =
        ("state_dummy")

    // A code generation template for the synthesized header.
    static member GenFileHeaderText =
        @"
/*
*  This program source is automatically generated by aif2sysmoc tool.
*  Part of work done at Embedded Systems Group, Computer Science department, TU Kaiserslautern.
*
*  2013, Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
*/

#include <iostream>
#include <systemoc/smoc_event.hpp>
#include <systemoc/smoc_port.hpp>
#include <systemoc/smoc_fifo.hpp>
#include <systemoc/smoc_node_types.hpp>
#include <systemoc/smoc_expr.hpp>

#include <cmath>
#include <cassert>
#include <cstdlib> // for atoi

using namespace std; 

"

 
    // A code-generation template for Elastic Buffer.
    static member GenElasticBufferText 
            ( name:string
//            , portType:string
            , clk:string) = 
        @"
// Class template of Elastic Buffer
template <typename DATATYPE>
class " + name+ @" : public smoc_actor {
    SC_HAS_PROCESS(" + name+ @");

private:
    smoc_firing_state buffer_empty;
    smoc_firing_state buffer_full;

    smoc_event ev;
    sc_core::sc_clock clk;

    DATATYPE carry;

	void buffer_empty_action() {
        carry = in[0];
        //std::cout << std::boolalpha <<""@""<<sc_core::sc_time_stamp() << "" - EB:"" << name()  << "" BE -> "" << carry << std::endl;
	    ev.reset();
	}

	void buffer_forward_action() {
       std::cout << std::boolalpha << ""@""<<sc_core::sc_time_stamp() << "" - EB:"" << name()  << "" BF -> "" << carry << std::endl;
       out[0] = carry;
	   ev.reset();
	}

	void buffer_store_forward_action() {
       std::cout << std::boolalpha << ""@""<<sc_core::sc_time_stamp() << "" - EB:"" << name()  << "" SF -> "" << carry << std::endl;
       out[0] = carry;
       carry = in[0];
	   ev.reset();
	}

    void notifier() {
	    ev.notify();
	}

public:
    smoc_port_out< DATATYPE > out;
    smoc_port_in< DATATYPE > in;

    "    + name+ @"(sc_module_name name)
    : smoc_actor(name, buffer_empty), clk(""clk"", " + clk+ @", sc_core::SC_NS)
    {
        //carry = 0;

		buffer_empty =
		TILL(ev)
		>> in(1)
		>> CALL(" + name + @"::buffer_empty_action)
		>> buffer_full;

		buffer_full =
		TILL(ev)
        >> in(1)
		>> out(1)
		>> CALL(" + name + @"::buffer_store_forward_action)
		>> buffer_full |
        TILL(ev)
		>> out(1)
		>> CALL(" + name + @"::buffer_forward_action)
		>> buffer_empty;

		SC_METHOD(notifier);
		sensitive << clk.posedge_event();
		dont_initialize();
	}

};

 "
    static member GenActorDebugMsg(portdir:string, portname:string, portvar:string) =
        @"    std::cout << std::boolalpha << ""@""<<sc_core::sc_time_stamp() << "" - Actor:"" << name() << """ + portdir + @":" + portname + @" -> "" << "+ portvar + @" << std::endl; "        
               
    static member GenMainText =         
        @"

int sc_main (int argc, char **argv) {  
     smoc_top_moc<Graph> graph(""graph""); 
     sc_start();  
     return 0; 
}"

       
    // A code-generation template for SysteMoC actor.
    static member GenActorText (name:string
        , clk:string
        , port_declarations:string
        , local_declarations:string
        , state_declarations:string
        , locals_default_vals:string
        , start_state:string 
        , state_transitions:string
        , reaction_to_abs:string
        , reset_next_flags: string
        , propagate_output:string
        , action_defs:string
        , guard_defs:string) =

        @" 

class " + name+ @": public smoc_actor {
   SC_HAS_PROCESS(" + name+ @");

private:
    //  Generated local declarations, carry and flag variables 
    "    + local_declarations + @"

    //  Generated state declarations
    "    + state_declarations + @"

    //  Action definitions, guarded actions of each state correspond to a transition action
    inline void ReactionToAbsence(){ 
    "    + reaction_to_abs    + @"   
    }
    inline void ResetNextFlags(){ 
    "    + reset_next_flags    + @"   
    }
    inline void PropagateOutput(){ 
    "    + propagate_output    + @"   
    }

    "    + action_defs        + @"

    //  Guard definition, guards on state transitions.
    "    + guard_defs        + @"
    
    //  Local Definitions needed for clock event handling 
    smoc_event        ev;
    sc_core::sc_clock clk;

    void notifier() {
       ev.notify();
   }

public:
   "     + port_declarations + @"

   "     + name+ @"(sc_module_name name)
      : smoc_actor(name,  " + start_state + @"), clk(""clk"", " + clk + @", sc_core::SC_NS)
    {
    // Setting locals to default values
    " + locals_default_vals + @"
    // Definitions of state transitions
    "    + state_transitions + @"
    // End of Defs

    SC_METHOD(notifier);
    sensitive << clk.posedge_event();
    dont_initialize();
   }

};

"

    static member GenActorNetworkText(actor_declarations:string
                                    , elastic_buffer_declarations:string
                                    , node_initializations:string 
                                    , port_connections:string ) =
        @"
class Graph: public smoc_graph {
protected:
  "      + actor_declarations + @"
  "      + elastic_buffer_declarations + @"
public:
  Graph(sc_module_name name)
    : smoc_graph(name)
      "  + node_initializations + @"
  {
      "  + port_connections +     @"
  }
};

  "

    static member DefaultChannelDelay
        with get() = 1


    static member GenConnectionToBufferText(srcActorName:string, outport:QName, dstbufname:string, buftype:string ) =
        @"
    connectNodePorts(" + srcActorName + "."+ SysMocDefs.GetVarName(outport) + @", " + dstbufname + @".in, smoc_fifo< " + buftype + " >(1)); "
    
    static member GenConnectionFromBufferText(srcbufname:string, dstActorName:string, inport:QName, buftype:string ) =
        @"
    connectNodePorts(" + srcbufname + ".out, " + dstActorName + @"."+ SysMocDefs.GetVarName(inport) + @", smoc_fifo< " + buftype + " >(1)); "

    static member GenConnectionBetweenBuffersText(srcname:string, dstname:string, buftype:string) =
        @"
    connectNodePorts(" + srcname + ".out, " + dstname + @".in, smoc_fifo< " + buftype + " >(1)); "
    

    static member GenAssertionStatement(condition:string) =
        ("    assert(" + condition + ");")

    //  Write conflict assertions: make sure that no two writes are done in the 
    //             same reaction e.g. delayed and an immediate action.
    static member SynthesizeWriteConflictAssertion(qname:QName, qtype:Types.QType) =
            let condition = "!(" + SysMocDefs.GetNextFlagVar(qname) + ")"
            SysMocDefs.GenAssertionStatement(condition)

    //  Write conflict assertions for arrays: make sure that no two writes are done in the 
    //             same reaction e.g. delayed and an immediate action.
    static member SynthesizeWriteConflictAssertionArray(qname:QName, qtype:Types.QType, index:string) =
            let condition = "!(" + SysMocDefs.GetNextFlagVar(qname) + "[" + index + "])"
            SysMocDefs.GenAssertionStatement(condition)

    //  Write conflict assertions for tuples: make sure that no two writes are done in the 
    //             same reaction e.g. delayed and an immediate action.
    static member SynthesizeWriteConflictAssertionTuples(qname:QName, index:string) =
            let condition = "!(" + SysMocDefs.GetNextFlagVar(qname) + "[" + index + "])"
            SysMocDefs.GenAssertionStatement(condition)


    //  Bound assertion: make sure that if a type is bounded, then the assigned value is within its bound.
    static member SynthesizeBoundAssertion(lhsVar:string, qtype:Types.QType) =

        match qtype with
        |Types.Qbool |Types.Qreal-> ""
        |Types.Qnat (bound) -> 
            if bound.IsSome then
                let boundValue = Utils.ConvertBoolListToLong(bound.Value)
                SysMocDefs.GenAssertionStatement("("  + lhsVar + ") < " + (boundValue.ToString() + "UL"))              
            else
                ""
        |Types.Qint (bound) -> 
            if bound.IsSome then
                let boundValue = Utils.ConvertBoolListToLong(bound.Value)
                SysMocDefs.GenAssertionStatement("(-" + (boundValue.ToString() + "L") + " <= (" + lhsVar + "))&&(("  + lhsVar + ") < " + (boundValue.ToString()) + "L)")               
            else
                ""
        |Types.Qbtv (bound) -> ""
        |(other) -> ""

    static member SynthesizeBoundAssertionArray(lhsVar:string, qtype:Types.QType, index:string, rhsexpr:string) =

        match qtype with
        |Types.Qarr (bound, elementtype) -> 
            match elementtype with
            |Types.Qnat (bound)  ->
                let condition = ( index + " < " + bound.ToString())
                if bound.IsSome then
                    (SysMocDefs.GenAssertionStatement(condition) + SysMocDefs.SynthesizeBoundAssertion(rhsexpr, Types.Qnat (bound)))
                else
                    (SysMocDefs.GenAssertionStatement(condition))
            | Types.Qint(bound) -> 
                let condition = ( index + " < " + bound.ToString())
                if bound.IsSome then
                    (SysMocDefs.GenAssertionStatement(condition) + SysMocDefs.SynthesizeBoundAssertion(rhsexpr, Types.Qint (bound)))
                else
                    (SysMocDefs.GenAssertionStatement(condition))

            | (other) ->
                let condition = ( index + " < " + bound.ToString())
                (SysMocDefs.GenAssertionStatement(condition))

        |(other) -> ""



    static member SynthesizeBoundAssertionArray(lhsVar:string, qtype:Types.QType, index:string) =

        match qtype with
        |Types.Qarr (bound, elementtype) -> 
            let condition = ( index + " < " + bound.ToString())
            SysMocDefs.GenAssertionStatement(condition) 
        |(other) -> ""

    static member SynthesizeBoundAssertionTuple(lhsVar:string, qtype:Types.QType, index:int) =

        match qtype with
        |Types.Qtup (typelist) -> 
            let itemtype = typelist.Item index
            // GetElement at index at make sure it satisfies bounds
            SysMocDefs.SynthesizeBoundAssertion(DynamicDataTypes.GetTupleItemDefName(lhsVar, index), itemtype)

        | (other) -> ""


    // Synthesize an action, read vars are replaced using nameRewrite map
    static member SynthesizeAction(inAction:Actions.Action
                    , nameRewrite: Map<Names.QName, string>
                    , restrictedSet: Set<QName> option
                    , atype:ActionType) =
        

        match inAction with
        | AssignNow (lhsexpr, _, expr) | AssignNxt (lhsexpr, _, expr) ->
            match lhsexpr with
            |LhsVar (qname, qtype) -> 
                let result = new StringWriter()
                // Note that only output and local variables can be Lhs of an action
                if ((restrictedSet.IsNone)|| (restrictedSet.Value.Contains(qname))) then
                    // Local variables always have a next flag
                    // Only output variables of type event have a next flag
                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertion(qname, qtype))
                    result.WriteLine()

                let lhsVar = 
                    if (nameRewrite.ContainsKey(qname)) then
                        // Writing to an output port should be done on its carry var.
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    

                result.Write (("    " + lhsVar + " = " + SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)) + ";")
                result.WriteLine()
                result.Write (SysMocDefs.SynthesizeBoundAssertion(lhsVar, qtype))

                if atype = ActionType.Delayed then
                    if ((restrictedSet.IsNone)|| (restrictedSet.Value.Contains(qname))) then
                        result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + " = true ;")
                result.ToString()

            |LhsArrAcc (innerlhsexp, natexp) -> 
                match innerlhsexp with
                |LhsVar (qname, qtype) ->
                    // Assumes that arrays can only be locals
                    let result = new StringWriter()
                    let index = "(" + SysMocDefs.SynthesizeNatExp(natexp, nameRewrite) + ")"

                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertionArray(qname, qtype, index))
                    // Assuming that arrays appear only as local vars
                    let lhsVar = SysMocDefs.GetVarName(qname)  
    
                    let rhsexpr = SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)
                    
                    result.WriteLine()
                    result.Write ("    " + lhsVar + "[" + index + "] = " + rhsexpr + ";")
                    result.WriteLine()
                    match qtype with
                    |Types.Qarr (_, Types.Qint(bound)) | Types.Qarr (_, Types.Qnat(bound)) ->
                        if bound.IsSome then
                            result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index, rhsexpr))
                        else
                            result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index))
                    | (other) ->
                        result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index))

                    if atype = ActionType.Delayed then
                       result.WriteLine()
                       result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + "[" + index + "] = true ;")
                    result.ToString()

                | (other) -> 
                    failwith "SynthesizeAction: only basic types are supported inside arrays " 

            |LhsTupAcc (innerlhsexp, index) ->
                match innerlhsexp with
                |LhsVar (qname, itemqtype) ->
                    let result = new StringWriter()

                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertionTuples(qname, index.ToString()))

                    let lhsVar = 
                        if (nameRewrite.ContainsKey(qname)) then
                            // Writing to an output port should be done on its carry var.
                            (nameRewrite.Item qname)
                        else 
                            // Writing is done to a local variable
                            (SysMocDefs.GetVarName(qname))    

                    let rhsexpr = SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)
                    
                    result.WriteLine()
                    result.Write ("    " + DynamicDataTypes.GetTupleItemDefName(lhsVar, index) + " = " + rhsexpr + ";")
                    result.WriteLine()
                    
                    result.Write(SysMocDefs.SynthesizeBoundAssertion(DynamicDataTypes.GetTupleItemDefName(lhsVar, index), itemqtype))

                    if atype = ActionType.Delayed then
                        result.WriteLine()
                        result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + "[" + index.ToString() + "] = true ;")
                    result.ToString()

                |(other) -> 
                    failwith "SynthesizeAction: only basic types are supported inside tuples " 

        | Assert (qname, boolexp) -> ("    assert(" + SysMocDefs.SynthesizeBoolExp(boolexp, nameRewrite)  + ");")
            
        |(expr) -> failwith "SynthesizeAction: unsupported expression " + expr.ToString()


    // Synthesize an action, read vars are replaced using nameRewrite map
    //  write variable is replaced using lhsNameRewrite map.
    // The action is assumed to by of type delayed here. 
    // This is an overload function.
    static member SynthesizeActionLhsRewrite(inAction:Actions.Action
                            , nameRewrite: Map<Names.QName, string>
                            , lhsNameRewrite: Map<Names.QName, string>
                            , restrictedSet: Set<QName> option) =
        SysMocDefs.SynthesizeActionLhsRewrite(inAction, nameRewrite, lhsNameRewrite, restrictedSet, ActionType.Delayed)

    // Synthesize an action, read vars are replaced using nameRewrite map
    //  write variable is replaced using lhsNameRewrite map.
    static member SynthesizeActionLhsRewrite(inAction:Actions.Action
                            , nameRewrite: Map<Names.QName, string>
                            , lhsNameRewrite: Map<Names.QName, string>
                            , restrictedSet: Set<QName> option, atype:ActionType) =

        match inAction with
        | AssignNow (lhsexpr, _, expr) | AssignNxt (lhsexpr, _, expr) ->
            match lhsexpr with
            |LhsVar (qname, qtype) -> 
                let result = new StringWriter()
                // Note that only output and local variables can be Lhs of an action
                if ((restrictedSet.IsNone)|| (restrictedSet.Value.Contains(qname))) then
                    // Local variables always have a next flag => restricted set None
                    // Only output variables of type event have a next flag => qname in restricted set
                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertion(qname, qtype))
                    result.WriteLine()

                let lhsVar = 
                    if (lhsNameRewrite.ContainsKey(qname)) then
                        // Writing is done to the carry of a local variable.
                        (lhsNameRewrite.Item qname)
                    else 
                        // Writing is done to the carry of an output variable.
                        (nameRewrite.Item qname)

                result.Write (("    " + lhsVar + " = " + SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)) + ";")
                result.WriteLine()
                result.Write (SysMocDefs.SynthesizeBoundAssertion(lhsVar, qtype))

                if atype = ActionType.Delayed then
                    if ((restrictedSet.IsNone)|| (restrictedSet.Value.Contains(qname))) then
                        result.WriteLine()
                        result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + " = true ;")
                result.ToString()

            |LhsArrAcc (innerlhsexp, natexp) -> 
                match innerlhsexp with
                |LhsVar (qname, qtype) ->
                    // Assumes that arrays can only be locals
                    let result = new StringWriter()
                    let index = "(" + SysMocDefs.SynthesizeNatExp(natexp, nameRewrite) + ")"

                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertionArray(qname, qtype, index))
                    let lhsVar = 
                        if (lhsNameRewrite.ContainsKey(qname)) then
                            // Writing is done to the carry of a local variable.
                            (lhsNameRewrite.Item qname)
                        else 
                            // Writing is done to the carry of an output variable.
                            (nameRewrite.Item qname)

                    let rhsexpr = SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)
                    
                    result.WriteLine()
                    result.Write ("    " + lhsVar + "[" + index + "] = " + rhsexpr + ";")
                    result.WriteLine()
                    match qtype with
                    |Types.Qarr (_, Types.Qint(bound)) | Types.Qarr (_, Types.Qnat(bound)) ->
                        if bound.IsSome then
                            result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index, rhsexpr))
                        else
                            result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index))
                    | (other) ->
                        result.Write (SysMocDefs.SynthesizeBoundAssertionArray(lhsVar, qtype, index))

                    if atype = ActionType.Delayed then
                        result.WriteLine()
                        result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + "[" + index + "] = true ;")
                    result.ToString()

                | (other) -> 
                    failwith "SynthesizeActionLhsRewrite: only basic types are supported inside arrays " 

            |LhsTupAcc (innerlhsexp, index) ->
                match innerlhsexp with
                |LhsVar (qname, itemqtype) ->
                    // Assumes that arrays can only be locals
                    let result = new StringWriter()

                    result.Write(SysMocDefs.SynthesizeWriteConflictAssertionTuples(qname, index.ToString()))
                    let lhsVar = 
                        if (lhsNameRewrite.ContainsKey(qname)) then
                            // Writing is done to the carry of a local variable.
                            (lhsNameRewrite.Item qname)
                        else 
                            // Writing is done to the carry of an output variable.
                            (nameRewrite.Item qname)

                    let rhsexpr = SysMocDefs.SynthesizeGenericExpression(expr, nameRewrite)
                    
                    result.WriteLine()
                    result.Write ("    " + DynamicDataTypes.GetTupleItemDefName(lhsVar, index) + " = " + rhsexpr + ";")
                    result.WriteLine()
                    
                    result.Write(SysMocDefs.SynthesizeBoundAssertion(DynamicDataTypes.GetTupleItemDefName(lhsVar, index), itemqtype))

                    if atype = ActionType.Delayed then
                        result.WriteLine()
                        result.Write ("    " + SysMocDefs.GetNextFlagVar(qname) + "[" + index.ToString() + "] = true ;")
                    result.ToString()

                |(other) -> 
                    failwith "SynthesizeActionLhsRewrite: only basic types are supported inside tuples " 

        | Assert (qname, boolexp) -> ("    assert(" + SysMocDefs.SynthesizeBoolExp(boolexp, nameRewrite)  + ");")
            
        |(expr) -> failwith "SynthesizeActionLhsRewrite: unsupported expression " + expr.ToString()

           
    static member GenReactionToAbsence(qname:Names.QName, declaration: Declarations.Decl) =
        
        match declaration.flow with
        | Declarations.Flow.Output -> 
            if declaration.storage = Declarations.Storage.Event then
                // Only event output vars need a reaction to absence handling
                //   memorrized output var values should be set in the delayed guarded 
                //   action section of actor action. Value held in the carry variable
                //   will correspond to the output var.
                match (declaration.qtype) with 
                | Types.Qbool | Types.Qnat(_) | Types.Qint(_) | Types.Qreal | Types.Qbtv(_) ->
                    let condition = "(!" + SysMocDefs.GetNextFlagVar(qname) + ")"
                    let ifbody = SysMocDefs.GenSetDefaultVal(qname, declaration.qtype, AuxName.Carry) 
                    (SysMocDefs.GenSysCIfClause(condition, ifbody))
   
                | Types.Qarr (size, itemtype) -> "" // Arrays do not appear as output variables
          
                | Types.Qtup (itemtypelist) -> 
   
                    let synthesizedRta = new StringWriter()
                    let carryName = SysMocDefs.GetCarryVarName(qname)
                    let condition = ref("")
                    let ifbody = ref("")
                    let elsebody = ref("")
                    let count = ref(0)

                    itemtypelist|> List.iter(fun (itemtype) ->
                        // Generating reaction to absence for each tuple item seperately
                        condition := ("(!" + SysMocDefs.GetNextFlagVar(qname) + "[" + count.Value.ToString() + "])")
                        ifbody := DynamicDataTypes.GetTupleItemDefName(carryName, count.Value) + " = " + SysMocDefs.GetDefaultValue(itemtype)  + ";"                
                        (synthesizedRta.Write(SysMocDefs.GenSysCIfClause(condition.Value, ifbody.Value)))
                        count:= (!count) + 1)
                           
                    (synthesizedRta.ToString()) 

            else
                "" // No reaction to absence for memorized output vars. 

        // reaction to absence and delayed value assignment for local variables
        | Declarations.Flow.LocVar ->
            match (declaration.qtype) with 
            | Types.Qbool | Types.Qnat(_) | Types.Qint(_) | Types.Qreal | Types.Qbtv(_) ->
                // Types that have only one carry and next flags variable
                let condition = SysMocDefs.GetNextFlagVar(qname) 
                let ifbody = SysMocDefs.GetVarName(qname) + " = " + SysMocDefs.GetCarryVarName(qname) + ";" 
                if (declaration.storage = Declarations.Event) then
                    let elsebody = SysMocDefs.GenSetDefaultVal(qname, declaration.qtype, AuxName.Self)
                    SysMocDefs.GenSysCIfThenElseClause(condition, ifbody, elsebody)
                else
                    (SysMocDefs.GenSysCIfClause(condition, ifbody))
   
            | Types.Qarr (size, itemtype) -> 
                // arrays have a carry and nextflag for each of their elements.
                let condition = "(" + SysMocDefs.GetNextFlagVar(qname) + "[i])"
                let varName = SysMocDefs.GetVarName(qname)
                let carryName = SysMocDefs.GetCarryVarName(qname)

                let ifbody = "    " + varName + "[i] = " + carryName + "[i];" 
                
                let loopbody = 
                    if (declaration.storage = Declarations.Event) then
                        let elsebody = "    " + varName + "[i] = " + SysMocDefs.GetDefaultValue(itemtype) + ";"    
                        (SysMocDefs.GenSysCIfThenElseClause(condition, ifbody, elsebody))
                    else
                        (SysMocDefs.GenSysCIfClause(condition, ifbody))
                       
                (SysMocDefs.GenSysCIncreasingForLoop(size, loopbody)) 
          
            | Types.Qtup (itemtypelist) -> 
                // Tuples have a carry and nextflag for each of their items.
                // nextflags are defined in an array wheras carrys are defined in another instance 
                // of the tuple struct.
                let synthesizedRta = new StringWriter()
                let varName = SysMocDefs.GetVarName(qname)
                let carryName = SysMocDefs.GetCarryVarName(qname)
                let condition = ref("")
                let ifbody = ref("")
                let elsebody = ref("")
                let count = ref(0)

                itemtypelist
                    |> List.iter(fun (itemtype) ->

                    condition := ("(" + SysMocDefs.GetNextFlagVar(qname) + "[" + count.Value.ToString() + "])")
                    ifbody := "    " + DynamicDataTypes.GetTupleItemDefName(varName, count.Value) + " = " + DynamicDataTypes.GetTupleItemDefName(carryName, count.Value)  + ";" 
                
                    if (declaration.storage = Declarations.Event) then
                        elsebody := "    " + DynamicDataTypes.GetTupleItemDefName(varName, count.Value) + " = " + SysMocDefs.GetDefaultValue(itemtype)  + ";" 
                        (synthesizedRta.Write(SysMocDefs.GenSysCIfThenElseClause(condition.Value, ifbody.Value, elsebody.Value)))
                    else
                        (synthesizedRta.Write(SysMocDefs.GenSysCIfClause(condition.Value, ifbody.Value)))

                    count:= !count + 1)
                       
                (synthesizedRta.ToString()) 

        |(other) -> "" // Declaration flows other than local and output are not of interest.
       

    // SynthesizeRealExp, uses nameRewrite to synthesize variable names.    
    static member SynthesizeRealExp( realexp:Expressions.RealExpr, nameRewrite: Map<Names.QName, string>) =
        match realexp with
        | RealVar (qname) ->
            if (nameRewrite.ContainsKey(qname)) then
                (nameRewrite.Item qname)
            else 
                (SysMocDefs.GetVarName(qname))    
                                
        | RealConst (value) ->
            value.ToString()
        | RealOfNat (value) ->
            "static_cast<double>(" + SysMocDefs.SynthesizeNatExp(value, nameRewrite) + ")"
        | RealOfInt (value) ->
            "static_cast<double>(" + SysMocDefs.SynthesizeIntExp(value, nameRewrite) + ")"
        | RealAdd (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")+(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"
        | RealSub (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")-(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"
        | RealMul (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")*(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"
        | RealDiv (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")/(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"
        | RealSin (expr) ->
            "sin("+ SysMocDefs.SynthesizeRealExp(expr,nameRewrite) + ")"
        | RealCos (expr) ->
            "cos("+ SysMocDefs.SynthesizeRealExp(expr,nameRewrite) + ")"
        | RealExp (expr1, expr2) ->
            "pow (("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + "),(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"
        | RealLog2 (expr) ->
            "log2("+ SysMocDefs.SynthesizeRealExp(expr,nameRewrite) + ")"
        | RealIte (boolexpr, expr1, expr2) ->
            "(" + SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite) + ")?(" + SysMocDefs.SynthesizeRealExp(expr1, nameRewrite) + "):(" + SysMocDefs.SynthesizeRealExp(expr2, nameRewrite) + ")"
        | RealArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                let arrName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                arrName + "[" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)  + "]"
            |(other) -> failwith "SynthesizeRealExp: array type " + arrexpr.ToString() + " unsupported"
 
        | RealTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                let tupName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (DynamicDataTypes.GetTupleItemDefName(tupName, index))

            |(other) -> failwith "SynthesizeRealExp: tuple type " + tupexpr.ToString() + " unsupported"
        | (expr) ->
            failwith "SynthesizeRealExp: Type " + expr.ToString() + " unsupported"


    // SynthesizeNatExp, uses nameRewrite to synthesize variable names.
    static member SynthesizeNatExp( natexp:Expressions.NatExpr, nameRewrite: Map<Names.QName, string> ) =
        match natexp with
        | NatVar (qname, bitlist) ->
            if (nameRewrite.ContainsKey(qname)) then
                (nameRewrite.Item qname)
            else 
                (SysMocDefs.GetVarName(qname))    
                                
        | NatConst (boollist) ->
            (NatConst (boollist)).ToString()

        | IntAbs (intexpr) ->
            "abs(" + SysMocDefs.SynthesizeIntExp(intexpr, nameRewrite) + ")"
        | NatAdd (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")+(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"
        | NatSub (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")-(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"
        | NatMul (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")*(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"
        | NatDiv (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")/(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"
        | NatMod (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")%(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"

        | NatExp (expr1, expr2) ->
            "pow (("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + "),(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"
        | NatLog2 (expr) ->
            "static_cast<unsigned int>(log2("+ SysMocDefs.SynthesizeNatExp(expr,nameRewrite) + "))"
        | NatOfBtv (btvexpr) ->
            "(" + (SysMocDefs.SynthesizeBVExp(btvexpr, nameRewrite)) + ").to_uint()"
        | NatIte (boolexpr, natexpr1, natexpr2) ->
            "(" + SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite) + ")?(" + SysMocDefs.SynthesizeNatExp(natexpr1, nameRewrite) + "):(" + SysMocDefs.SynthesizeNatExp(natexpr2, nameRewrite) + ")"
 
        | NatArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                let arrName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                arrName + "[" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)  + "]"
            |(other) -> failwith "SynthesizeNatExp: array type " + arrexpr.ToString() + " unsupported"
 
        | NatTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                let tupName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (DynamicDataTypes.GetTupleItemDefName(tupName, index))

            |(other) -> failwith "SynthesizeNatExp: tuple type " + tupexpr.ToString() + " unsupported"

        | (expr) ->
            failwith "SynthesizeNatExp: Type " + expr.ToString() + " unsupported"

    // SynthesizeIntExp, uses nameRewrite to synthesize variable names.
    static member SynthesizeIntExp( intexp:Expressions.IntExpr, nameRewrite: Map<Names.QName, string>) =
        match intexp with
        | IntVar (qname, _) ->
            if (nameRewrite.ContainsKey(qname)) then
                (nameRewrite.Item qname)
            else 
                (SysMocDefs.GetVarName(qname))    
                               
        | IntConst (boollist) ->
            (IntConst (boollist)).ToString()
        | IntOfNat (natexp) ->
            "static_cast<int>(" + SysMocDefs.SynthesizeNatExp(natexp, nameRewrite) + ")"

        | IntAdd (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")+(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"
        | IntSub (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")-(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"
        | IntMul (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")*(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"
        | IntDiv (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")/(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"
        | IntMod (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")%(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"

        | IntOfBtv (btvexpr) ->
            "(" + (SysMocDefs.SynthesizeBVExp(btvexpr, nameRewrite)) + ").to_int()"
  
        | IntIte (boolexpr, expr1, expr2) ->
            "(" + SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite) + ")?(" + SysMocDefs.SynthesizeIntExp(expr1, nameRewrite) + "):(" + SysMocDefs.SynthesizeIntExp(expr2, nameRewrite) + ")"
  
        | IntArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                let arrName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                arrName + "[" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)  + "]"
            |(other) -> failwith "SynthesizeIntExp: array type " + arrexpr.ToString() + " unsupported"
 
        | IntTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                let tupName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (DynamicDataTypes.GetTupleItemDefName(tupName, index))

            |(other) -> failwith "SynthesizeIntExp: tuple type " + tupexpr.ToString() + " unsupported"

        | (expr) ->
            failwith "SynthesizeIntExp: Type " + expr.ToString() + " unsupported"

    // SynthesizeBoolExp, uses nameRewrite to synthesize variable names.
    static member SynthesizeBoolExp( boolexp:Expressions.BoolExpr, nameRewrite: Map<Names.QName, string> ) =

        match boolexp with
        | BoolVar (qname) -> 
            if (nameRewrite.ContainsKey(qname)) then
                (nameRewrite.Item qname)
            else 
                (SysMocDefs.GetVarName(qname))    
                                
        | BoolConst (boolconst) ->
            if boolconst then
                "true"
            else 
                "false"
        | BoolNeg (expr) ->
            "!(" + SysMocDefs.SynthesizeBoolExp(expr, nameRewrite) + ")"

        | BoolConj (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeBoolExp(expr1,nameRewrite) + ")&&(" + SysMocDefs.SynthesizeBoolExp(expr2,nameRewrite) + "))"

        | BoolDisj (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeBoolExp(expr1,nameRewrite) + ")||(" + SysMocDefs.SynthesizeBoolExp(expr2,nameRewrite) + "))"

        | BoolImpl (expr1, expr2) ->
            "(!("+ SysMocDefs.SynthesizeBoolExp(expr1,nameRewrite) + ")||(" + SysMocDefs.SynthesizeBoolExp(expr2,nameRewrite) + "))"

        | BoolEqu (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeBoolExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeBoolExp(expr2,nameRewrite) + "))"

        | BtvEqu  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeBVExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeBVExp(expr2,nameRewrite) + "))"

        // Thanks to using C++ structs, the equality of two structs is overiddin by te compiler.
        | TupEqu  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeTupExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeTupExp(expr2,nameRewrite) + "))"
  
        | NatEqu (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"

        | NatLes  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")<(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"

        | NatLeq  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeNatExp(expr1,nameRewrite) + ")<=(" + SysMocDefs.SynthesizeNatExp(expr2,nameRewrite) + "))"

        | IntEqu  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"

        | IntLes  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")<(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"

        | IntLeq  (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeIntExp(expr1,nameRewrite) + ")<=(" + SysMocDefs.SynthesizeIntExp(expr2,nameRewrite) + "))"

        | RealEqu (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")==(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"

        | RealLes (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")<(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"

        | RealLeq (expr1, expr2) ->
            "(("+ SysMocDefs.SynthesizeRealExp(expr1,nameRewrite) + ")<=(" + SysMocDefs.SynthesizeRealExp(expr2,nameRewrite) + "))"

        | BoolBitOfBtv (btvexpr, index) ->
            ("(" + SysMocDefs.SynthesizeBVExp(btvexpr, nameRewrite) + ")[" + index.ToString()  + "]")
//            match btvexpr with
//            | BtvVar (qname, _) ->
//                let bvName = 
//                    if (nameRewrite.ContainsKey(qname)) then
//                        (nameRewrite.Item qname)
//                    else 
//                        (SysMocDefs.GetVarName(qname))    
//                (bvName + "[" + index.ToString()  + "]")
//            |(other) -> failwith "SynthesizeBoolExp: Bitvictor type " + btvexpr.ToString() + " unsupported"

        | BoolIte (boolexpr, expr1, expr2) ->
            "(" + SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite) + ")?(" + SysMocDefs.SynthesizeBoolExp(expr1, nameRewrite) + "):(" + SysMocDefs.SynthesizeBoolExp(expr2, nameRewrite) + ")"
 
        | BoolArrAcc  (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                let arrName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (arrName + "[" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)  + "]")
            |(other) -> failwith "SynthesizeBoolExp: array type " + arrexpr.ToString() + " unsupported"
 
        | BoolTupAcc  (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                let tupName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (DynamicDataTypes.GetTupleItemDefName(tupName, index))

            |(other) -> "SynthesizeBoolExp: tuple type " + tupexpr.ToString() + " unsupported"
        | (expr) ->
            failwith "SynthesizeBoolExp: Type " + expr.ToString() + " unsupported"



    static member SynthesizeBVExp(inexpr:Expressions.BtvExpr , nameRewrite: Map<Names.QName, string>) =
        match inexpr with
        | BtvVar (qname, _ ) -> 
            if (nameRewrite.ContainsKey(qname)) then
                (nameRewrite.Item qname)
            else 
                (SysMocDefs.GetVarName(qname))   
        
        | BtvConst (boollist) ->
            "sc_bv<" + boollist.Length.ToString() + ">(" + (Utils.ConvertBoolListToNat(boollist)).ToString() + "U)"
        
        | BtvOfNat (natexpr, size) ->
            ("sc_bv<" + size.ToString() + ">(" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)) + ")"
//            SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)
        
        | BtvOfInt (intexpr, size) ->
//            SysMocDefs.SynthesizeIntExp(intexpr, nameRewrite)
            ("sc_bv<" + size.ToString() + ">(" + SysMocDefs.SynthesizeIntExp(intexpr, nameRewrite)) + ")"
       
        | BtvNeg (btvexpr) ->
            match btvexpr with
            | BtvEqv (expr1, expr2) -> 
                ("(" + SysMocDefs.SynthesizeBVExp (expr1, nameRewrite) + ")^(" + SysMocDefs.SynthesizeBVExp (expr2, nameRewrite) + ")")
            | (other) -> ("~(" + SysMocDefs.SynthesizeBVExp (btvexpr, nameRewrite) + ")")

        | BtvConj  (btvexpr1, btvexpr2) ->
            ("(" + SysMocDefs.SynthesizeBVExp (btvexpr1, nameRewrite) + ")&(" + SysMocDefs.SynthesizeBVExp (btvexpr2, nameRewrite) + ")")

        | BtvDisj (btvexpr1, btvexpr2) ->
            ("(" + SysMocDefs.SynthesizeBVExp (btvexpr1, nameRewrite) + ")|(" + SysMocDefs.SynthesizeBVExp (btvexpr2, nameRewrite) + ")")
 
        | BtvImpl (btvexpr1, btvexpr2) ->
            ("(~(" + SysMocDefs.SynthesizeBVExp (btvexpr1, nameRewrite) + "))|(" + SysMocDefs.SynthesizeBVExp (btvexpr2, nameRewrite) + ")")

        | BtvEqv (btvexpr1, btvexpr2) ->
            ("~((" + SysMocDefs.SynthesizeBVExp (btvexpr1, nameRewrite) + ")^(" + SysMocDefs.SynthesizeBVExp (btvexpr2, nameRewrite) + "))")

        | BtvAppend (btvexpr1, btvexpr2) ->
            ("((" + SysMocDefs.SynthesizeBVExp (btvexpr1, nameRewrite) + "), (" + SysMocDefs.SynthesizeBVExp (btvexpr2, nameRewrite) + "))")

        | BtvSegment (btvexpr, high, low) ->
            ("(" + SysMocDefs.SynthesizeBVExp (btvexpr, nameRewrite) + ").range(" + high.ToString() + "," + low.ToString() + ")")

        | BtvReverse (btvexpr) ->
            ("(" + SysMocDefs.SynthesizeBVExp (btvexpr, nameRewrite) + ").reverse()")

        | BtvIte (boolexpr, expr1, expr2) ->
            "(" + SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite) + ")?(" + SysMocDefs.SynthesizeBVExp(expr1, nameRewrite) + "):(" + SysMocDefs.SynthesizeBVExp(expr2, nameRewrite) + ")"
        
        | BtvArrAcc (arrexpr, natexpr) ->
            match arrexpr with
            | ArrVar (qname, _) ->
                let arrName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (arrName + "[" + SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)  + "]")
            |(other) -> failwith "SynthesizeBVExp: array type " + arrexpr.ToString() + " unsupported"
 
        | BtvTupAcc (tupexpr, index) ->
            match tupexpr with
            | TupVar (qname, _) ->
                let tupName = 
                    if (nameRewrite.ContainsKey(qname)) then
                        (nameRewrite.Item qname)
                    else 
                        (SysMocDefs.GetVarName(qname))    
                (DynamicDataTypes.GetTupleItemDefName(tupName, index))

            |(other) -> "SynthesizeBVExp: tuple type " + tupexpr.ToString() + " unsupported"
 
        |(other) ->
            failwith "SynthesizeBVExp: Type " + other.ToString() + " unsupported"


    static member SynthesizeArrExp(inExpr:Expressions.ArrExpr, nameRewrite: Map<Names.QName, string>) =
        failwith "SynthesizeArrExp: expression " + inExpr.ToString() + " is unsupported"

    static member SynthesizeTupExp(inExpr:Expressions.TupExpr, nameRewrite: Map<Names.QName, string>) =
        failwith "SynthesizeTupExp: expression " + inExpr.ToString() + " is unsupported"

    // SynthesizeGenericExpression, uses nameRewrite to synthesize variable names.
    static member SynthesizeGenericExpression(inExpr:Expressions.Expr, nameRewrite: Map<Names.QName, string>) =
        match inExpr with
        | Ebool (boolexpr) ->
            SysMocDefs.SynthesizeBoolExp(boolexpr, nameRewrite)
        | Enat  (natexpr) ->
            SysMocDefs.SynthesizeNatExp(natexpr, nameRewrite)
        | Eint (intexpr) ->
            SysMocDefs.SynthesizeIntExp(intexpr, nameRewrite)
        | Ereal (realexpr) ->
            SysMocDefs.SynthesizeRealExp(realexpr, nameRewrite)
        | Ebtv (bvexpr) ->
            SysMocDefs.SynthesizeBVExp (bvexpr, nameRewrite)
        | Earr (arrexpr) ->
            SysMocDefs.SynthesizeArrExp(arrexpr, nameRewrite)
        | Etup (tupexpr) ->
            SysMocDefs.SynthesizeTupExp(tupexpr, nameRewrite)
        | (expr) ->
            failwith "SynthesizeGenericExpression: Type " + expr.ToString() + " unsupported"
