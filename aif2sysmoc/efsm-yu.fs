(* --------------------------------------------------------------------------------- *)
(* This module takes the control flow guarded actions and dataflow  guarded actions  *)
(* and generates the EFSM. It takes two assumptions:                                 *)
(* 1. The Control-flow guarded actions should be grouped so that for each assignment *)
(*    of the next location variable, there is exactly one guarded action, except for *)
(*    the start location. The start location's truth value is true only at the start *)
(*    of the program. For all the following states its truth value should be false.  *)
(* 2. The global variable table stores the (index * string) pairs. All location and  *)
(*    data variables as well as abbreviated variables are stored in this table. When *)
(*    starting the EFSM generation, the global table should contain all variables in *)
(*    the given control-flow and dataflow guarded actions.                           *)
(* --------------------------------------------------------------------------------- *)

namespace EFSMPack

(* reference of the Averest dlls *)
//#r @"E:\Lektion\Masterarbeit\Averest-new-2\averest\Averest.Core.dll"
//#r @"E:\Lektion\Masterarbeit\Averest-new-2\averest\Averest.Transformation.dll"
//#r @"E:\Lektion\Masterarbeit\Averest-new-2\averest\Averest.Synthesis.dll"
//#r @"E:\Lektion\Masterarbeit\FSharp-2.0.0.0\BDD.dll"

module EFSM =

(* open the needed modules *)
open Averest.Core
open Averest.Core.Expressions
open Averest.Core.Evaluation
open Averest.Transformation
open Averest.Transformation.Utils
open Averest.Core.Names
open Averest.Core.Types
open Averest.Core.Actions
open Averest.Core.AIF
open Averest.Core.AIFIO
open Averest.Core.Declarations
open Averest.Core.Printer
open BDDPack.BDD

open System.Collections.Generic


(* exceptions *)
let ExepNotAbbrExpr = "Expr is not abbreviated"
let ExepNameNotExist = "ERROR NAME NOT EXISTED"
let ExepNotCGA = "Not a control flow guarded action"
let ExepNotGA = "Not a guarded action"
let ExepNotProp = "Not a propositional formula"
let ExepNoInitBvr = "Init Behavior already eliminated"
let ExepNotBoolVal = "Not a value of Boolean constant"



(* ------------------------------------------------------------ *)
(*                      state type definition                   *)
(* ------------------------------------------------------------ *)

(* assume the index of the location variable "start" *)
(* in the global variable table is 0.                *)
//let IndexSt = 0

type EFSMState = (QName * BoolValue) Set

type EFSMStateTrans = EFSMState * ((EFSMState * BoolExpr) list)

type EFSMStateEncoding = {state: QName; numberofbv: int; encoding: Map<EFSMState, BtvExpr>;}

(* type definition for graph generation (for graphviz) *)

type StateGraphVertex = EFSMState

type StateGraphEdge = BoolExpr

type StateGraph = Graph<StateGraphVertex,StateGraphEdge>

(* ------------------------------------------------------- *)
(*           The Abbreviation Table of BoolExpr            *)
(* ------------------------------------------------------- *)
(* The abbreviation table stors (expr, name) pairs. For    *)
(* each expression there is a unique name for abbreviation *)
(* Thus it maintains a bijection relation between the expr *)
(* and the abbreviative names.                             *)

let abbrVarTable = new Dictionary<BoolExpr, QName>()


(* A backward table is needed for transforming *)
(* the abbreviated formula's non-boolean sub-  *)
(* expressions back to its original form.      *)

let revAbbrVarTable = new Dictionary<QName, BoolExpr>()


(* Generate pure boolean formula from BoolExpr *)
(* First a name generation is needed for the   *)
(* abbreviations of the expressions. Everytime *)
(* a new expression is found, a new name is    *)
(* generated for it and the pair of expr*name  *)
(* is added to the abbreviation dictionary.    *)

(* create a new name for the abbreviated expression *)
(* the index should be length of the global table+1 *)
let NewAbbrName (tabG:Dictionary<Index, string>) = 
    let index = tabG.Count + 1 //consider exploit????
    let newname = BasicName index
    tabG.Add(index, "__abrr" + index.ToString())
    newname

(* Get the name of the abbreviated expression. *)
(* If the expression doesn't exist, a new name *)
(* will be created for the abbreviation        *)
(*!!!!
let GetAbbrVar expr (tabAbbr:Dictionary<BoolExpr, QName>) (tabRev:Dictionary<QName, BoolExpr>) (tabG:Dictionary<Index, string>) = 
    if tabAbbr.ContainsKey(expr) then tabAbbr.[expr]
    else 
        let newname = NewAbbrName tabG
        tabAbbr.Add(expr, newname)
        tabRev.Add(newname, expr)
        newname
*)
let GetAbbrVar expr (tabAbbr:Dictionary<BoolExpr, QName>) (tabRev:Dictionary<QName, BoolExpr>) = 
    if tabAbbr.ContainsKey(expr) then tabAbbr.[expr]
    else 
        let newname = NewLocalName()
        tabAbbr.Add(expr, newname)
        tabRev.Add(newname, expr)
        newname


(* Functions for the partial expression mapping.        *)
(* used for transforming a BoolExpr to its abbreviation *)
//!!!!let CsFwdBoolExpr (tabAbbr:Dictionary<BoolExpr, QName>) (tabRev:Dictionary<QName, BoolExpr>) (tabG:Dictionary<Index, string>) bexpr = 
let CsFwdBoolExpr (tabAbbr:Dictionary<BoolExpr, QName>) (tabRev:Dictionary<QName, BoolExpr>) bexpr = 
    match bexpr with
    (* None cases *)
    | BoolNeg _ | BoolConj _ | BoolDisj _ | BoolImpl _ | BoolEqu _ -> None
    (* Some cases *)
    | BoolVar var -> Some (BoolVar var)
    | BoolConst bc -> Some (BoolConst bc)
    | otherexpr
        -> Some (BoolVar (GetAbbrVar otherexpr tabAbbr tabRev))

let CsFwdBtvExpr (expr:BtvExpr) = match expr with | _ -> None
let CsFwdLhsExpr (expr:LhsExpr) = match expr with | _ -> None
let CsFwdNatExpr (expr:NatExpr) = match expr with | _ -> None
let CsFwdIntExpr (expr:IntExpr) = match expr with | _ -> None
let CsFwdRealExpr (expr:RealExpr) = match expr with | _ -> None
let CsFwdArrayExpr (expr: ArrayExpr) = match expr with | _ -> None
let CsFwdTupExpr (expr: TupExpr) = match expr with | _ -> None

let (pmapping:PartialExprMapping)  = 
    {lhs = CsFwdLhsExpr;
     bool = CsFwdBoolExpr abbrVarTable revAbbrVarTable;
     btv = CsFwdBtvExpr;
     nat = CsFwdNatExpr;
     int = CsFwdIntExpr;
     real = CsFwdRealExpr;
     array = CsFwdArrayExpr;
     tup = CsFwdTupExpr;}

(* SubtBoolExpr of type:          *)
(* function: BoolExpr -> BoolExpr *)
let SubtBoolExpr = (PartialTopDownMapping pmapping).bool


(* Functions for the partial expression mapping. *)
(* used for transforming an abbreviation back.   *)
let CsBwdBoolExpr (tabRev:Dictionary<QName, BoolExpr>) bexpr = 
    match bexpr with
    (* None cases *)
    | BoolNeg _ | BoolConj _ | BoolDisj _ | BoolImpl _ | BoolEqu _ -> None
    (* Some cases *)
    | BoolVar var -> if (tabRev.ContainsKey(var)) then Some(tabRev.[var]) else Some (BoolVar var)
    | BoolConst bc -> Some (BoolConst bc)
    | _ -> failwith ExepNotAbbrExpr 

let CsBwdBtvExpr (expr:BtvExpr) = match expr with | _ -> None
let CsBwdLhsExpr (expr:LhsExpr) = match expr with | _ -> None
let CsBwdNatExpr (expr:NatExpr) = match expr with | _ -> None
let CsBwdIntExpr (expr:IntExpr) = match expr with | _ -> None
let CsBwdRealExpr (expr:RealExpr) = match expr with | _ -> None
let CsBwdArrayExpr (expr: ArrayExpr) = match expr with | _ -> None
let CsBwdTupExpr (expr: TupExpr) = match expr with | _ -> None

let (revpmapping:PartialExprMapping)  = 
    {lhs = CsBwdLhsExpr;
     bool = CsBwdBoolExpr revAbbrVarTable;
     btv = CsBwdBtvExpr;
     nat = CsBwdNatExpr;
     int = CsBwdIntExpr;
     real = CsBwdRealExpr;
     array = CsBwdArrayExpr;
     tup = CsBwdTupExpr;}

(* transform the abbreviated boolean expression back *)
(* according to the reverse abbreviated table:       *)
(* function: BoolExpr -> BoolExpr                    *)
let RevSubtBoolExpr = (PartialTopDownMapping revpmapping).bool


(* ---------------------------------------------------------------- *)
(*                Assignment of Propositional formulae              *)
(* ---------------------------------------------------------------- *)
(* SubVar substitute the bool variable by the corresponding constant*)
let SubVar var (varTable : Dictionary<QName, BoolValue>) = 
    if varTable.ContainsKey(var) then
        match varTable.[var] with
        | BoolVal true -> BoolConst true
        | BoolVal false -> BoolConst false
        | BoolBot -> BoolVar var
        | BoolTop -> BoolVar var
    else
        BoolVar var

(* Assign truth values to a propositional formula *)
let rec Assign (tab : Dictionary<QName, BoolValue>) prop = 
    match prop with
    | BoolConst bc -> BoolConst bc
    | BoolVar var -> SubVar var tab
    | BoolNeg prop -> BoolNeg (Assign tab prop)
    | BoolConj (prop_l, prop_r) -> BoolConj (Assign tab prop_l, Assign tab prop_r)
    | BoolDisj (prop_l, prop_r) -> BoolDisj (Assign tab prop_l, Assign tab prop_r)
    | BoolImpl (prop_l, prop_r) -> BoolImpl (Assign tab prop_l, Assign tab prop_r)
    | BoolEqu (prop_l, prop_r) -> BoolEqu (Assign tab prop_l, Assign tab prop_r)
    | _ -> failwith ExepNotProp



(* -------------------------------------------------------------------- *)
(*                  Partition control GrdActions                        *)
(* -------------------------------------------------------------------- *)


(* compute location variables from control flow guarded actions *)
(* Note that the form of the control flow guarded actions are   *)
(* "r => next(l) = true" where r is a boolean formula and l is  *)
(* a location variable of type BoolExpr                         *)
(* -GetLocVarOfCGA check the left hand side variable of the     *)
(*  guarded action and  if it is inside the variable table,     *)
(*  return the name of the variable. Else return an error msg.  *)
(* -ExtrActVars                                                 *)
(*  extract active location variables from the given state.     *)
(*  the active locations are those with assignment true, and'll *)
(*  be used later for the calculation of the related control    *)
(*  guarded actions.                                            *)


(* get the location variable from the control guarded action *)
(* all varaible QName*string pairs are stored in a table.    *)
(* return the QName of the variable if successfully located. *)
let GetLocVarOfCGA (ga: GrdAction) (nameTab:Map<Index, string>) = 
    match ga with
    | (_, AssignNxt action) -> 
        match action with
        | (LhsVar (BasicName index, Qbool), _, _) -> 
            if (Map.containsKey index nameTab) then (BasicName index)  else failwith ExepNameNotExist 
        | _ -> failwith ExepNotCGA
    | _ -> failwith ExepNotGA

(* extract location variables from the list of guarded actions *)
let rec ExtrLocVars cgalist valtab = 
    match cgalist with
    | [] -> []
    | hd::tail -> 
        let locvar = (GetLocVarOfCGA hd valtab)
        locvar::(ExtrLocVars tail valtab)


(* extract active location variables from the given state*)
(* the active locations are those with assignment true,  *)
(* and will be used later for the calculation of the     *)
(* related control guarded actions.                      *)
(*
let rec ExtrActVars (state: EFSMState) = 
    match state with
    | [] -> []
    | (hd, BoolVal true)::tail -> hd :: (ExtrActVars tail)
    | (hd, _)::tail -> ExtrActVars tail
*)

(*refined: EFSMState as Set of (QName, BoolVal)*)
let ExtrActVars (state: EFSMState) = 
    let foldfunc l e =
        match e with
        | (n, BoolVal true) -> n::l
        | _ -> l
    Set.fold foldfunc [] state

(* get guard of guarded action *)
let GetGuardOfGA (ga: GrdAction) = 
    match ga with
    | (boolexpr, action) -> boolexpr

let GetActionOfGA (ga: GrdAction) =
    match ga with
    | (boolexpr, action) -> action

(* get read variables from a boolean expression.    *)
(* this function was implemented in Expression.sig  *)
(* the function here is a simplification.           *)
(* originally, there is a set of functions that can *)
(* extract all read variables from all kinds of     *)
(* expressions.                                     *)
//val ReadVarsBoolExpr  : BoolExpr  -> (Names.QName * Types.QType) Binaryset.set

let rec ReadVarsBoolExprS boolexpr = 
    match boolexpr with
    | BoolConst bc -> []
    | BoolVar var -> [var]
    | BoolNeg (expr) -> ReadVarsBoolExprS expr
    | BoolConj (expr_l, expr_r) -> (ReadVarsBoolExprS expr_l)@(ReadVarsBoolExprS expr_r)
    | BoolDisj (expr_l, expr_r) -> (ReadVarsBoolExprS expr_l)@(ReadVarsBoolExprS expr_r)
    | BoolImpl (expr_l, expr_r) -> (ReadVarsBoolExprS expr_l)@(ReadVarsBoolExprS expr_r)
    | BoolEqu (expr_l, expr_r) -> (ReadVarsBoolExprS expr_l)@(ReadVarsBoolExprS expr_r)
    | _ -> failwith ExepNotProp 

(* find all related guarded actions and put them into a list *)
(* related guarded actions are defined as those whose guard  *)
(* read the some/all of the variables that are active in the *)
(* current state. Those unrelated guarded actions are put in *)
(* to another list                                           *)
(* a typical test is: IsRelatedGA (ExtrActVars (InitState cgalist LocVarTable)) cga4*)

(* check if a guarded action read any variable in the list varl *)
let IsRelatedGA varl ga = 
    let gard = ReadVarsBoolExprS (GetGuardOfGA ga)
    let rec isRead  gard varl = 
        match gard with
        | [] -> false
        | hd::tail -> if (List.exists (fun e -> e = hd) varl) then true else (isRead tail varl)
    isRead gard varl


(* partition the given guarded action list into two *)
(* one is the related guarded actions, the other is *)
(* the unrelated actions                            *)
let PartitionGA galist state = 
    let actloc = ExtrActVars state
    List.partition (IsRelatedGA actloc) galist




(* -------------------------------------------------------------------- *)
(*            Evaluation guards of the related guarded actions          *)
(* -------------------------------------------------------------------- *)

(* The related control flow guarded actions determine the next state's  *)


(* location variables that are possible to be true. The location        *)
(* variables of the unrelated guarded actions will definitely be false. *)
let EFSMEvalBoolExpr expr = 
    let exprBdd = PropToBDD expr
    match exprBdd with
    | LEAF lf -> BoolConst lf
    | exprNode -> BDDToProp exprNode

(* construct a structure for the ease of evaluation *)
(* nameTab is the table that stores the QName*Str   *)
(* pairs. The function checks if the loc vars are   *)
(* valid. All valid loc vars should be stored in    *)
(* the table.                                       *)
//!!!!let rec StructCGA (galist:GrdAction list) (nameTab:Dictionary<Index, string>) = 
let rec StructCGA (galist:GrdAction list) (nameTab:Map<Index, string>) = 
    match galist with
    | [] -> []
    | hd::tail -> ((GetLocVarOfCGA hd nameTab),GetGuardOfGA hd)::(StructCGA tail nameTab)


(* Evaluation of the guard conditoins                                    *)
(* inputs are current state and list of (QName, Guard) pairs             *)
(* outputs are two lists: one contains the partially fixed next state    *)
(* location variable assignments: (QName, BoolVal val) list, the other   *)
(* (QName, BoolExpr) pairs of the still unfixed guards                   *)

(* -Truthval function generate a dictionary of QName * BoolValue from the state parameter *)

(* -AccFix function takes the truth table generated by Truthval and two list   *)
(*  and a structured guarded action (QName, guard) as inputs and generates     *)
(*  corresponding fixed / unfixed location variables to the corresponding list *)
(*  It will first do a truth assignment to the guard, then do an evaluation.   *)
(*  The location variables whose guards that have true / false will be added   *)
(*  to the fixed list. The location variables whose guards are evaluated to    *)
(*  boolean expressions that can't be fixed will be added to the other list.   *)
//???? let EvalGuardOfCGA (state: EFSMState) (strgas:(QName, BoolExpr) list) = 
(*
let Truthval state =
    let truthTab = new Dictionary<QName, BoolValue>()
    let rec ConstructDict (state: EFSMState) (tTab:Dictionary<QName, BoolValue>) =
        match state with
        | [] ->  tTab
        | (name, value)::tail -> tTab.Add(name, value); ConstructDict tail tTab
    ConstructDict state truthTab
*)

(* refined: EFSMState as a Set *)
let Truthval (state:EFSMState) =
    let truthTab = new Dictionary<QName, BoolValue>()
    Set.fold (fun (tab:Dictionary<QName, BoolValue>) e -> tab.Add e;tab ) truthTab state


(*
let EvalGuardOfCGA (state: EFSMState) strgas = 
    let AccFix (table:Dictionary<QName, BoolValue>) (fixedlv, unfixedlv) strga = 
        match strga with
        | (name, guard) -> 
                       let eval = EFSMEvalBoolExpr(Assign table guard)
                       if eval = (BoolConst true) then ((name, BoolVal true)::fixedlv, unfixedlv)
                       else if eval = (BoolConst false) then ((name, BoolVal false)::fixedlv, unfixedlv)
                       else (fixedlv, (name, eval)::unfixedlv)
    let (fixedlv, unfixedlv) = List.fold (AccFix (Truthval state)) ([], []) strgas
    fixedlv, unfixedlv
*)

let EvalGuardOfCGA (state: EFSMState) strgas = 
    let AccFix (table:Dictionary<QName, BoolValue>) (fixedlv, unfixedlv) strga = 
        match strga with
        | (name, guard) -> 
                       let eval = EFSMEvalBoolExpr(Assign table guard)
                       if eval = (BoolConst true) then ((Set.add (name, BoolVal true) fixedlv), unfixedlv)
                       else if eval = (BoolConst false) then ((Set.add (name, BoolVal false) fixedlv), unfixedlv)
                       else (fixedlv, (name, eval)::unfixedlv)
    let (fixedlv, unfixedlv) = List.fold (AccFix (Truthval state)) (Set.empty, []) strgas
    fixedlv, unfixedlv

(* refinement: EFSMState as Set *)

(*----------------------------------------------------------------*)
(*        generate the next state based on the current state      *)
(*----------------------------------------------------------------*)
(* based on the evaluation of the related guarded actions, the    *)
(* next state's location variable will take value true if the grd *)
(* is evaluated to true and false otherwise. For those evaluated  *)
(* to an unknown value bool expr, further case distinction should *)
(* be done. the expr will take both true and false and for the    *)
(* "true" case, if another unknown value expr' conjunction with   *)
(* this expr and evaluated to false, expr' must be false. or      *)
(* further case distinction on this expr' is needed. For theother *)
(* case, if another unknown value expr' disjunction with this     *)
(* expr evaluated to true, expr' must be true.                    *)
(* A further consideration is to construct a structure that conta-*)
(* ins the whole controlflow--the state-condition-nextstate list  *)


(* case distionction function determine the loc vars' values for  *)
(* iteratively doing case distinctions on the unknown bool exprs  *)
(*
let rec ConnectLstToLsts (t1, t2) lst = 
    match lst with
    | [] -> []
    | (hd1, hd2)::tl -> ((t1@hd1),(t2@hd2))::(ConnectLstToLsts (t1, t2) tl)
*)
(* refined: EFSMState as Set *)
let rec ConnectLstToLsts (t1, t2) lst = 
    match lst with
    | [] -> []
    | (hd1, hd2)::tl -> ((Set.union t1 hd1),(t2@hd2))::(ConnectLstToLsts (t1, t2) tl)


(* refined version of CaseDistinction, generate (guard*nextstate)list *)
(* the "guard" should be a list of boolean expressions, which means   *)
(* that only if the conjunction of this list of guard holds can the   *)
(* corresponding state be reached.                                    *)
(*
let rec CaseDistinction unfixedstrga =
    match unfixedstrga with
    | [] -> []
    | (name, expr)::tail ->
            // case true
            let CaseTrueConj expr (fx, unfx) exprtg = 
                match exprtg with
                | (name, exprp) -> 
                    let resexpr = EFSMEvalBoolExpr(BoolConj(expr, exprp))
                    if resexpr = (BoolConst false) then ((name, BoolVal false)::fx, unfx)
                    else (fx, (name, resexpr)::unfx)
            let (fxrt, unfxrt) = List.fold (CaseTrueConj expr) ([], []) tail
            let fxt = (name, BoolVal true)::fxrt
            let cdunfxrt = CaseDistinction unfxrt
            let casetrue = if cdunfxrt = [] then ([(fxt, [expr])]) else (ConnectLstToLsts (fxt,[expr]) cdunfxrt)           
            // case false
            let CaseFalseDisj expr (fx, unfx) exprtg = 
                match exprtg with
                | (name, exprp) -> 
                    let resexpr = EFSMEvalBoolExpr(BoolDisj(expr, exprp))
                    if resexpr = (BoolConst true) then ((name, BoolVal true)::fx, unfx)
                    else (fx, (name, resexpr)::unfx)
            let (fxrf, unfxrf) = List.fold (CaseFalseDisj expr) ([], []) tail
            let fxf = (name, BoolVal false)::fxrf
            let cdunfxrf = CaseDistinction unfxrf
            let casefalse = if cdunfxrf = [] then ([(fxf, [(BoolNeg expr)])]) else (ConnectLstToLsts (fxf, [(BoolNeg expr)]) cdunfxrf)
            casetrue @ casefalse
*)

(* refined: EFSMState as Set *)
let rec CaseDistinction unfixedstrga =
    match unfixedstrga with
    | [] -> []
    | (name, expr)::tail ->
            // case true
            let CaseTrueConj expr (fx, unfx) exprtg = 
                match exprtg with
                | (name, exprp) -> 
                    let resexpr = EFSMEvalBoolExpr(BoolConj(expr, exprp))
                    if resexpr = (BoolConst false) then ((Set.add (name, BoolVal false) fx), unfx)
                    else (fx, (name, resexpr)::unfx)
            let (fxrt, unfxrt) = List.fold (CaseTrueConj expr) (Set.empty, []) tail
            let fxt = Set.add (name, BoolVal true) fxrt
            let cdunfxrt = CaseDistinction unfxrt
            let casetrue = if cdunfxrt = [] then ([(fxt, [expr])]) else (ConnectLstToLsts (fxt,[expr]) cdunfxrt)
            // case false
            let CaseFalseDisj expr (fx, unfx) exprtg = 
                match exprtg with
                | (name, exprp) -> 
                    let resexpr = EFSMEvalBoolExpr(BoolDisj(expr, exprp))
                    if resexpr = (BoolConst true) then ((Set.add (name, BoolVal true) fx), unfx)
                    else (fx, (name, resexpr)::unfx)
            let (fxrf, unfxrf) = List.fold (CaseFalseDisj expr) (Set.empty, []) tail
            let fxf = Set.add (name, BoolVal false) fxrf
            let cdunfxrf = CaseDistinction unfxrf
            let casefalse = if cdunfxrf = [] then ([(fxf, [(BoolNeg expr)])]) else (ConnectLstToLsts (fxf, [(BoolNeg expr)]) cdunfxrf)
            casetrue @ casefalse

(* TEST
let unfixedstrga = [(BasicName 1, BoolConj(BoolVar (BasicName 11), BoolVar (BasicName 12)));
                    (BasicName 2, BoolConj(BoolNeg(BoolVar(BasicName 11)), BoolVar(BasicName 12)))]
CaseDistinction unfixedstra
*)




(*-----------------------------------------------------------------*)
(*                     generate the init state                     *)
(*-----------------------------------------------------------------*)
(* new version of generating the initial state.                    *)
(* precondition: the AIFSystem is not transformed by using clin.   *)

(* combine CGAs that have the same location variable *)
(* for t1=>next(l)=true and t2=>next(l)=true, the c- *)
(* ombined CGA is: (t1 OR t2)=>next(l)=true;         *)
let rec CombineCGAs cgalist (tabG:Map<Index, string>)= 
    match cgalist with
    | [] -> []
    | hd::tail ->
        let lv = GetLocVarOfCGA hd tabG
        let act = GetActionOfGA hd
        let (rel, unrel) = List.partition (fun cga -> (GetLocVarOfCGA cga !index2NameTable) = lv) cgalist
        let rec DisjCGAs rel =
            match rel with
            | [] -> BoolConst false
            | hd::tail ->
                //let grd =  GetGuardOfGA hd !!!!abbreviation needed!
                let grd = hd |> GetGuardOfGA |> SubtBoolExpr
                let rst = DisjCGAs tail
                BoolDisj(grd, rst)
        let smprelgrd = rel |> DisjCGAs |> EFSMEvalBoolExpr
        (smprelgrd, act)::(CombineCGAs unrel !index2NameTable)

(* ------------------------------------------------------------ *)
(* InitState takes the aif system and the global variable table *)
(* as input parameters and return the QName of the start label  *)
(* and the initial state: (locvar, bool value) list.            *)
(* ------------------------------------------------------------ *)
let rec GetLocVarOfInterface (ifc:Interface) =
    match ifc with
    | [] -> []
    | (name, decl)::tail -> 
        if (decl.flow = Averest.Core.Declarations.Flow.Label) then (name::(GetLocVarOfInterface tail))
        else (GetLocVarOfInterface tail)
(*

let InitState (aifsys:AIFSystem) =
        let st = NewLocalName()
        let locifc = aifsys.locals
        let locvars = GetLocVarOfInterface locifc
        let rec toStateVar lvs = 
            match lvs with
            | [] -> []
            | hd::tail ->
                (hd, BoolVal false)::(toStateVar tail)
        st, (st, BoolVal true)::(toStateVar locvars)
*)

(* refined: EFSMState as Set *)
let InitState (aifsys:AIFSystem) =
        let (initst:EFSMState) = Set.empty
        let st = NewLocalName()
        let locifc = aifsys.locals
        let locvars = GetLocVarOfInterface locifc
        let rec toStateVar lvs = 
            match lvs with
            | [] -> initst
            | hd::tail ->
                Set.add (hd, BoolVal false) (toStateVar tail)
        st, (Set.add (st, BoolVal true) (toStateVar locvars))

(* evaluate the init control flow ????*)
let InitCGAs st (aifsys:AIFSystem) =
    let initcgas = aifsys.init.ctrlFlow
    let SubtGrd lst cga =
        match cga with
        | (grd, act) -> (BoolVar st, act)::lst
    List.fold SubtGrd [] initcgas

(* evaluate the init dataflow *)
let InitDGAs initst (aifsys:AIFSystem) =
    let truthTab = Truthval initst
    let initdgas = aifsys.init.dataFlow
    let rec EvalGAGuards gas =
        match gas with
        | [] -> []
        | (guard, action)::tail ->
            let newgrd = guard |> SubtBoolExpr |> (Assign truthTab) |> EFSMEvalBoolExpr|> RevSubtBoolExpr
            (newgrd, action)::(EvalGAGuards tail)
    EvalGAGuards initdgas


(*--------------------------------------------------------------*)
(*     generate the complete EFSM conditional transitions       *)
(*--------------------------------------------------------------*)

(* refined generate next states function--generate a EFSMStateTrans for the given state *)
(* Note that the start label "st" has no corresponding CGA, so the next value of st is  *)
(* encoded explicitly inside.                                                           *)
(* the generated list is : (EFSMState * BoolExpr list) list where the "BoolExpr list" is*)
(* the list of transition conditions, which means if only the conjunction of the guards *)
(* in the list holds can the transition take place.                                     *)
//!!!!let GenerateStateTrans state cgalist (lvTab:Dictionary<Index, string>) =
(*
let GenerateStateTrans st state cgalist (lvTab:Map<Index, string>) =

    let (rel, unrel) = PartitionGA cgalist state
    let strrel = StructCGA rel lvTab
    let strunrel = StructCGA unrel lvTab
    let (relfx, unfx) = EvalGuardOfCGA state strrel
    let rec FixUnrel strunrel = 
        match strunrel with
        | [] -> []
        | (name, guard)::tail -> (name,BoolVal false)::(FixUnrel tail)
    let unrelfx = (st, BoolVal false)::(FixUnrel strunrel) // Add the start label explicitly
    let fx = (relfx @ unrelfx, [BoolConst true])
    let unfxtofx =  CaseDistinction unfx
    let nextTrans = if unfxtofx = [] then [fx] else (ConnectLstToLsts fx unfxtofx)
    nextTrans
*)

(* refinement: EFSMState as Set *)
let GenerateStateTrans st state cgalist (lvTab:Map<Index, string>) =

    let (rel, unrel) = PartitionGA cgalist state
    let strrel = StructCGA rel lvTab
    let strunrel = StructCGA unrel lvTab
    let (relfx, unfx) = EvalGuardOfCGA state strrel
    let unrelfxr = List.fold (fun s (n, g) -> Set.add (n, BoolVal false) s) relfx strunrel
    let fx = Set.add (st, BoolVal false) unrelfxr //::(FixUnrel strunrel) // Add the start label explicitly
    let fxp = (fx, [BoolConst true])
    let unfxtofx =  CaseDistinction unfx
    let nextTrans = if unfxtofx = [] then [fxp] else (ConnectLstToLsts fxp unfxtofx)
    nextTrans

(* -IsEqState will check if a generated state already exists *)
(*
let rec IsEqState st1 st2 =
    match st1 with
    | [] -> true
    | hd::tl -> if (List.exists ((fun lv1 lv2 -> lv1 = lv2) hd) st2) then (IsEqState tl st2) else false
*)

(*refined: EFSMState as Set*)
let rec IsEqState (st1:EFSMState) (st2:EFSMState) = 
    st1 = st2

(* revised version of GenerateStates, generating (state*(nextstate*guard)list)list    *)
(* the guards are organized in a list, but not as a unique simplified boolexpr. *)
(* this could be done when generating the final EFSM.                           *)
let rec GetStatesOfTrans trans = 
    match trans with
    | [] -> []
    | (st, tran)::tail -> st::GetStatesOfTrans tail

let rec AbbrCGAList cgalist = 
    match cgalist with
    | [] -> []
    | hd::tail ->
        match hd with
        | (guard, action) -> ((SubtBoolExpr guard), action)::(AbbrCGAList tail)

(* nexttrans is of the form (EFSMState * BoolExpr list) list *)
(* trans is of the form (EFSMState * nexttrans) list         *)
(* this function will return the list of all states and the  *)
(* (EFSMState * nexttrans) list                              *)
(* Note that the conditions of the transitions are still of  *)
(* abbreviation form, thus a further back transformation may *)
(* be needed.                                                *)
//!!!! Note that the abbreviations should be neglected. the Conjunction should be done here.
//!!!! let rec GenerateStates currstates allstates trans cgalist (lvTab:Dictionary<Index, string>) = 

let rec GenerateStates st currstates allstates trans cgalist (lvTab:Map<Index, string>) = 
    // substitute non boolean expressions to abbreviated variables first:
    let abbrcgalist = AbbrCGAList cgalist
    match currstates with
    | [] -> (allstates, trans)
    | hd::tail ->
        let nexttrans = GenerateStateTrans st hd cgalist lvTab
        let updatetrans = (hd, nexttrans) :: trans
        let nextstates = GetStatesOfTrans nexttrans
        let IsNewState allstates state = not (List.exists (IsEqState state) allstates) // revised already
        let newstates = List.filter (IsNewState allstates) nextstates
        let updatests = allstates @ newstates
        let updatenew = tail @ newstates
        GenerateStates st updatenew updatests updatetrans cgalist lvTab





(* Transform the abbreviated EFSM back to the original forms *)
(* according to the reverse abbreviation table. The efsm is  *)
(* of the form: (state * (nextstate * condition)list)list *)
let rec TransAbbrGuards guards =
    match guards with
    | [] -> []
    | hd::tail -> (RevSubtBoolExpr hd)::(TransAbbrGuards tail)

let rec ReverseEFSM efsm =
    let rec ReverseTrans nextrans = 
        match nextrans with
        | [] -> []
        | (nextst, guards)::tail -> (nextst, (TransAbbrGuards guards))::(ReverseTrans tail)
    match efsm with
    | [] -> []
    | (state, nexttrans)::tail -> (state, ReverseTrans nexttrans)::(ReverseEFSM tail)



(* Generate the corresponding Dataflow Guarded Actions of a given state *)
(* First check if a DGA is related. If related, then do assignment of   *)
(* corresponding loc vars by the given state. Then do evaluation and    *)
(* generate the simplified guard. Finaly generate the new DGA and put it*)
(* into the list of related DGAs.                                       *)

(* -SubtBoolExpr does abbreviations of subexpressions. The original fu- *)
(*  nction EFSMEvalBoolExpr can only evaluate bool expressions within the   *)
(*  boolean arithmetic. Here the guard of a DGA can contain sub-exprs   *)
(*  of other types, e.g. of NatEqu or RealLst.                          *)
(*  The idea is to first use abbreviated forms of pure boolean formula  *)
(*  for the evaluation, then transform back for the non-boolean typed   *)
(*  subexpressions.                                                     *)
(* -RevSubtBoolExpr transforms an abbreviated boolean expression back   *)
(*  according to the reverse abbreviation table (QName, BoolExpr)       *)

let rec GenerateDGAOfState (state:EFSMState) (dgalist:GrdAction list) = 
    let truthTab = Truthval state
    let actloc = ExtrActVars state
    match dgalist with
    | [] -> []
    | (guard, action)::tail -> 
            let guardsub = SubtBoolExpr guard
            if (IsRelatedGA actloc (guardsub, action)) then 
                let newgrd = guardsub  |> (Assign truthTab) |> EFSMEvalBoolExpr |> RevSubtBoolExpr
                (newgrd, action)::(GenerateDGAOfState state tail)
            else
                GenerateDGAOfState state tail

(* generate list of pairs (state, DGA list) *)
(* first generate the (state, dgas) for the *)
(* initial state and the rest states separ- *)
(* ately, then combine them together.       *)
(*
let GenerateDGAs initst (states:EFSMState list) (aifsys:AIFSystem) =
    let rec GenDGAOfRestSt states dgalist =
        match states with
        | [] -> []
        | hd::tail -> (hd, (GenerateDGAOfState hd dgalist))::(GenDGAOfRestSt tail dgalist)
    let (init, restst) = List.partition (fun st -> st = initst) states
    let rstdgas = GenDGAOfRestSt restst aifsys.main.dataFlow
    let initdgas = InitDGAs initst aifsys
    (initst, initdgas)::rstdgas
*)

(* refined: EFSMState as Set *)
let GenerateDGAs initst (states:EFSMState list) (aifsys:AIFSystem) =
    let rec GenDGAOfRestSt states dgalist =
        match states with
        | [] -> []
        | hd::tail -> (hd, (GenerateDGAOfState hd dgalist))::(GenDGAOfRestSt tail dgalist)
    let restst = List.filter (fun st -> st <> initst) states
    let rstdgas = GenDGAOfRestSt restst aifsys.main.dataFlow
    let initdgas = InitDGAs initst aifsys
    (initst, initdgas)::rstdgas



(* -------------------------------------------------------------------- *)
(*                   Transform the EFSM to AIFSystem                    *)
(* -------------------------------------------------------------------- *)
(* collect state information and do encoding of states; generate for    *)
(* each state a state variable (location variable?); change the guards  *)
(* of the initial and main control / data flow GAs.                     *)
(* Note that the generated CGAs will eliminate all abbreviations.       *)

(* conjunct the conditions of the transitions.         *)
(* this function will eliminate possible abbriviations *)
let ConjGrdExpr conds =
    let rec ConjExprs conds =
        match conds with
        | [] -> BoolConst true
        | hd::tail ->
            let rst = ConjExprs tail
            BoolConj(hd, rst)
    conds |> ConjExprs |> SubtBoolExpr |> EFSMEvalBoolExpr |> RevSubtBoolExpr

(* simplify the condition list of the transition *)
let SimpCondsOfTrans trans =
    let SimpConds tran =
        match tran with
        | (nxst, conds) -> (nxst, ConjGrdExpr conds)
    let NewTran lst tran =
        match tran with
        | (st, nxtrans) ->
            let newnxtrans = List.fold (fun l e -> (SimpConds e)::l) [] nxtrans
            (st, newnxtrans)::lst
    List.fold NewTran [] trans

(*TEST
// GetAbbrVar expr (tabAbbr:Dictionary<BoolExpr, QName>) (tabRev:Dictionary<QName, BoolExpr>) 
let qa = GetAbbrVar (IntLes(IntVar (BasicName 1, None), IntConst [false; true; false])) abbrVarTable revAbbrVarTable
let qb = GetAbbrVar (IntLes(IntVar (BasicName 2, None), IntConst [false; true; false])) abbrVarTable revAbbrVarTable
let trans1 = (1, [(2, [BoolConj(BoolVar qa, BoolVar qb); BoolConst false]);
                  (3, [BoolConj(BoolConst true, BoolVar qb)])])
let trans2 = (2, [(3, [BoolVar qa; BoolConst true])])
let testtrans = [trans1; trans2]
SimpCondsOfTrans testtrans


*)

(* sort the state variables w.r.t. their QName *)
(* this won't be needed for EFSMState as Set
let FormatEFSMState state = 
    let CompStateVar lv1 lv2 = 
        match lv1, lv2 with
        | (name1, val1), (name2, val2) ->
            if (name1 < name2) then -1
            else if (name1 > name2) then 1
            else 0
    List.sortWith CompStateVar state
*)


let NewEFSMStateName () =
    let n = (!index2NameTable).Count
    InsertName ("__state" + (n.ToString()))

(* a simple encoding of the states:                  *)
(* transform the location variables to a bit vector; *)
(* return a map of pairs:(state, BtvEqq(name,  bitvector))list *)
(* the "name" is the unique state location variable generated. *)
(*
let EFSMStateEncoding states =
    let stname = NewEFSMStateName()
    let bvlength = states |> List.head |> List.length
    let rec EncodeStates states =
        match states with
        | [] -> let (stEncodingMap:Map<EFSMState, BtvExpr>) = Map.empty
                stEncodingMap
        | state::restst ->
            let fmtst = FormatEFSMState state
            let BoolOfBoolVal (bval:BoolValue) = 
                match bval with
                | BoolVal bv -> bv
                | _ -> failwith ExepNotBoolVal
            let bv = BtvConst (List.fold (fun bv locval -> (locval |> snd |> BoolOfBoolVal)::bv) [] fmtst)
            // let stname = NewEFSMStateName()
            // Map.add state (BtvEqq(BtvVar(BasicName stname, None), bv)) (EncodeStates restst)
            Map.add state bv (EncodeStates restst)
    {state = (BasicName stname); numberofbv =  bvlength;  encoding = (EncodeStates states)}
*)

(* refined:EFSMState as Set *)
let EFSMStateEncoding states =
    let stname = NewEFSMStateName()
    let bvlength = states |> List.head |> Set.count
    let rec EncodeStates states =
        match states with
        | [] -> let (stEncodingMap:Map<EFSMState, BtvExpr>) = Map.empty
                stEncodingMap
        | state::restst ->
            let BoolOfBoolVal (bval:BoolValue) = 
                match bval with
                | BoolVal bv -> bv
                | _ -> failwith ExepNotBoolVal
            let bv = BtvConst (Set.fold (fun bv locval -> (locval |> snd |> BoolOfBoolVal)::bv) [] state)
            // let stname = NewEFSMStateName()
            // Map.add state (BtvEqq(BtvVar(BasicName stname, None), bv)) (EncodeStates restst)
            Map.add state bv (EncodeStates restst)
    {state = (BasicName stname); numberofbv =  bvlength;  encoding = (EncodeStates states)}


(* generate CGAs from a pair of (state, (nextstate, conditions)list) *)
(* this pair is an element of the transition list.                   *)
(* the new state names are generated and stored in the encodingMap,  *)
(* while the guards are calculated from the conditions and added by  *)
(* the boolean variable representing the state location variable.    *)

let GenNewCGAOfState tran (encoding:EFSMStateEncoding) =
    let stname = encoding.state
    let bvlng = encoding.numberofbv
    let encodingMap = encoding.encoding
    match tran with
    | (state, nextsts) -> //!!!!: the state is a list which is order-sensitive
        let btv  = encodingMap.[state]
        let rec GenCGAs nextsts =
            match nextsts with
            | [] -> []
            | (nextst, conds)::tail ->  // for each transition
                let nxtstbtv = encodingMap.[nextst] // get the next state's bit vector
                let btveq = (BtvEqq(BtvVar(stname, Some bvlng), btv))    // make the bit vector equation
                let condsp = BoolConj(btveq, conds)                 // add the bitvec equation to the condition list
                //let conj = ConjGrdExpr condsp               // make the conjunction of the CGA
                // construct the new CGA:
                let newcga = (condsp, AssignNxt(LhsVar (stname, Qbtv (Some bvlng)), Qbtv (Some bvlng), Ebtv nxtstbtv))
                newcga::(GenCGAs tail)
        GenCGAs nextsts


(* generate the new control flow guarded actions.            *)
(* trans is of type (state, (nextstate, conditions) list)list *)
let rec GenNewCGAs trans (encoding:EFSMStateEncoding) =
    match trans with
    | [] -> []
    | hd::tail ->
        let stcgas = GenNewCGAOfState hd encoding
        stcgas @ (GenNewCGAs tail encoding)

(* generate DGAs of the given state *)
(* stdgapair is of (state, DGA list) *)
let GenNewDGAOfState stdgapair (encoding:EFSMStateEncoding) =
    let stname = encoding.state
    let bvlng = encoding.numberofbv
    let encodingMap = encoding.encoding
    match stdgapair with
    | (state, dgas) ->
        // get the name of the EFSMState
        let btv = encodingMap.[state]
        let btveq = (BtvEqq(BtvVar(stname, Some bvlng), btv))
        let rec GenDGAs dgas =
            match dgas with
            | [] -> []
            | (grd, act)::tail -> // for each DGA
                let newgrdp = (BoolConj(grd, btveq))
                let newgrd = newgrdp |> SubtBoolExpr |> EFSMEvalBoolExpr |> RevSubtBoolExpr
                let newdga = (newgrd, act)
                newdga::(GenDGAs tail)
        GenDGAs dgas


(* generate DGAs from a list of old DGAs *)
(* the only change from the olde ones is *)
(* the guards are conjuncted with the    *)
(* boolean variable of the state location*)
(* "stdgas" is of (state, DGA list) list *)
let rec GenNewDGAs stdgas (encoding:EFSMStateEncoding) = 
    match stdgas with
    | [] -> []
    | hd::tail ->
        let stdgas = GenNewDGAOfState hd encoding
        stdgas @ (GenNewDGAs tail encoding)

(* get new state names *)
(*
let GetNewStateNames (encodingMap:Map<EFSMState, EFSMStateEncoding>) =
    Map.fold (fun lst key vl -> (vl |> fst)::lst) [] encodingMap
*)

(* update the interface of the AIFSystem *)
(* eliminate the old location variables  *)
(* and insert the new state variables    *)
let UpdateLocalsOfAIFSys (aifsys:AIFSystem) (encoding:EFSMStateEncoding) =
    let newstate = encoding.state
    let bvlng = encoding.numberofbv
    let locvars = aifsys.locals
    let IsOldLocVar (pair:(QName * Decl)) = 
        match pair with
        | (name, decl) -> if decl.flow = Averest.Core.Declarations.Flow.Label then false else true
    let (elmlocvars, oldvars) = List.partition IsOldLocVar locvars
    let nlociface = (newstate, {flow = Averest.Core.Declarations.Flow.Label; storage = Event; qtype = Qbtv (Some bvlng);})
    nlociface::elmlocvars

(*----------------------------------------------------------------------*)
(*                          Graph Generation                            *)
(*----------------------------------------------------------------------*)
// create the Graph structure
let MkEFSMStateGraph states trans =
    let (stateG:StateGraph) = Graph.Empty
    // generate vertexes
    let rec GenEFSMVertex states =
        match states with
        | [] -> stateG
        | hd::tail ->
            stateG.AddVertex hd
            GenEFSMVertex tail
    // for each state, generate its outgoing edges
    let GenEFSMPartGraph tran = 
        match tran with
        | (st, nxtran) ->
            let rec GenEdges st nxtran = 
                match nxtran with
                | [] -> stateG
                | (nxst, conds)::tail -> 
                    //let grd = ConjGrdExpr conds
                    stateG.AddEdge (st, conds, nxst)
                    GenEdges st tail
            GenEdges st nxtran
    // generate the whole graph
    let rec GenEFSMGraph trans = 
        match trans with
        | [] -> stateG
        | hd::tail ->
            GenEFSMPartGraph hd
            GenEFSMGraph tail
    GenEFSMVertex states
    GenEFSMGraph trans

// generate the .dot file for the graphviz tool
let PrnEFSMStateGraph label initst stParts (g:StateGraph) =
    // print function for guarded actions
    let prnGrdAction (grd,act) =
        PrnSeq[PrnBoolExpr grd; PrnString " -> "; PrnAction act; PrnString "\\n"]
    // print a state encoding: the active labels
    let PrnEFSMState st =
        let prnt = ExtrActVars st
        let prntnum = List.fold (fun lst elm -> match elm with | BasicName index -> index::lst) [] prnt
        List.fold (fun str elm -> (!index2NameTable).[elm] + " " + str) "" prntnum
    // print vertex
    let prnVertex st =
        // get the related DGAs of the state st
        let rdgas = snd (List.find (fun elem -> match elem with | (tst, _) -> tst = st) stParts)
        PrnSeq
            [   (   if st=initst then PrnString "shape=invhouse,label=\"begin\\n"
                    else PrnString ("shape=rect,label=\"[state "+(PrnEFSMState st)+"]\\n" ))
                PrnApp prnGrdAction rdgas
                PrnString"\""
            ]
    let prnEdge be = PrnString ("label=\""+(string be)+"\"")
    PrnGraph prnVertex prnEdge label g

(*--------------------------------------------*)
(* Generate the new AIFSystem structure.      *)
(* the function will generate the EFSM, and   *)
(* create the new AIFSystem based on the EFSM *)
(* preconditions of the generation are:       *)
(* 1.the abbreviation table should be empty;  *)
(* 2.the abstoReact should be empty;          *)
(* 3.the init and main behavior are separated *)
(* the new AIFSystem will have a main CGA /   *)
(* DGA list and an updated local var list.    *)
(* an option to generate the graph file is    *)
(* provided by the parameter "graph".         *)
(*--------------------------------------------*)
let GenNewAIFSystem aifsys graph =
    // check preconditions
    if (aifsys.abbrevs.size <> 0) then failwith "EFSM trans: AIFSystem's abbrv table is not empty"
    else if (aifsys.absReacts <> []) then failwith "EFSM trans: AIFSystem's absReacts is not empty"
    else if (aifsys.init.ctrlFlow = [] && aifsys.init.dataFlow = []) then failwith "EFSM trans: AIFSystem's init and main should be separated"
    else
        // generate the (state, guarded transitions) pairs
        // and the (state, related DGA) pairs
        let (st, initst) = InitState aifsys
        let aifcgas = CombineCGAs ((InitCGAs st aifsys) @ (aifsys.main.ctrlFlow)) (!index2NameTable)

        let (states, trans) = GenerateStates st [initst] [initst] [] aifcgas !index2NameTable
        // note that the generated trans may have abbreviated guards
        // simplify the conditions of the trans; the abbreviations will also be eliminated
        let smptrans = SimpCondsOfTrans trans

        let stdgas = GenerateDGAs initst states aifsys

        // generate the graph file if demanded ????Prn2File working?
        if graph then
            let dfile = (!index2NameTable).[aifsys.name] + ".dot"
            let g = MkEFSMStateGraph states smptrans
            let gf = PrnEFSMStateGraph ((!index2NameTable).[aifsys.name]) initst stdgas g
            Prn2File dfile gf

        // get the encoding of the EFSM
        let encode = EFSMStateEncoding states
        let newcgas = GenNewCGAs smptrans encode
        let newdgas = GenNewDGAs stdgas encode
        let newlocals = UpdateLocalsOfAIFSys aifsys encode
        let newaifsys = {
                         name = aifsys.name;
                         iface = aifsys.iface;
                         locals = newlocals;
                         abbrevs = aifsys.abbrevs
                         init = {ctrlFlow = []; dataFlow = []; asserts = []};
                         main = {ctrlFlow = newcgas; dataFlow = newdgas; asserts = aifsys.main.asserts}
                         absReacts = [];
                         invar = aifsys.invar;
                         specs = [];
                         }
        newaifsys



(*----------------------------------------------------------------------*)
(*                              Utilities                               *)
(*----------------------------------------------------------------------*)

(* count the number of state for a given list of states *)
let NumOfEFSMStates allstates =
    List.length allstates //List.fold (fun count e -> count+1) 0 allstates

(* count the number of transition relations for a given list of (state, (nextstate, guard)list) *)
let rec NumOfEFSMTrans trans = 
    match trans with
    | [] -> 0
    | (state, nexttrans)::tail -> 
        (List.length nexttrans) + (NumOfEFSMTrans tail)

(* count the number of related DGAs for each state *)
let NumOfDGAPerSt dgaOfSt = 
    match dgaOfSt with
    | (state, dgas) -> List.length dgas

(* count the number of total DGAs *)
let rec NumOfDGAs stNdga =
    match stNdga with
    | [] -> 0
    | hd::tail -> (NumOfDGAPerSt hd) + (NumOfDGAs tail)

(* Printers *)
(*
let PrnEFSMState state =
    let fmtstate = FormatEFSMState state
    let rec PrintLocVar fmstate = 
        match fmstate with
        | [] -> printf " "
        | (locvar, truthval)::tail -> 
            if (truthval = (BoolVal true)) then printf "1"
            else printf "0"
            PrintLocVar tail
    PrintLocVar fmtstate
*)

let PrnEFSMState state =
    let PrnBool (name,var) =
        match var with
        | BoolVal true -> printf "1"
        | BoolVal false -> printf "0"
    Set.iter PrnBool state


(* there's a PrnBoolExpr in Expressions but the usage is not clear *)

(* print the transition relations for each state *)
let rec PrnEFSMNextSt nexttrans = 
    match nexttrans with
    | [] -> printfn ""
    | (nxtst, guards)::tail -> 
        PrnEFSMState nxtst; printf " / "
        PrnEFSMNextSt tail

let rec PrnEFSMTrans trans =
    match trans with
    | [] -> printfn ""
    | (state, nexttrans)::tail -> 
        PrnEFSMState state; printf " -> ";
        PrnEFSMNextSt nexttrans; printfn ""
        PrnEFSMTrans tail


(*TEST
// before translation

let aiffile = "E:\Lektion\Masterarbeit\Test5.aifs"
// translated;
let aiffile = "E:\Lektion\Masterarbeit\Test9.aifs"
let aifsys = ReadSystem aiffile 

// very cool printers:
Prn2Str (PrnAIFSystem aifsys)

// do extention of abbreviations
let (trans:SystemTrans) = ExpandAbbrvs
let aifsyst = TransSystem [trans] aifsys

let newaifsys = GenNewAIFSystem aifsys false

Prn2Str (PrnAIFSystem newaifsys)

let filename = "test"
let raw = true
WriteCFilesLoop dir newaifsys raw

Prn2File filename (PrnXMLAIFSystem newaifsys)
Prn2Str (PrnXMLAIFSystem newaifsys)
*)


(*TEST
// generate the (state, guarded transitions) pairs
// and the (state, related DGA) pairs
let (st, initst) = InitState aifsys
let aifcgas = CombineCGAs ((InitCGAs st aifsys) @ (aifsys.main.ctrlFlow)) !index2NameTable
let (states, trans) = GenerateStates st [initst] [initst] [] aifcgas !index2NameTable
// note that the generated trans may have abbreviated guards
let stdgas = GenerateDGAs initst states aifsys

// generate the .dot graphviz file for the EFSM
let g = MkEFSMStateGraph states trans
let graphviz = PrnEFSMStateGraph "test" initst stdgas g
*)


















