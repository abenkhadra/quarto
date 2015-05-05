//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//


namespace Dump


open Averest.Synthesis.SysMoc
open Averest.Core
open Averest.Core.AIFIO
open Averest.Tools.CommandLine
open System.Collections.Generic
open Averest.Core.Actions
open Averest.Core.Expressions
open Averest.Core.Names



module Main =

    let progname = "aif2dump"
    let (numFiles:FileType) = FileType.One

    let outputFileOption = Option.Create('o', "output", "dumped file", NoParam)
//    let genEFSMGraph = Option.Create('g', "graph", "Generate the .dot file for the graphviz", NoParam)

    let optionList = [outputFileOption; ]
    
    let main (wrapper:Averest.Tools.CommandLine.Wrapper) = 
              
        let outputfile = 
            if wrapper.IsSet outputFileOption then
                wrapper.GetParam outputFileOption
            else
                @"dump.txt"
            
        let aifsys = 
            AIFIO.ReadSystem (wrapper.GetFile())  

        printfn "*************************************"
        printfn "Dumping interface vars ...."
        printfn "*************************************"

        aifsys.iface 
            |> List.iter (fun (x,y) -> 
                let temp1 = x;
                let temp2 = y;
                printfn "Interface Qname:%s Type %s Direction %s " (x.ToString()) (y.qtype.ToString()) (y.flow.ToString())) 

        printfn "*************************************"
        printfn "Dumping local vars ...."
        printfn "*************************************"

        aifsys.locals
            |> List.iter (fun (x,y) -> 
                let temp1 = x;
                let temp2 = y;
                printfn "Locals Qname:%s Type %s Direction %s " (x.ToString()) (y.qtype.ToString()) (y.flow.ToString())) 
          
        printfn "*************************************"
        printfn "Dumping basic control flow ...."
        printfn "*************************************"
        aifsys.ctrlFlow
            |> List.iter (fun x -> 
                let temp1 = x;
                printfn "CGA    - %s " (x.ToString()) ) 


        printfn "*************************************"
        printfn "Dumping basic data flow ...."
        printfn "*************************************"
        aifsys.dataFlow 
            |> List.iter (fun x -> 
                let temp1  = x;
                printfn "DGA    - %s " (x.ToString()) ) 

  
        printfn "*************************************"
        printfn "Dumping abbreviations data flow ...."
        printfn "*************************************"
        aifsys.abbrevs 
            |> List.iter (fun x -> 
                let temp1 = x;
                printfn "Abbrev  - %s " (x.ToString()) ) 

        let _abbrevDict =  new Dictionary<Names.QName, Expressions.BoolExpr>()

            // Used to group multiple guards in CGAs that affect a single label
        let _labelGuardDict = new Dictionary<QName, Expressions.BoolExpr>()

        let ExpandBoolExp (boolexp:Expressions.BoolExpr) =
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



        // Returns a boolean expression expanded by replacing all abbreviations with their original values.
        let ExpandAbbrev (expr:Expressions.Expr) =            
            match expr with
            // Assumes that for an abbreviation to be expanded, its referenced abbreviations are already in _abbrevDict
            | Expressions.Ebool (boolexp) -> ExpandBoolExp(boolexp)
            | _ -> failwith "Abbreviation table is corrupted: No valid boolean expression"

        // Initializes the abbreviation directory, abbreviations are used in reduce the size of boolean expressions.
        let InitializeAbbrevDict = 
            let count = ref(0)
            aifsys.abbrevs |> 
            List.iter (
                fun (boolexp,action) -> 
                    match action with
                    |Actions.AssignNow(lhs,_,exp) ->
                        match lhs with
                        |Expressions.LhsVar (name, _) ->
                            let temp = exp.ToString()
//                            printfn "Processing expression %s " (temp)
                            
//                            if (!count > 395) then
//                                _abbrevDict.Add(name,  Utils.MakeCanonicalBoolExpr(ExpandAbbrev(exp)))
//                            else 
//                                _abbrevDict.Add(name,  ExpandAbbrev(exp))
                            _abbrevDict.Add(name,  ExpandAbbrev(exp))
                            count := !count + 1
                        | _ -> failwith "Abbreviation table is corrupted: No valid Qname"
                    | _ -> failwith "Abbreviation table is corrupted: Abbreviations are not direct assignment" )

        
        printfn "Abbreviation Dirctory is initialized"
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
                let (boolexp, qname) = (fst(grdaction), fst(Utils.LhsQnameofAction(snd(grdaction))))
                if tempLabelDict.ContainsKey(qname) then
                    let currentExpr = tempLabelDict.Item qname
                    ignore (tempLabelDict.Remove(qname))
                    // Multiple guards in a CGA are grouped with a disjoin
                    tempLabelDict.Add(qname, BoolDisj (boolexp, currentExpr))                   
                else
                    tempLabelDict.Add(qname, boolexp)
            
            normalizedControlFlow|> List.iter(buildLabelDict)

            let mutable labelEnum = tempLabelDict.GetEnumerator()
            printfn "*************************************"
            printfn "Dumping optimized control flow ...."
            printfn "*************************************"
            while labelEnum.MoveNext() do
                // Boolean expressions in temporary dict are expanded and canonicalized and added to the final
                //  dict for grouping a single label with multiple guards
                let expandedGuard = Utils.MakeCanonicalBoolExpr(ExpandBoolExp labelEnum.Current.Value)
//                let expandedGuard = this.ExpandBoolExp labelEnum.Current.Value

                printfn "CGA Guard %s,  Label %s "  (expandedGuard.ToString())  (labelEnum.Current.Key.ToString())
                _labelGuardDict.Add(labelEnum.Current.Key, expandedGuard) 
        
        // Initializes the mapping between abbreviations and their guards    
 //       InitializeAbbrevDict
        // Maps each label to combined guard consisting of all CGAs writing to that label.


   //     InitializeLabelGuards

        printfn "*************************************"
        printfn "Dumping optimized data flow ...."
        printfn "*************************************"
        aifsys.dataFlow 
            |> List.iter (fun (grd, action) -> 
              
                printf "DGA    Guard  %s - Action %s " ((ExpandBoolExp(grd)).ToString()) (action.ToString()) 
                let temp =    fst(Utils.LhsQnameofAction(action))
                printfn "- QName %s" (temp.ToString()))

    [<EntryPoint>]
    let run (args : string []) = 
        Wrapper.Run progname optionList numFiles main args

