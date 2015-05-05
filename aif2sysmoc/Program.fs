//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//


namespace Averest.Synthesis.SysMoc

open Averest.Synthesis.SysMoc.Efsm
open Averest.Synthesis.SysMoc.Synthesis

open Averest.Core
open Averest.Core.AIFIO
open Averest.Tools.CommandLine
open System.Collections.Generic
open Averest.Core.Actions



module Main =

    let progname = "aif2sysmoc"
    let (numFiles:FileType) = FileType.One

    let outputFileOption = Option.Create('o', "output", "Synthesized systemoc file", NoParam)
//    let genEFSMGraph = Option.Create('g', "graph", "Generate the .dot file for the graphviz", NoParam)

    let optionList = [outputFileOption; ]
    
    let main (wrapper:Averest.Tools.CommandLine.Wrapper) = 
              
        let outputfile = 
            if wrapper.IsSet outputFileOption then
                wrapper.GetParam outputFileOption
            else
                @"E:\synthesis\synthesis2.cpp"
            
        let aifsys = 
            AIFIO.ReadSystem (wrapper.GetFile())  

//            AIFIO.ReadSystem(@"E:\qrz\IslandTrafficControl\IslandTrafficControl.aifs")
        let temp =  
            aifsys.ctrlFlow |> List.iter (fun x -> printfn "CGA %s " (x.ToString()) ) 

        let temp2 =  
            aifsys.dataFlow |> List.filter (fun (x,y) -> Actions.IsAssignNow(y))
                |>List.iter (fun x -> 
                    printfn "DGA assign now %s " (x.ToString()) ) 
            aifsys.dataFlow |> List.filter (fun (x,y) -> Actions.IsAssignNxt(y))
                |>List.iter (fun x -> 
       
                    printfn "DGA assign next %s " (x.ToString()) ) 
  
        let temp3 =  
            aifsys.abbrevs |> List.iter (fun x -> printfn "Abbreviations %s " (x.ToString()) ) 
////
//        let temp4 =  
//            aifsys.drivers.Head.absReacts |> List.iter (fun x -> printfn "Absreact %s " (x.ToString()) ) 
//        let temp5 =  
//            aifsys.iface |> List.iter (fun (x,y) -> printfn "Interface Qname:%s Type %s Direction %s " (x.ToString()) (y.qtype.ToString()) (y.flow.ToString())) 
//        let temp6 =  
//            aifsys.drivers.Head.locals |> List.iter (fun (x,y) -> printfn "Locals Qname:%s Type %s Direction %s " (x.ToString()) (y.qtype.ToString()) (y.flow.ToString())) 

        let mainsystem = Efsm ("MainSystem", Utils.AIFComponentOfAIFSystem(aifsys))

        mainsystem.Initialize()
        printfn "Main system initialized successfully ... "

        mainsystem.BuildControlGraph
        printfn "Main system control graph built successfully ... "

        mainsystem.BuildAttachedDataGrdActions
        printfn "Main system guarded actions read successfully ... "

        printfn "Now printing main system"
        mainsystem.PrintEFSM

        if (aifsys.drivers.IsEmpty) then
            printfn "No drivers found, terminating ... "
        else

            let maindriver = Efsm("MainDriver", Utils.AIFComponentOfAIFSystemDriver(aifsys.iface, aifsys.drivers.Head))
        
            maindriver.Initialize()
            printfn "Driver initialized successfully ... "

            maindriver.BuildControlGraph
            printfn "Driver system control graph built successfully ... "

            maindriver.BuildAttachedDataGrdActions
            printfn "Driver system guarded actions read successfully ... "

            let topology = new ActorNetworkSynthesizer()

            topology.AddSystemAndDriverDefinitions(mainsystem, maindriver)

            topology.Initialize()
            topology.SynthesizeToFile(outputfile)

            printfn "Actor network synthesized to file successfully ... "
                   
    [<EntryPoint>]
    let run (args : string []) = 
        Wrapper.Run progname optionList numFiles main args

