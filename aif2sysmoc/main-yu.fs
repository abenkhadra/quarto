
// commandline interface to the C synthesis output

open Averest.Core
open Averest.Core.CommandLine
open Averest.Core.Properties
open Averest.Core.AIFIO
open Averest.Core.Names
open Averest.Core.Printer
open Averest.Transformation.Utils
open Averest.Transformation.Clearer

open EFSMPack.EFSM
open SMTSolvingPack.SMTSolving
open IvIfPack.InvarInference
open IDPassCode.IDPC

let progname = "aif2efsm2aif"
let numFiles = One

//let preventTrans = Option.Create('r', "raw", "take aif as it is and perform no transformation", NoParam)
let outputDirOption = Option.Create('o', "output", "directory to output generated files", OneParam Arbitrary)
let genEFSMGraph = Option.Create('g', "graph", "generate the .dot file for the graphviz", NoParam)
let smtSolving = Option.Create('s', "smt", "SMT enhanced EFSM generation", NoParam)
let invInf = Option.Create('v', "inv.infer", "invariant inference", NoParam)
let idPC = Option.Create('p', "id.pass.code", "identify passive code", NoParam)



let optionList = [outputDirOption; genEFSMGraph; smtSolving; invInf; idPC]

let main (wrapper:Wrapper) =
    // set default output directory if no other one is given
    let dir =
        if wrapper.IsSet outputDirOption then
            wrapper.GetParam outputDirOption
        else "."
    // set graph flag
    let graph = wrapper.IsSet genEFSMGraph
    // set smt flag
    let smt = wrapper.IsSet smtSolving
    // set invariant infer flag
    let ivif = wrapper.IsSet invInf
    // set id passive code flag
    let idpc = wrapper.IsSet idPC
    // read system
    let system = AIFIO.ReadSystem (wrapper.GetFile ())

    // transformation to eliminate abbreviations: suab
    //????let (trans:SystemTrans) = ExpandAbbrvs
    // do transformation
    //????let aifsysp = TransSystem [trans] system
    // do generation of the new AIFSystem
    //????let newsystem = AdvGenNewAIFSystem aifsysp graph
    let newsystem = AdvGenNewAIFSystemV3 system graph smt ivif idpc
    //let newsystem = GenNewAIFSystem aifsysp graph
    // output the XML file
    let opfile = (!index2NameTable).[newsystem.name] + ".aifs"
    Prn2File opfile (PrnXMLAIFSystem newsystem)
    


[<EntryPoint>]
let run (args : string []) =
    Wrapper.Run progname optionList numFiles main args