//  
//  Part of a master-thesis work done at 
//  Embedded Systems Group, Computer Science department, TU Kaiserslautern.
//
//  Thesis Title: A Model-based approach to Synchronous Elastic Systems.
//  2013, M.Ammar Ben Khadra <ammar@rhrk.uni-kl.de>
//



namespace Averest.Synthesis.SysMoc.Synthesis

open Averest.Core
open System.Collections.Generic
open System.IO


type ElasticBufferSynthesizer() =

    let mutable _defaultClk = 10 

    let mutable _bufferDeclarations = ([])


    member this.ClkPeriod
        with get() =  _defaultClk
        and set(period) = _defaultClk <- period

    // Adds an elastic buffer supporting a certain type to the list of elastic buffer actors that
    //   will be synthesized.
    member this.AddElasticBuffer(name:string, portType:string) =
        _bufferDeclarations <- List.append _bufferDeclarations [(name, portType)]


    // Synthesizes text of the elastic buffers.
    member this.GenerateElasticBufferDefinitionText() =
        let _writer = new StringWriter()
//        _typeList|> List.iter (fun (name, portType) -> _writer.Write(SysMocDefs.GenElasticBufferText (name, portType, this.ClkPeriod.ToString())))
        _writer.Write(SysMocDefs.GenElasticBufferText ("ElasticBuffer", this.ClkPeriod.ToString()))
        _writer.ToString()
        
    member this.GenerateElasticBufferDeclarationText() =
        let declWriter = new StringWriter()

        // We need to generate buffer declarations in the same order of buffer initializations
        _bufferDeclarations 
            |> List.iter(fun (name, buftype) ->
                    declWriter.WriteLine()         
                    declWriter.Write("    ElasticBuffer< "+ buftype + " >  " + name + ";"))                
 
        declWriter.ToString()
        
