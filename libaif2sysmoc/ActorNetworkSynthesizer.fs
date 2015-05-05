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
open Averest.Core.Printer
open Averest.Core.Declarations
open System.Collections.Generic
open Averest.Core.Actions
open System.IO
 

// Actor is defined by its EFSM, Instance Number, Detached Output Ports
type ActorDefinition = Efsm * int * Set<QName>

// Port is defined by its Actor name, Actor instance number, QName.
type PortIdentifier = string*int*QName

// An abbreviation for the variable declaration of Averest.
type PortSpecification =   Averest.Core.Declarations.Decl 

// A port is connectin is identified by its src and dst ports and the minimum delay on it.
type PortConnection = PortIdentifier * PortIdentifier * int


type ActorNetworkSynthesizer () =


    // Actor definitions in the network
    let _actorDefs =  new List<ActorDefinition>()

    let _actorsDeclarationsText = new StringWriter()

    // Class definitions of actors
    let _actorDefinitionsText = new StringWriter()

    let _portConnectionsText = new StringWriter()

    let _actorInitializationText = new StringWriter()

    let _bufferInitializationText = new StringWriter()

    let _dynamicDataTypes = new DynamicDataTypes()

    // An instance of ElasticBufferSynthesizer to synthesize class definitions 
    //   and instance declarations of elastic buffer
    let _bufferSynthesizer = ElasticBufferSynthesizer()

    // A dictionary mapping port ID with their specification
    let _actorPortDict = new Dictionary<PortIdentifier, PortSpecification>()

    // List of port connections in the network
    let _actorConnections = new List<PortConnection>()

    member private this.GetActorInstanceName(actorName:string, index:int) =
        (actorName.ToLower()+"_"+ index.ToString())

    member private this.GetElasticBufName(srcport:PortIdentifier, dstport:PortIdentifier, bufferId: int) =

        let GenerateName (intype:string, index:int, qname:QName) =           
            (this.GetActorInstanceName(intype, index) + "_" + SysMocDefs.GetVarName(qname))

        let (srctype, srcindex, srcqname) = srcport
        let (dsttype, dstindex, dstqname) = dstport

        (GenerateName(srctype, srcindex, srcqname) + "_" + GenerateName(dsttype, dstindex, dstqname) + "_" + bufferId.ToString())
    
    member private this.GetNodeInitializationText(name:string) =
        @", " + name + @"(""" + name + @""")"

    member this.AddActorDefinition(actorEfsm:Efsm) =
        this.AddActorDefinition(actorEfsm, 1, Set.ofList([]))

    member this.AddActorDefinition(actorEfsm:Efsm, detachedOutputPorts: Set<QName>) =
        this.AddActorDefinition(actorEfsm, 1, detachedOutputPorts)

    // Adds an actor of the specified type and given number of instances in the network.
    member this.AddActorDefinition(actorEfsm:Efsm, instanceNumber: int, detachedOutputPorts: Set<QName>) =

        let node:ActorDefinition = (actorEfsm, instanceNumber, detachedOutputPorts)
        _actorDefs.Add(node)
  
        if instanceNumber < 1 then failwith "AddActorDefinition: invalid number of actor instances"
   
        // Tracks dynamic datatypes in the actor. Dynamic datatypes are bitvictors and tuples.
        _dynamicDataTypes.AddVariables(actorEfsm.InputPorts, actorEfsm.OutputPorts, actorEfsm.LocalVars)
 
        for i in 1 .. (instanceNumber) do
            actorEfsm.InputPorts
                |>List.iter (fun (qname, decl) -> _actorPortDict.Add((actorEfsm.Name, i, qname), decl))
   
            actorEfsm.OutputPorts
                // Remove detached output ports from the list of output ports.
                |>List.filter(fun (qname, decl) -> not(detachedOutputPorts.Contains(qname)))
                // Add the rest of output ports to the port dictionary.
                |>List.iter (fun (qname, decl) -> _actorPortDict.Add((actorEfsm.Name, i, qname), decl))
                

    member this.AddConnection(src:PortIdentifier, dest:PortIdentifier) =
        this.AddConnection(src, dest, SysMocDefs.DefaultChannelDelay)

    member this.AddConnection(src:PortIdentifier, dest:PortIdentifier, delay:int) =
        if delay < SysMocDefs.DefaultChannelDelay then failwith "AddConnection: minimum connection delay should be at least one cycle"

        // TODO: Error handling if ports do not exist
        let srcspec = _actorPortDict.Item src
        let dstspec = _actorPortDict.Item dest
   
        if (not(srcspec.flow =  Averest.Core.Declarations.Output)) ||( not(dstspec.flow =  Averest.Core.Declarations.Input)) then
            failwith ("At least one connection port doesn't have valid flow type, from: " + src.ToString() + "to: " + dest.ToString())

        if (not(srcspec.qtype = dstspec.qtype)) then
            failwith ("Ports are of not compatible type from: " + src.ToString() + "to: " + dest.ToString())

        let connection:PortConnection = (src, dest, delay)
        _actorConnections.Add(connection)
   
    
    member this.AddSystemAndDriverDefinitions(mainSystem:Efsm, driverSystem: Efsm) =

        let detachedPorts = Set.ofList (mainSystem.OutputPorts |> List.map(fun (qname, decl) -> qname))

        this.AddActorDefinition(mainSystem, detachedPorts)
        this.AddActorDefinition(driverSystem)
            
        // Build connection topology of driver and system
        List.iter2( fun (qname1, decl1) (qname2, decl2) ->
                    let srcport:PortIdentifier= (driverSystem.Name,1,qname1)
                    let dstport:PortIdentifier= (mainSystem.Name,1, qname2)
                    (this.AddConnection(srcport, dstport,2))) driverSystem.OutputPorts mainSystem.InputPorts

        
    
    member this.Initialize() =

        
        _dynamicDataTypes.Initialize()

        // Actor declaration are built
        let BuildActorDeclarations () =
            
            let mutable actorEnumerator = _actorDefs.GetEnumerator()
  
            while actorEnumerator.MoveNext() do
                _actorsDeclarationsText.WriteLine()
                let (synefsm, instancenum, _) = actorEnumerator.Current
                _actorsDeclarationsText.Write("    " + synefsm.Name)

                let actorName = this.GetActorInstanceName(synefsm.Name, 1)
                _actorsDeclarationsText.Write(" "+ actorName)
                _actorInitializationText.WriteLine()
                _actorInitializationText.Write("    " + this.GetNodeInitializationText(actorName))

                for i in 2 .. (instancenum) do
                    let actorName = this.GetActorInstanceName(synefsm.Name, i)
                    _actorsDeclarationsText.Write(", "+ actorName)
                    _actorInitializationText.WriteLine()
                    _actorInitializationText.Write("    " + this.GetNodeInitializationText(actorName))

                _actorsDeclarationsText.Write(" ;")
            ()

        // End of actor declarations

        let BuildConnectionAndBuffers() =

            let mutable connEnumerator = _actorConnections.GetEnumerator()

            let firstBufName = ref("")
            let lastBufName = ref("")

            while connEnumerator.MoveNext() do
                let (srcport, dstport, delay) = connEnumerator.Current
                let (srctype, srcindex, srcqname) = srcport
                let (dsttype, dstindex, dstqname) = dstport
                let portType = (_actorPortDict.Item srcport).qtype
                

                firstBufName := this.GetElasticBufName(srcport, dstport, 1)
                lastBufName := !firstBufName

                _bufferInitializationText.WriteLine()
                _bufferInitializationText.Write("    " + this.GetNodeInitializationText(!firstBufName))
                _bufferSynthesizer.AddElasticBuffer(!firstBufName, SysMocDefs.GetSysCTypeName(portType))
                
                // Generate connection from source actor to first elastic buffer.                
                _portConnectionsText.WriteLine()                
                _portConnectionsText.Write(
                    SysMocDefs.GenConnectionToBufferText(this.GetActorInstanceName(srctype, srcindex)
                                        , srcqname
                                        , !firstBufName
                                        , SysMocDefs.GetSysCTypeName(portType)))

                for i in 2 .. (delay) do
                                    
                    lastBufName := this.GetElasticBufName(srcport, dstport, i)
                    _bufferInitializationText.WriteLine()
                    _bufferInitializationText.Write("    " + this.GetNodeInitializationText(!lastBufName))
                    
                    _bufferSynthesizer.AddElasticBuffer(!lastBufName, SysMocDefs.GetSysCTypeName(portType))
                    
                    // Generate connection between elastic buffers
                    _portConnectionsText.WriteLine()                
                    _portConnectionsText.Write(
                        SysMocDefs.GenConnectionBetweenBuffersText(!firstBufName
                                            , !lastBufName
                                            , SysMocDefs.GetSysCTypeName(portType)))
                    firstBufName:=!lastBufName
                 
                // Generate connection from last elastic buffer to destination actor.
                _portConnectionsText.WriteLine()

                _portConnectionsText.Write(
                    SysMocDefs.GenConnectionFromBufferText(!lastBufName
                                        , this.GetActorInstanceName(dsttype, dstindex)
                                        , dstqname
                                        , SysMocDefs.GetSysCTypeName(portType)))


            ()
        

    
        let BuildActorDefinitions() =
            let mutable actorEnumerator = _actorDefs.GetEnumerator()

            while actorEnumerator.MoveNext() do
                _actorDefinitionsText.WriteLine()
                let (synefsm, _, detachedPorts) = actorEnumerator.Current
                let actor = new ActorSynthesizer(synefsm, detachedPorts)
                actor.Initialize()
                _actorDefinitionsText.Write(actor.Synthesize())
            ()

        // Build actor declaration text, used inside the graph class definition text
        BuildActorDeclarations ()
        
        // Build port connections and buffers, each port connection needs one or more buffers depending 
        //   on the required delay.
        BuildConnectionAndBuffers()   

        // Build actor class definition        
        BuildActorDefinitions()

        ()

        member this.SynthesizeNetworkGraphDefinition() =
            SysMocDefs.GenActorNetworkText(_actorsDeclarationsText.ToString()
                                            , _bufferSynthesizer.GenerateElasticBufferDeclarationText()
                                            , _actorInitializationText.ToString() + _bufferInitializationText.ToString()
                                            , _portConnectionsText.ToString())
        
        // Synthesizes the whole actor network simulation code
        // Pre-requisites are the initialization of the instance.
        member this.Synthesize() = 
            ( SysMocDefs.GenFileHeaderText 
            + _dynamicDataTypes.Synthesize()
            + _bufferSynthesizer.GenerateElasticBufferDefinitionText() 
            + _actorDefinitionsText.ToString()
            + this.SynthesizeNetworkGraphDefinition()
            + SysMocDefs.GenMainText)

        member this.SynthesizeToFile(outputfile:string) =
            File.WriteAllText(outputfile , this.Synthesize())
 

  

