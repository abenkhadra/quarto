
namespace Averest.Synthesis.SysMoc.Synthesis

open Averest.Synthesis.SysMoc

open Averest.Core
open Averest.Core.Expressions
open Averest.Core.AIFIO
open Averest.Core.Names
open Averest.Core.Declarations
open System.Collections.Generic
open Averest.Core.Actions
open System.IO
 

type DynamicDataTypes() =

    let _inputVars= ref([])
    let _outputVars= ref([])
    let _localVars= ref([])

    // Set of the sizes of bitvectors used in the actor network
    let _bvSizeSet = ref(Set.ofList([]))
  
    // Tuples types used in the actor network.
    let _tupTypeMap = ref(Map.ofList([]))
        
    // Similar to SysMoCDef's GetSysCTypeName but restricted to basic datatypes

    static member GetSysCTypeName(inType:Types.QType) =
        match inType with
        |Types.Qbool -> "bool"
        |Types.Qnat (_) -> "unsigned int"
        |Types.Qint (_) -> "int"
        |Types.Qreal (_) -> "double"
        |Types.Qbtv (size) ->
            if size.IsSome then
                "sc_bv<" + size.Value.ToString() + ">"
            else
                failwith "GenSysCType: unbounded bitvectors are not supported"  
        | (_) -> failwith "GenSysCType: compund types are unsupported inside a tuple"

    // Used in generating a struct name for a tuple
    static member private GetTuplePartDefName(inType:Types.QType) =
        match inType with
        |Types.Qbool -> "bl"
        |Types.Qnat (_) -> "uint"
        |Types.Qint (_) -> "int"
        |Types.Qreal (_) -> "db"
        |Types.Qbtv (size) ->
            if size.IsSome then
                "bv"
            else
                failwith "GetVarDefName: unbounded bitvectors are not supported"  
        | (_) -> failwith "GetVarDefName: tuples of tuples is not supported"

    // Generates a struct name for a tuple
    static member GenTupleTypeName(typelist: Types.QType list) =
        let typename = new StringWriter()
        typename.Write("Tup")
        typelist|> List.iter(fun (qtype) -> 
            typename.Write("_" + DynamicDataTypes.GetTuplePartDefName(qtype)))
        typename.ToString()
        
    // Overloads the (<<) operator to write to an output stream
    static member GenBitvectorXMLSerializer(bvtype:Types.QType) =
        match bvtype with
        | Types.Qbtv (size) ->
            if (size.IsSome) then
                DynamicDataTypes.GenBitvectorXMLSerializer(size.Value)
            else
                ""
        | (other) -> ""
    
    // Overloads the (<<) operator to write to an output stream
    static member GenBitvectorXMLSerializer(size:int) =
        @" 
inline std::ostream &operator<<(std::ostream &out, const sc_bv<" + size.ToString() + @"> &ptr) {
	// Serialize a BV of size " + size.ToString() + @"
    ptr.print(out);
    return out;
}
"    
    // Used to parse tuples to get bitvictors inside them.
    static member GetBitvectorsInTuple(typelist:Types.QType list) =
        let result = ref(Set.ofList([]))
        typelist|> List.iter( fun (qtype)->
            match qtype with
            |Types.Qbtv (size) ->
                if size.IsSome then
                    result := result.Value.Add(size.Value)
            |(other)-> ()
            )
        (result.Value)

    
    static member GetTupleItemDefName (tupDefName:string, index:int) =
        (tupDefName + ".item_" + index.ToString())

    static member GetTupleItemDefName (typelist:Types.QType list, index:int) =
        (DynamicDataTypes.GenTupleTypeName typelist + ".item_" + index.ToString())


    // Add a set of variable types to the tracked variables types.
    member this.AddVariables(inputPortVars:(QName * Decl) list
                            , outputPortVars:(QName * Decl) list
                            , localVars:(QName * Decl) list) =

        _inputVars := List.append _inputVars.Value inputPortVars
        _outputVars := List.append _outputVars.Value outputPortVars
        _localVars := List.append _localVars.Value localVars

    // After all variable types have been added the instance needs to be initialized.
    member this.Initialize() =

        let _combinedVarList = 
            List.append (List.append _inputVars.Value  _outputVars.Value) _localVars.Value    

        _combinedVarList|> 
            List.iter(fun (_, declaration) ->
                match declaration.qtype with
                |Types.Qbtv (size) ->
                    if (size.IsSome) then
                        _bvSizeSet := _bvSizeSet.Value.Add(size.Value)
                    else
                        failwith "InitializeVarTypes: unbounded bitvectors are not supported"

                |Types.Qtup(typelist) ->
                    let bvsInTuple:Set<int> = DynamicDataTypes.GetBitvectorsInTuple(typelist)

                    if (not(bvsInTuple.IsEmpty)) then
                        _bvSizeSet := Set.union _bvSizeSet.Value bvsInTuple
                    if not(_tupTypeMap.Value.ContainsKey(typelist)) then
                        let tupleTypeDefName =  DynamicDataTypes.GenTupleTypeName(typelist)
                        _tupTypeMap:= _tupTypeMap.Value|> Map.add (typelist) tupleTypeDefName

                |(other) -> () )


    member this.GetTupleTypeDefName(typelist:Types.QType list) =
        (_tupTypeMap.Value.Item typelist)


    member this.GetTupleItemDefName (typelist:Types.QType list, index:int) = 
        ((this.GetTupleTypeDefName typelist) + ".item_" + index.ToString())

    // Overloads the (<<) operator to write to an output stream
    member this.GenTupleXMLSerializer(typelist: Types.QType list) =
        let typeDefName = this.GetTupleTypeDefName typelist

        let serializedItems = new StringWriter()
        serializedItems.Write(@"item_0="" << ptr.item_0 << ")
        for i in 1..(typelist.Length - 1) do
            serializedItems.Write(@""", item_" + i.ToString() + @"="" << ptr.item_" + i.ToString() + @" << ")
      
        @" 
inline std::ostream &operator<<(std::ostream &out, const " + typeDefName + @" &ptr) {
    out << """ + typeDefName + @" {" + serializedItems.ToString() + @"""}"";
    return out;
}
"    

    // Given a tuple, a C++ struct definion is generated
    member this.GenTupleStructDefinition(typelist: Types.QType list) =
        
        let definitionBody = new StringWriter()
        let count = ref(0)

        typelist|> List.iter (fun (itemtype) ->
            definitionBody.Write("    " + DynamicDataTypes.GetSysCTypeName(itemtype) + "  item_" + count.Value.ToString() + ";")
            definitionBody.WriteLine()
            count:= !count + 1)
            
        @"
struct " + this.GetTupleTypeDefName(typelist) + @"{
"        + definitionBody.ToString() + @" };
"
    
    // Synthesizes all function overloads of operator (<<)
    member this.SynthesizeXMLSerializers() =
        let synthesizedFunctions = new StringWriter()

        Set.toList(_bvSizeSet.Value)
            |> List.iter( fun (size) -> 
            synthesizedFunctions.Write(DynamicDataTypes.GenBitvectorXMLSerializer(size)))
            
        Map.toList (_tupTypeMap.Value)
            |>List.iter( fun (typelist, _) ->
                synthesizedFunctions.Write(this.GenTupleXMLSerializer(typelist)))
 
        (synthesizedFunctions.ToString())

    // Synthesizes all struct definions of tuples on the actor network.
    member this.SynthesizeTupleStructDefinitions() =
        let synthesizedDefinitions = new StringWriter()

        Map.toList (_tupTypeMap.Value)
            |>List.iter( fun (typelist, _) ->
                synthesizedDefinitions.Write(this.GenTupleStructDefinition(typelist)))
        
        
        (synthesizedDefinitions.ToString())

    // Combines all needed synthesis text in a single function.
    member this.Synthesize() =
        (this.SynthesizeTupleStructDefinitions() + this.SynthesizeXMLSerializers() )


