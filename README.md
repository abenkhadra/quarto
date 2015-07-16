# quartz-synthesizer

A library and an example MS Visual Studio project developed in F#. The library is developed for synthesizing modules written in the synchronous language Quartz to actors in SysteMoC. SysteMoC is a SystemC based actor oriented modeling library.

Quartz is an experimental synchronous language developed by the Embedded Systems Group, Technical University of Kaiserslautern. Quartz is part of the [Averest framework](http://www.averest.org/)  for formal model-based design of embdded systems. [SysteMoC](https://www12.informatik.uni-erlangen.de/research/scd/systemoc.phphttps://www12.informatik.uni-erlangen.de/research/scd/systemoc.php) is a SystemC based library for actor-oriented modeling, its developed by the Hardware-Software-Codesign group, University of Erlangen.

The goal of the project is to explore merging the synchronous and actor-oriented Models-of-Computation (MoC) in a single unified model-based design flow for embedded software. So far, we are able of generating C++ code that can simulate efficiently using SysteMoC. 

Synthesis procedure starts by taking a Quartz module in the form of Synchronous Guraded-Actions. Then, we proceed to generate a Control-Flow Graph in the form of Extended Finite State Machine (EFSM) from that. We should make sure that the EFSM is deterministic by requiring that the conjunction of guards on each outgoing node is not satisfiable. A mini-sat solver has been developed in `Utils.fs` to check that. Finally, a corresponding SysteMoC module is generated. We take care of presrving the synchronous semantics, a variable has only one value in each step, by generating appropriate temporary variables. 

# Dependancies

The project depends on the core library of averest framework to parse guarded actions. The library can be found in folder  */depend*. In order to simulate the generated C++ code you need to install [SystemC](http://accellera.org/downloads/standards/systemc) and [SysteMoC](https://www12.informatik.uni-erlangen.de/research/scd/systemoc.phphttps://www12.informatik.uni-erlangen.de/research/scd/systemoc.php).
