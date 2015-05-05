# quartz-synthesizer

A library and an example MS Visual Studio project developed in F#. The library is developed for synthesizing modules written in the synchronous language Quartz to actors in SysteMoC. SysteMoC is a SystemC based actor oriented modeling library.

Quartz is an experimental synchronous language developed by the Embedded Systems Group, Technical University of Kaiserslautern. Quartz is part of the [Averest framework](http://www.averest.org/)  for formal model-based design of embdded systems. [SysteMoC](https://www12.informatik.uni-erlangen.de/research/scd/systemoc.phphttps://www12.informatik.uni-erlangen.de/research/scd/systemoc.php) is a SystemC based library for actor-oriented modeling, its developed by the Hardware-Software-Codesign group, University of Erlangen.

The goal of the project is to explore merging the synchronous and actor-oriented Models-of-Computation (MoC) in a single unified model-based design flow for embedded software. So far, we are able of generating C++ code that can simulate efficiently using SysteMoC.

Please check the *License* file for licensing terms.

# Dependancies

The project depends on the core library of averest framework to parse guarded actions. In order to simulate the generated C++ code you need to install [SystemC](http://accellera.org/downloads/standards/systemc) and [SysteMoC](https://www12.informatik.uni-erlangen.de/research/scd/systemoc.phphttps://www12.informatik.uni-erlangen.de/research/scd/systemoc.php).
