
A Simple Pseudo-Boolean Solver With Symbolic Conflict Analysis Procedure
===============================================================================

This repository constains all sources used in the paper "Symbolic Conflict Analysis in Pseudo-Boolean Optimization". 

This PB solver with symbolic conflict analysis procedure will keep a symbolic representation for the degree of every constraint.
When an objective function is strengthened in maximization problems, the solver allows to 
(1) strengthen the rerused learned constraints drived from the objective function between problems, thus further pruning the search space traversal,
(2) automatically extract upper bounds from them to estimate how far the solver is from reaching an optimal solution.

It works with a counter-based unit propagation procedure by default in all our experiments, but it can coexist with a watched-based propagation.

Experimental results show that this symbolic procedure is indeed effective with important runtime improvements in problems where several
solutions are found, and the overhead is negligible.

The experiments have been done in a cluster with 10 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 3600 seconds.


# Dependencies
- At least C++14 
- Boost library: https://www.boost.org 

# Build and Run
To check the usage, go to one of solver directories:
```bash
$ make -j
$ ./pbsat -help
```

Original solver:
```bash
$ cd original-solver
$ make -j
$ ./pbsat benchmark.opb    // default flags: -bt0 1 -wperc 0
```

Symbolic solver:
```bash
$ cd symbolic-solver
$ make -j
$ ./pbsat benchmark.opb   // default flags: -bt0 1 -wperc 0 -symb 1
```

# Debug
Compile with the flag `d=1` in any solver directory:
```bash
$ make -j d=1
```
