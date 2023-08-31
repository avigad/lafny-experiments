# lafny-experiments
A repository for experimenting on methods of code verification in Lean

# Notes from trials
The main insight from our failed attempts is that doing the most general
form of looping is best. Implementing `for` and `while` loops seperately
introduces overhead which makes implementation and usage tedious. The best choice that we found was to implement a generic loop with a `break` and, if implementing `for` and `while` loops at all, simply
desugar them in the following manner:

```
let mut x := 0
while x < n do
    body ()
    x := x + 1
```
can be desugared into
```
let mut x := 0
loop do
    if x >= 10 then
        break
    else
        body()
        x := x + 1
```
With Lean 4 elaborators this translation can be done automatically, although this is not currently implemented.

# Repository Structure
This repository is research of experiments of imperative code verification in Lean.
This reposity contains three main parts. The main repository inside `Lafny` and a 
bunch of proof of concept results in `Lafny/DafnyBookExperiments`, and old attempts
in `Lafny/OldExperiments`

 The imporant files in `Lafny` are as follows:
* `Do.lean` which contains the workings of a rewrite of the `do` notation
* `whileM.lean` contains two versions of a while loop: one which uses continuations and one which doesn't.
    The one with continuations will be used in the rewrite of the `do` notation, the one without exists
    for the feasability of writing small examples. `loop_blockM`
    and `loop_with_invariant_contM` are the main results.
* `whileSyntax.lean` which contains the syntax descriptions fo the new notation

Inside `DafnyBookExperiments` exists five files which contain various exercises form the Dafny book, Program Proofs.
The main interesting ones are `Searching.lean` and `Sorting.lean` which contain "skeletons" of verifications of
linear search, binary search, selection sort, and insertion sort. These are "skeletons" because the proofs themselves
are not filled in, but could all easily be done by hand, or in the future, by SMT. The main contribution is that
these proofs can be written at all, given the imperative structure of the code. Other commonly used algorithms like mergesort could be done with this framework as well, but doing so without the ease of Lean managing your variables for you via some built in notation makes it very difficult.

Inside `OldExperiments` are several attempts at making this idea work. These are not garaunteed to work, or even compile.