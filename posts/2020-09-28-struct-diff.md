---
is-post: true
---

# Type-Safe Generic Differencing for Mutually Recursive Families

This page enumerates the publications and deliverables that
came out of my PhD. I was supervised by Wouter Swierstra 
and Gabriele Keller. The research herein was funded by NWO 
(TOP, number 612.001.401, _Revision control of structured data_).

### Abstract

The UNIX `diff` tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used in software
version control. The fixed lines-of-code granularity, however, is
sometimes too coarse and obscures simple changes, i.e., renaming a
single parameter triggers the whole line to be seen as changed . This
may lead to unnecessary conflicts when unrelated changes occur on the
same line. Consequently, it is difficult to merge such changes
automatically.

During my PhD I investigated two approaches to structural
differencing which work over a large class of
datatypes. The first approach defines a type-indexed representation of
patches and provides a clear merging algorithm, but it is
computationally expensive to produce patches with this approach. The
second approach addresses the efficiency problem by choosing an
extensional representation for patches.  This enables us to represent
transformations involving insertions, deletions, duplication,
contractions and permutations which are computable in linear
time. With the added expressivity, however, comes added complexity.
Consequently, the merging algorithm is more intricate and the patches
can be harder to reason about.

Both approaches can be instantiated to mutually recursive datatypes
and, consequently, can be used to compare elements of most programming
languages. Writing the software that does so, however, comes with
additional challenges. To address this we have developed two new
libraries for generic programming in Haskell.

## List of Publications

> 1. Victor Cacciari Miraldo,
>   Type Safe Generic Differencing of Mutually Recursive Families, PhD thesis. [pdf](data/MiraldoPhD.pdf)
>
> 2. Victor Cacciari Miraldo and Wouter Swierstra,
>   An Efficient Algorithm for Type-Safe Structural Diffing, In *ICFP 2019, Berlin*. [pdf](data/icfp2019.pdf)
>
> 3. Alejandro Serrano Mena and Victor Cacciari Miraldo,
>   Generic Programming of All Kinds, In *Haskell Symposyum 2018, St. Louis*. [pdf](data/hask2018_draft.pdf) [slides](data/hask2018_slides.pdf)
> 4. Victor Cacciari Miraldo and Alejandro Serrano Mena,
>   Sums of Products for Mutually Recursive Datatypes, In *TyDe 2018, St. Louis*. [pdf](data/tyde2018_draft.pdf) [slides](data/tyde2018_slides.pdf)
>
> 5. Victor Cacciari Miraldo, Pierre-Évariste Dagand and Wouter Swierstra,
>   Type-Directed Diffing of Structured Data, In *TyDe 2017, Oxford*. [pdf](data/tyde2017.pdf)

## Software

### `hdiff` 

  The [hdiff](https://github.com/VictorCMiraldo/hdiff) builts on top
of our ICFP [2] and uses the various generic programming libraries we
developed. It treats patches as pattern-expression pairs: the
transformation that swaps two children of a binary tree is represented
by `Bin x y -> Bin y x`.  The main advantage is the ease to define
normal forms; the main difficulty is in handling duplications. 

  Our empirical evaluation ([1], Chap 7) over a [dataset](https://zenodo.org/record/3751038) 
of real conflicts suggests a good line of future work is to restrict `hdiff` to handle only linear patches.
This might enable us to write a much simpler merging algorithm.

### `stdiff`

  The `stdiff` approach origniated from a collaboration with Pierre-Evariste [5];
it constitutes a first attempt at capturing differences between values of type `a`
by induction on the structure of `a`. The work started as an [Agda repo](https://github.com/VictorCMiraldo/stdiff),
which culminates in a proof of the commutativity of the merge algorithm:

```
apply (merge p q) . apply p == apply (merge q p) . apply q
```

  The Agda repo, however, only deals with regular datatypes (lists, trees, etc). Moreover,
the computation of `stdiff` patches is very slow. Garufi's MSc was a first attempt at working 
around these issues by hardcoding the approach to the Clojure language. This was later
followed by van Putten's MSc, where we finished porting the work to arbitrary mutually recursive families
using the [generics-mrsop](https://hackage.haskell.org/package/generics-mrsop) library.

### `simplistic-generics` library

  The [simplistic-generics](https://hackage.haskell.org/package/simplistic-generics) came 
as a replacement for [generics-mrsop](https://hackage.haskell.org/package/generics-mrsop),
after we bumped into two compiler bugs  when attempting to instantiate it with large families.
This has also been joint work with Alejandro Serrano.

### `generics-mrsop` library
  
  The [generics-mrsop](https://hackage.haskell.org/package/generics-mrsop) library [4] was our
first attempt generic programming with mutually recursive families. Unfortunately, we
were held back by two compiler issues ([#17223](https://gitlab.haskell.org/ghc/ghc/-/issues/17223) and 
[14987](https://gitlab.haskell.org/ghc/ghc/-/issues/14987)) when attempting to use larger
families (such as the Python AST) with this library.
  
  This work was done in close collaboration with Alejandro Serrano, and also sparked
other interesting generic programming approaches [3], including the hability to handle
a large class of GADTs, for example.