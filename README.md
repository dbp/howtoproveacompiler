## About

This is the code repository for a toy compiler verification. It has a compiler
for arithmetic expressions to a tiny stack machine (idea came from Adam
Chlipala's [CPDT]((http://adam.chlipala.net/cpdt/))) implemented in Haskell (in
`src/Compiler.hs`) that is then converted to Coq (using the
[hs-to-coq](https://github.com/antalsz/hs-to-coq) tool by [Spector-Zabusky,
Breitner, Rizkallah, and Weirich](https://arxiv.org/abs/1711.09286), with result
in `src/Compiler.v`) and verified in Coq (proofs in `src/Proofs.v`).

The proofs follow a style that is essentially a modified version of the proof
style advocated by Adam Chlipala in [Certified Programming with Dependent
Types](http://adam.chlipala.net/cpdt/) -- modified slightly in that hints are
always kept extremely locally scoped. The intention behind this (explained a
little further in the library repository for the couple tactics that implement
this: [dbp/literatecoq](https://github.com/dbp/literatecoq)) is to make
reading proofs be as easy as possible, where on paper you would write "follows
by induction using X, Y, and Z". When hints end up in global databases, you can
end up writing proofs that say "follows by induction using X, Z", because you
had hinted Y somewhere earlier.

## Writeup

The accompanying writeup for this compiler is at YYYY.

## Setup

This requires [stack](https://www.haskellstack.org) to install haskell
dependencies needed by `hs-to-coq` (and maybe to experiment with the toy
compiler itself), and [opam](https://opam.ocaml.org/).

Download the submodules that contain the versions of `hs-to-coq` and the
`literatecoq` tactics with:

```
git submodule init
git submodule update
```

Then you need to both build `hs-to-coq`:

```
stack setup --resolver lts-8.3
STACK_YAML=hs-to-coq/stack.yaml stack build
```

And get Coq 8.6 and accompanying libraries:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update && opam install coq.8.6 coq-mathcomp-ssreflect.1.6.1
```

Once Coq has been installed, you can compile the base library for `hs-to-coq`
(which essentially means that your converted programs can use elements of
Haskell's `base` library):

```
make -C hs-to-coq/base
```

Finally, build the `literatecoq` library:

```
make -C literatecoq
```

## Building

To convert the Haskell source to Coq, run:

```
STACK_YAML=hs-to-coq/stack.yaml stack exec hs-to-coq -- -o src/ src/Compiler.hs -e hs-to-coq/base/edits
```

This will put `Compiler.v` into `src`.

To compile this (so you can work on proofs), run:

```
make
```

After which you can open up `src/Proofs.v` in your chosen interactive frontend.
Note that `make` will probably end with an error if you have changed things, as
it tries to run `Proofs` through Coq as well, and if there are theorems that no
longer hold that won't work. But it will have built `src/Compiler.vo` which is
what you need.

## Proving

Obviously, this tiny example is not going to teach you how to prove things in
Coq! There are various resources how to do that. A good one that used to not be
online but now seems to be is Bertot and Casteron's [Coq'Art: Interactive
Theorem Proving and Program
Development](https://archive.org/details/springer_10.1007-978-3-662-07964-5).
Classics that have always been online are [Certified Programming with Dependent
Types](http://adam.chlipala.net/cpdt/) and [Software
Foundations](https://softwarefoundations.cis.upenn.edu/). Theorem proving (of
which I'm still quite new at) seems to be a skill that relies on three pretty
different skills: deep understanding of typed functional programming concepts,
normal paper-and-pencil proof strategy, and understanding the abilities / quirks
of the particular system you are using. 
