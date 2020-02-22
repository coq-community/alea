# ALEA

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[travis-shield]: https://travis-ci.com/coq-community/alea.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/alea/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby


[doi-shield]: https://zenodo.org/badge/DOI/10.1016/j.scico.2007.09.002.svg
[doi-link]: https://doi.org/10.1016/j.scico.2007.09.002

ALEA is a library for reasoning on randomized algorithms
in Coq, based on interpreting programs inside a monad
as probability distributions.

## Meta

- Author(s):
  - Christine Paulin-Mohring (initial)
  - David Baelde (initial)
  - Pierre Courtieu (initial)
- Coq-community maintainer(s):
  - Anton Trunov ([**@anton-trunov**](https://github.com/anton-trunov))
  - Vladimir Gladstein ([**@volodeyka**](https://github.com/volodeyka))
- License: [GNU General Public License v2.1](LICENSE.md)
- Compatible Coq versions: 8.11 or later (use releases for other Coq versions)
- Additional dependencies: none
- Coq namespace: `ALEA`
- Related publication(s):
  - [Proofs of randomized algorithms in Coq](https://hal.inria.fr/inria-00431771) doi:[10.1016/j.scico.2007.09.002](https://doi.org/10.1016/j.scico.2007.09.002)
- Old ALEA repo
  - https://github.com/coq-contribs/random/

## Building and installation instructions

The easiest way to install the latest released version of ALEA
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-alea
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/alea
cd alea
make   # or make -j <number-of-cores-on-your-machine>
make install
```


## Files described in the paper

The library and its underlying theory is described in the paper
[Proofs of randomized algorithms in Coq][random],
Science of Computer Programming 74(8), 2009, pp. 568-589.
Coq source files mentioned in the paper are described below.

### `Misc.v`
A few preliminary notions, in particular primitives for reasoning classically in Coq, are defined.

### `Ccpo.v`
The definition of structures for ordered sets and ω-complete partial orders (a monotonic sequence has a least upper bound).
We define the type O1 → m O2 of monotonic functions and define the fixpoint-construction for monotonic functionals. Continuity is also defined.

### `Utheory.v`

An axiomatisation of the interval [0,1]. The type [0,1] is given a cpo structure.
We have the predicates ≤ and ==, a least element 0 and a least upper bound on all monotonic sequences of elements of [0,1].

### `Uprop.v`
Derived operations and properties of operators on [0,1].

### `Monads.v`
Definition of the basic monad for randomized constructions, the type α is mapped to the type (α → [0,1]) → m [0,1] of measure functions. We define the unit and star constructions and prove that they satisfy the basic monadic properties. A measure will be a function of type (α → [0,1]) → m [0,1] which enjoys extra properties such as stability with respect to basic operations and continuity. We prove that functions produced by unit and star satisfy these extra properties under appropriate assumptions.

### `Probas.v`
Definition of a dependent type for distributions on a type α. A distribution on a type α is a record containing a function µ of type (α → [0,1]) → m [0,1] and proofs that this function enjoys the stability properties of measures.

### `Prog.v`
Definition of randomized programs constructions. We define the probabilistic choice and conditional constructions and a fixpoint operator obtained by iterating a monotonic functional. We introduce an axiomatic semantics for these randomized programs  --
 let e be a randomized expression of type τ, p be an element of [0,1] and q be a function of type τ → [0,1], we define p ≤ \[e\](q) to be the property --
 the measure of q by the distribution associated to the expression e is not less than p. In the case q is the characteristic function of a predicate Q, p ≤ \[e\](q) can be interpreted as "the probability for the result of the evaluation of e to satisfy Q is not less than p". In the particular case where q is the constant function equal to 1, the relation p ≤ \[e\](q) can be interpreted as "the probability for the evaluation of e to terminate is not less than p".

### `Cover.v`
A definition of what it means for a function f to be the characteristic function of a predicate P. Defines also characteristic functions for decidable predicates. 

### `Choice.v`
A proof of composition of two runs of a probabilistic program, when a choice can improve the quality of the result. Given two randomized expressions p1 and p2 of type τ and a function Q to be estimated, we consider a choice function such that the value of Q for choice(x,y) is not less than Q(x)+Q(y). We prove that if pi evaluates Q not less than ki and terminates with probability 1 then the expression choice(p1,p2) evaluates Q not less than k1(1-k2)+k2 (which is greater than both k1 and k2 when k1 and k2 are not equal to 0).

[random]: https://hal.inria.fr/inria-00431771

