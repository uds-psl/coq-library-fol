# Coq Library for First-Order Logic

This library collects several results about concerning first-order logic (FOL) that have been mechanised over the span of several projects. To get started, follow the installation instructions below and import one of the summary files in the [theories](theories) folder, for instance the file [FullSyntax.v](theories/FullSyntax.v) providing all necessary definitions regarding syntax, natural deduction systems, and semantics. There are also summary files for specific theories, for instance [Arithmetics.v](theories/Arithmetics.v) providing the usual systems like PA and Q. Don't hesitate to contact the maintainers if you need help!

Note that the core definitions and results of FOL are included in the [Coq library of undecidability proofs](https://github.com/uds-psl/coq-library-undecidability), specifically the [theories/FOL](https://github.com/uds-psl/coq-library-undecidability/tree/coq-8.16/theories/FOL) folder and its subfolders on [Syntax](https://github.com/uds-psl/coq-library-undecidability/tree/coq-8.16/theories/FOL/Syntax), [Deduction](https://github.com/uds-psl/coq-library-undecidability/tree/coq-8.16/theories/FOL/Deduction), and [Semantics](https://github.com/uds-psl/coq-library-undecidability/tree/coq-8.16/theories/FOL/Semantics). With this distribution, all content regarding undecidability is natively placed in the undecidability library.

The FOL library currently extends this core with the following content:

- [Deduction](theories/Deduction): More deduction systems not included in the core library.
- [Semantics](theories/Semantics): More semantics not included in the core library.
- [Completeness](theories/Completeness): Completeness results for Tarski, Kripke, and algebraic semantics, constructive where possible.
- [Incompleteness](theories/Incompleteness): An abstract and synthetic version of the first incompleteness theorem, instantiated to Robinson's Q, as well as a proof of the first incompleteness theorem and Tarski's theorem via Carnap's diagonal lemma.
- [Tennenbaum](theories/Tennenbaum): Tennenbaum's theorem stating that the natural numbers are the only computable model of PA, constructivised.
- [ArithmeticalHierachy](theories/ArithmeticalHierarchy): Semantic and syntactic characterisations of the arithmetical hierarchy and an equivalence proof.
- [ModelTheory](theories/ModelTheory): Results on model theory, so far focused on the (downwards) Löwenheim-Skolem theorem
- [Proofmode](theories/Proofmode): A tool easing derivations in a deduction system, including a HOAS input language hiding de Bruijn encoded syntax.
- [Reification](theories/Reification): A tactic automating representability proofs of Coq predicates as first-order formulas.
- [Utils](theories/Utils): A collection of additional results needed in various projects.
- [HilbertSystem](theories/HilbertSystem): A Hilbert system for first-order logic with a proof of its equivalence to natural deduction.

## Dev Version Notice

This branch has experimental support for Rocq 9.2. It is still missing MetaRocq support, so the Reification mechanism is disabled.

This branch includes a workaround for [equations#716](https://github.com/rocq-prover/equations/issues/716). This workaround is non-deterministic, you might have to follow the "Library Developer" setup instructions like so:

```
opam switch create . --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda --deps-only --repos=default,coq-released=https://coq.inria.fr/opam/released
# if the above fails, answer N to keep the partially installed switch, then do the following
eval $(opam env)
opam install .
# repeat the above two lines again, as long as new packages keep being installed.
eval $(opam env)
make
```

## Installation

### As a Library User

This library is available in opam. To install it, you can use the following commands:

```
<<<<<<< HEAD
opam switch create coq-library-fol --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-library-fol
```

### As a Library Developer

First, clone this repostitory. Then, run the following commands:

```
opam switch create . --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda --deps-only --repos=default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
make
```

This should automatically build the library. If you are working on a "pre-release" version, you might need the following `--repos` flag:
```
--repos=default,coq-core-dev=https://coq.inria.fr/opam/core-dev,coq-extra-dev=https://coq.inria.fr/opam/extra-dev,coq-released=https://coq.inria.fr/opam/released
```
## Contributing

We are open to contributions! To contribute, fork the project on GitHub, add a new subdirectory for your project and your files, then file a pull request.


## Contributors

- Andrej Dudenhefner
- Yannick Forster
- Marc Hermes
- Johannes Hostert
- Dominik Kirst
- Mark Koch
- Dominique Larchey-Wendling
- Niklas Mück
- Benjamin Peters
- Gert Smolka
- Dominik Wehr
- Janis Bailitis
- Haoyi Zeng

## Publications

### Conference and Journal Papers

- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, Gert Smolka. CPP'19.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory. Yannick Forster, Dominik Kirst, Dominik Wehr. LFCS'20
- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR'20.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory (Extended Version). Yannick Forster, Dominik Kirst, Dominik Wehr. JLC'21.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. ITP'21.
- Trakhtenbrot's Theorem in Coq: Finite Model Theory through the Constructive Lens. Dominik Kirst, Dominique Larchey-Wendling. LMCS'22.
- Undecidability of Dyadic First-Order Logic in Coq. Johannes Hostert, Andrej Dudenhefner, Dominik Kirst. ITP'22.
- An Analysis of Tennenbaum's Theorem in Constructive Type Theory. Marc Hermes, Dominik Kirst. FSCD'22.
- Gödel's Theorem Without Tears: Essential Incompleteness in Synthetic Computability. Dominik Kirst, Benjamin Peters. CSL'23.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. JAR'23.
- The Kleene-Post and Post's Theorem in the Calculus of Inductive Constructions. Yannick Forster, Dominik Kirst, Niklas Mück. CSL'24.
- An Analysis of Tennenbaum's Theorem in Constructive Type Theory (Extended Version). Marc Hermes, Dominik Kirst. LMCS'24.
- The Blurred Drinker Paradox: Constructive Reverse Mathematics of the Downward Löwenheim-Skolem Theorem. Dominik Kirst, Haoyi Zeng. LICS'25.

### Workshop Abstracts

- A Toolbox for Mechanised First-Order Logic. Johannes Hostert, Mark Koch, Dominik Kirst. The Coq Workshop, 2021.
- Synthetic Versions of the Kleene-Post and Post's Theorem. Dominik Kirst, Niklas Mück, Yannick Forster. TYPES, 2022.
- Strong, Synthetic, and Computational Proofs of Gödel's First Incompleteness Theorem. Benjamin Peters, Dominik Kirst. TYPES, 2022.
- A Coq Library for Mechanised First-Order Logic. Dominik Kirst, Johannes Hostert, Andrej Dudenhefner, Yannick Forster, Marc Hermes, Mark Koch, Dominique Larchey-Wendling, Niklas Mück, Benjamin Peters, Gert Smolka, Dominik Wehr. The Coq Workshop, 2022.
- The Blurred Drinker Paradox and Blurred Choice Axioms for the Downward Löwenheim-Skolem Theorem. Dominik Kirst, Haoyi Zeng. TYPES, 2024.
