# Coq Library for First-Order Logic

A library for First-Order Logic in Coq

## Installation

We are currently planning to release this as an OPAM package.

Until then, the library can be installed manually.

First, we recommend that you create a new OPAM switch, although this is optional:

```
opam switch create coq-library-fol-8-16 --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
opam switch link coq-library-fol-8-16 .
eval $(opam env)
```

then, install the library using:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install .
```

### Contribuing

In order to compile the library for development, use the above manual installation instructions (preferably creating a new switch), but replace the last command with
```
opam install . --deps-only
```

Compile the library using `make` or using `opam build`.

To contribute, fork the project on GitHub, add a new subdirectory for your project and your files, then file a pull request.


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

## Publications

- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP'19.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory. Yannick Forster, Dominik Kirst, Dominik Wehr. LFCS'20
- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR'20.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory (Extended Version). Yannick Forster, Dominik Kirst, Dominik Wehr. JLC'21.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. ITP'21.
- Trakhtenbrot's Theorem in Coq: Finite Model Theory through the Constructive Lens. Dominik Kirst, Dominique Larchey-Wendling. LMCS'22.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. JAR'22.
- Undecidability of Dyadic First-Order Logic in Coq. Johannes Hostert, Andrej Dudenhefner, Dominik Kirst. ITP'22.
- An Analysis of Tennenbaum's Theorem in Constructive Type Theory. Marc Hermes, Dominik Kirst. FSCD'22.
