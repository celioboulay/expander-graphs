# Expander Graphs
A Lean 4 project depending on [mathlib](https://github.com/leanprover-community/mathlib4).

Goal is to formalize Expander Graphs and related Spectral Graph Theory results. [Link](https://celioboulay.github.io/expander-graphs/) to the blueprint of the project.

## Prereqs

You need [elan](https://github.com/leanprover/elan) installed.

## References
The primary reference for this project is:

- Daniel Spielman *Spectral and Algebraic Graph Theory*.

Unless stated otherwise, definitions and statements follow the conventions of that book.

## Building
```sh
git clone https://github.com/celioboulay/expander-graphs.git
cd expander-graphs
lake exe cache get
lake build
```
