# Expander Graphs
A Lean 4 project depending on [mathlib](https://github.com/leanprover-community/mathlib4).

Goal is to formalize Expander Graphs and related Spectral Graph Theory results.

## Prereqs

You need [elan](https://github.com/leanprover/elan) installed.

## Building
```sh
git clone https://github.com/celioboulay/expander-graphs.git
cd expander-graphs
lake exe cache get
lake build
```