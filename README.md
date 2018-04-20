# MiniZinc Analysis Toolkit

## What it does

1. Identifies submodels of a MiniZinc model.
2. Finds a best submodel according to heuristics selected by the user.
3. Automatically encapsulates said submodel within a predicate definition along with an presolve annotation using the auto-tabling tool by Jip J. Dekker (https://github.com/Dekker1/libminizinc), creating a new MiniZinc model.

## Prerequisites

* Stack (haskell-stack)

## Installation

1. Get necessary packages and files by running `make setup`.
2. Install by running `make install`; an executable will appear in `bin/`.
3. Add `bin/` to path if desired.
