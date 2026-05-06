# AnalyticCombinatorics

A Lean 4 formalization project organized around Flajolet and Sedgewick's
*Analytic Combinatorics*.

The repository contains a large collection of formal Lean modules for
generating functions, symbolic constructions, coefficient estimates,
asymptotic schemas, saddle-point and Tauberian methods, and executable sanity
checks for classical combinatorial sequences.

## Status

- Lean toolchain: `leanprover/lean4:v4.29.0`
- Mathlib revision: `v4.29.0`
- Lean source files: 1,284
- Lean source lines: 264,166
- Full library build: 4,548 jobs
- Examples build: 3,305 jobs
- `sorry`/`admit`/`axiom`: none in the Lean sources

The root library imports all non-`Examples` modules. The files under
`AnalyticCombinatorics/Examples` are built separately as executable sanity
checks.

## Layout

- `AnalyticCombinatorics/PartA`: symbolic methods, labelled structures, and
  parameters.
- `AnalyticCombinatorics/PartB`: complex asymptotic methods, singularity
  analysis, saddle-point methods, and limit laws.
- `AnalyticCombinatorics/Asymptotics`: reusable asymptotic schemas and
  transfer windows.
- `AnalyticCombinatorics/AppA`, `AppB`, `AppC`: appendices for finite models,
  complex analysis foundations, and Tauberian/probabilistic schemas.
- `AnalyticCombinatorics/Examples`: verified finite sanity checks for standard
  sequences.

## Build

Install Lean through `elan`, then run:

```bash
lake update
lake build
```

To build the examples as well:

```bash
lake build $(find AnalyticCombinatorics/Examples -name '*.lean' | sed 's#/#.#g; s#\.lean$##' | sort)
```

Useful release checks:

```bash
git diff --check
rg -n '\bsorry\b|\badmit\b|\baxiom\b|TODO|FIXME|placeholder|set_option autoImplicit' \
  AnalyticCombinatorics.lean AnalyticCombinatorics lakefile.toml README.md
```

## License

This project is released under the Apache License 2.0.
