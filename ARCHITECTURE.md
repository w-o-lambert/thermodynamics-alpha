# Lean Repository Architecture

This alpha branch is pinned to Lean 4.34.1 and Mathlib 4.34.1. The source
tree is organised by mathematical dependency:

```text
Math -> Thermodynamics -> Models -> Methods / Bridges -> Applications
```

## Package layers

- `Math/` contains reusable finite-dimensional, matrix, spectral, affine,
  projective, and calculus infrastructure.
- `Thermodynamics/` contains potentials, differentials, equilibrium,
  stability, criticality, coexistence, and extensivity interfaces.
- `Models/` contains the retained ideal-gas, solution, van der Waals,
  Berthelot, and Redlich--Kwong model definitions and consequences.
- `Methods/` contains model-independent constructions such as coexistence
  consistency and midpoint-difference methods.
- `Bridges/` contains focused translations between retained model
  representations and shared thermodynamic APIs.
- `Applications/` contains thin paper-facing wrappers and model applications.

The root module `ClassicalThermodynamics.lean` imports the complete package.
The aggregate modules `Core.lean`, `Models.lean`, `VanDerWaals.lean`,
`Models/RedlichKwong.lean`, `Methods.lean`, `Bridges.lean`, and
`Applications.lean` provide convenient entry points. Narrow imports are
preferred when a consumer needs only a small API.

## Formalisation rules

The primary physical assumption of a model is its free-energy or
equation-of-state definition together with its domain and parameter
hypotheses. Chemical potentials, pressure identities, Hessian consequences,
stability criteria, criticality, and coexistence results should be derived
from those assumptions whenever the required differentiability is available.

Definitions and theorem statements must expose their domains explicitly.
Nonzero denominators, positivity, temperature conditions, and matrix
symmetry assumptions should appear as hypotheses rather than being hidden in
unproved global claims.

Use `theorem` for public physical results, bridges, criticality, coexistence,
derivative-provenance, and paper-facing conclusions. Use `lemma` for local
algebra, coordinate expansions, symmetry, positivity, matrix transport, and
derivative plumbing.

## Documentation and validation

The retained application inventory is maintained in
[`TRACEABILITY.md`](./TRACEABILITY.md), the reduced scope audit in
[`AUDIT.md`](./AUDIT.md), and current follow-up work in
[`ROADMAP.md`](./ROADMAP.md). Regenerate `MANIFEST.txt` and
`LEAN_SOURCE_INVENTORY.txt` after source changes. The documentation checker
and the aggregate Lean build must pass before changes are considered complete.

## Extension policy

New reusable mathematics belongs in the lowest layer that contains all of its
dependencies. Paper modules should remain thin wrappers around canonical
model and thermodynamic results. If a result first appears in an application
but is later shown to be model-independent, move its canonical statement to
`Math/`, `Thermodynamics/`, `Methods/`, or `Bridges/` and retain only a
traceability wrapper in the application layer.
