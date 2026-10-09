# Project roadmap

Last refreshed: October 2026.

## Current baseline

- Lean toolchain: `leanprover/lean4:v4.34.1` (`lean-toolchain`).
- Mathlib: `v4.34.1` (pinned in `lakefile.toml` and `lake-manifest.json`).
- GitHub Actions runs the full Lake build on pushes and pull requests to
  `lean-4.34`; see [the workflow](.github/workflows/lean-4.34.yml).
- The latest local full build passed with reduced parallelism using
  `lake -Kjobs=1 build`. A default-parallelism run hit Lean out-of-memory
  failures in three large application modules; each passed when retried with
  reduced parallelism. Two earlier Mathlib artifact-read failures also passed
  on retry. The GitHub Actions result and any CI cache/build impact remain to be
  checked.

## Architecture

The dependency route remains:

```text
Math -> Thermodynamics -> Models -> Methods / Bridges -> Applications
```

Current reusable areas include finite-dimensional matrix and spectral methods,
thermodynamic observables and stability concepts, pure and mixture van der Waals,
Berthelot, Redlich--Kwong models, coexistence parametrisations, bridges,
and paper-facing traceability modules. See [ARCHITECTURE.md](./ARCHITECTURE.md)
for placement and proof-quality guidance, and [TRACEABILITY.md](./TRACEABILITY.md)
for the application inventory.

## Near-term engineering priorities

1. **Keep the full build reproducible.** Confirm a clean GitHub Actions build
   after the Lean 4.34 linter cleanup and retain its result as the reference
   validation for the branch.
2. **Keep documentation synchronized.** Regenerate the source inventories,
   maintain the application traceability table, and run the repository
   documentation consistency check after renames or application refactors.
3. **Audit derivative provenance.** Distinguish closed-form definitions and
   reflexive equation wrappers from actual proofs that chemical potentials,
   Hessians, and higher derivatives follow from free energies. Track any missing
   derivations explicitly rather than describing formula wrappers as derivations.
4. **Consolidate the Berthelot paper layer.** Review the Mi et al. traceability
   module for duplicated model definitions and prefer bridges to the shared
   `Models.Berthelot` API where those provide equivalent coverage.
5. **Make import surfaces deliberate.** Consider model-level barrels only when
   they provide a useful stable API; keep narrow imports where a broad barrel
   would needlessly compile unrelated modules.
6. **Measure import-minimisation impact.** Narrowed imports have replaced broad
   imports in all 30 modules from the original review set, and the full local
   build passes with reduced parallelism. Check GitHub Actions and compare its
   cache/build impact before treating this as a remedy for runner disk
   exhaustion.

### Import-minimisation handoff

All 30 modules in the original review set now use focused imports instead of a
top-level `import Mathlib`. Narrowing the final four modules exposed two
downstream files that relied on their broad transitive imports; those clients
now import their requirements directly. The full local build passes with
reduced parallelism. Continue to preserve intentional tactic, notation,
attribute, and public API imports, and add direct downstream imports when
needed. A successful local build does not by itself show that CI cache size or
runner disk use has improved; compare GitHub Actions results before drawing that
conclusion.

These are scoped follow-up opportunities, not claims that the current source is
incorrect or that broad reorganisation is required.

## Longer-term mathematical directions

Potential research work, subject to mathematical need and explicit assumptions:

- strengthen generic finite-dimensional criticality, matrix, and stability
  criteria;
- extend derivative provenance to model formulations where it is not yet
  established;
- develop further coexistence constructions and precise bridges between model
  representations;
- develop reusable probability or random-matrix results below their paper
  applications when such results are required by the formalisation.

The finite-index quotient-composition and extensive derivative-transfer
theorems are available in
`ClassicalThermodynamics/Thermodynamics/Extensivity/Construction.lean`.
The van der Waals mixture supplies a Frechet certificate on its explicit
nonzero domain. Berthelot now supplies a standalone model-level
coordinate-Hessian certificate in
`Models/Berthelot/Mixture/DerivativeProvenance.lean`; its extensive adapter uses
that certificate directly rather than reusing the van der Waals mixture
Hessian theorem. The generic `Extensivity/FrechetTransfer.lean` layer now
represents genuine second-Frechet certificates and transfers them for supplied
product-level certificates. It also derives canonical pressure and chemical
potential conjugates directly from an extensive Frechet derivative. Model-level
second-Frechet certificates remain a separate follow-up, since coordinate
Hessian data alone does not establish Frechet differentiability of the full
chemical-potential map.

The pure Redlich--Kwong model now has a standalone fixed-temperature API in
`Models/RedlichKwong/Pure/`, including the molar-volume equation of state,
the compatible density Helmholtz expression, and its proved pressure/Legendre
identity on the explicit physical domain. It deliberately makes no
derivative-provenance or critical-coordinate claim; those require separate
completed derivations.

The Redlich--Kwong mixture sibling is now present in
`Models/RedlichKwong/Mixture/`. It uses an explicit symmetric pair-attraction
matrix and the composition-based one-fluid rule
`q = sum_i b_i rho_i`, with closed-form density pressure, Helmholtz density,
and component chemical potentials. Its pressure identity and derivative
provenance remain follow-up work.

## Release discipline

- Keep the toolchain and Mathlib revisions pinned together.
- Preserve substantive theorems and paper wrappers when moving or refactoring
  code; document any genuine change of mathematical statement.
- Do not use `sorry`, `admit`, new axioms, or hidden completeness assumptions to
  bypass proofs.
- Distinguish source presence, inclusion in the default import graph, focused
  builds, and full-project CI verification.
- Update the architecture, traceability, and reference documentation when
  modules or paper coverage materially change.
