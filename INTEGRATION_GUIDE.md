# Contributor and integration guide

The original package-integration work is complete; the current repository is a
single Lean 4.34 project. This guide describes how to make later additions
without recreating the earlier multi-repository merge process.

## Build the project

1. Install the Lean toolchain named in `lean-toolchain`.
2. From the repository root, run `lake exe cache get` to fetch available
   Mathlib build artifacts.
3. Run `lake build`.
4. For submitted changes, check the GitHub Actions result for the
   `lean-4.34` branch.

After renames or application refactors, run
`pwsh -File scripts/check_documentation.ps1` to verify the source inventories,
application aggregate, Markdown links, and obsolete references. Use
`pwsh -File scripts/check_documentation.ps1 -Write` to regenerate the
inventories.

Use the pinned `lake-manifest.json`; do not update dependencies as part of an
ordinary code change. The CI configuration is in
`.github/workflows/lean-4.34.yml`.

## Place new declarations

Follow the dependency direction:

```text
Math -> Thermodynamics -> Models -> Methods / Bridges -> Applications
```

- Put model-independent algebra and analysis in `ClassicalThermodynamics/Math/`.
- Put generic physical/thermodynamic predicates and interfaces in
  `ClassicalThermodynamics/Thermodynamics/`.
- Keep free energies, states, parameters, and model-specific consequences in
  `ClassicalThermodynamics/Models/`.
- Put reusable parametrisation or calculation techniques in
  `ClassicalThermodynamics/Methods/`.
- Use `ClassicalThermodynamics/Bridges/` for proved translations between independently
  meaningful models, conventions, or state representations.
- Keep publication-specific notation and numbered theorem wrappers in
  `ClassicalThermodynamics/Applications/<Paper>/`.

Prefer importing the narrow module a declaration requires. Add or extend an
aggregate module only when it is intended to be a stable public entry point.
The aggregate imports in `ClassicalThermodynamics/` are convenient package entry points;
they are not a requirement that each model subtree have its own barrel.

## Preserve mathematical provenance

- Treat a model's free energy, domain, and physical parameter assumptions as
  inputs. Derive chemical potentials, Hessians, stability conditions, and
  coexistence consequences where the mathematics permits.
- Keep nonzero, positivity, symmetry, and nondegeneracy hypotheses explicit.
- Do not describe a reflexive formula theorem as a differentiation proof unless
  derivative provenance has actually been established.
- Reuse a canonical lower-layer theorem and add a thin paper wrapper instead of
  duplicating a substantive proof in an application.
- Do not add `sorry`, `admit`, or new axioms to bypass a proof.

For formalisation scope, read `AUDIT.md` and `TRACEABILITY.md`; for architectural
questions, read `ARCHITECTURE.md`.
