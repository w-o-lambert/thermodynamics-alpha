# Application and paper traceability

This inventory links the paper-facing application modules to their source
directories. It is a navigation aid, not a claim that every equation in each
publication has been formalised. Each `Traceability.lean` module describes the
scope and conventions of that application; see the linked Lean sources for
theorem names, hypotheses, and proofs.

Applications are classified by scope rather than by file count:

- **Paper traceability** records numbered equations or notation from a
  publication.
- **Model application** exposes paper-independent results for a canonical model
  in an application-facing context.
- **Partial bridge** records a focused translation or subset of a publication,
  not a complete paper formalisation.
- **Manuscript** tracks results from an in-development manuscript.

| Paper or project | Application directory | Main Lean modules |
|---|---|---|
| Schaink and Venema (2007) *(paper traceability)* | `Applications/SchainkVenema2007/` | `Traceability.lean` |
| Mi, Li, Li, and Li (2024) *(paper traceability)* | `Applications/MiLiLiLi2024/` | `Traceability.lean` |
| Lekner (1982) | `Applications/Lekner1982/` | `EquationComparison.lean`, `EquationDerivation.lean`, `PaperEquations.lean`, `Parametrisation.lean`, `Traceability.lean` |
| Pure van der Waals applications *(model application)* | `Applications/PureVanDerWaals/` | `Traceability.lean` |
| Mixture van der Waals applications *(model application)* | `Applications/VanDerWaalsMixture/` | `Traceability.lean` |
| DeVoe (2020), general thermodynamics and selected models | `Applications/DeVoe2020/` | `Thermodynamics.lean`, `Extensivity.lean`, `ClassicalRelations.lean`, `ChemicalEquilibrium.lean`, `Coexistence.lean`, `Models.lean`, `Traceability.lean` |
| Kirkwood and Oppenheim, *Chemical Thermodynamics* (1961), Chapter 11 | `Applications/KirkwoodOppenheim1961/` | `IdealSolutions.lean`, `RegularSolutions.lean`, `RealSolutions.lean`, `Traceability.lean` |

## Reading verification claims

- A theorem that unfolds to `rfl` can record a formula or notation faithfully;
  by itself, it does not prove analytic derivative provenance.
- A paper-facing wrapper may rely on a canonical theorem from `Math`,
  `Thermodynamics`, `Models`, `Methods`, or `Bridges`. Follow its imports and
  proof to inspect those dependencies.
- A listed module identifies formalisation scope, not complete coverage of every
  equation, numerical result, or physical conclusion in the paper.
- DeVoe (2020) wrappers explicitly record source/formalization scope
  mismatches. Henry's law is represented in the dilute-solution model as an
  infinite-dilution fugacity limit; the partial-pressure form is a dilute
  ideal-gas specialization, not an exact finite-composition law.
- Kirkwood–Oppenheim application files are thin source wrappers; model
  definitions and mathematical consequences are kept in `Models/`.
- Full-project compiler verification is provided by the
  [Lean 4.34 GitHub Actions workflow](.github/workflows/lean-4.34.yml). Check the
  latest run for the current result.

The aggregate `ClassicalThermodynamics.Applications` imports every application
directory that contains a `Traceability.lean` module. Model-specific aggregate
modules may also expose some of these applications transitively for historical
compatibility.
