import ClassicalThermodynamics.Models.RealSolution.Binary.Margules

/-!
# Kirkwood–Oppenheim: real binary solutions

The wrappers preserve the cubic polynomial convention used in the model
layer. Gibbs–Duhem coefficient constraints are derived there rather than
assumed as fields.
-/

namespace ClassicalThermodynamics.Applications.KirkwoodOppenheim1961

open ClassicalThermodynamics.Models.RealSolution.Binary.Margules

/-- Kirkwood–Oppenheim, Chapter 11, Eqs. (11-133)–(11-134): cubic
composition expansions for binary logarithmic activity coefficients. -/
theorem eqs_11_133_134_logActivities
    (A1 B1 C1 A2 B2 C2 x1 x2 : ℝ) :
    logActivity1 A1 B1 C1 x2 =
        A1 * x2 + B1 * x2 ^ 2 + C1 * x2 ^ 3 ∧
      logActivity2 A2 B2 C2 x1 =
        A2 * x1 + B2 * x1 ^ 2 + C2 * x1 ^ 3 :=
  ⟨rfl, rfl⟩

/-- Gibbs–Duhem compatibility of the two cubic expansions yields their
coefficient relations and the component-2 normal form. -/
theorem gibbsDuhem_cubicMargules_coefficients
    (A1 B1 C1 A2 B2 C2 x1 : ℝ)
    (h : GibbsDuhemCompatible A1 B1 C1 A2 B2 C2) :
    A1 = 0 ∧ A2 = 0 ∧
      B2 = B1 + (3 / 2 : ℝ) * C1 ∧
      C2 = -C1 ∧
      logActivity2 A2 B2 C2 x1 =
        (B1 + (3 / 2 : ℝ) * C1) * x1 ^ 2 - C1 * x1 ^ 3 := by
  rcases coefficients_of_gibbsDuhem A1 B1 C1 A2 B2 C2 h with
    ⟨hA1, hA2, hB2, hC2⟩
  refine ⟨hA1, hA2, hB2, hC2, ?_⟩
  exact logActivity2_normalForm A1 B1 C1 A2 B2 C2 x1 h

end ClassicalThermodynamics.Applications.KirkwoodOppenheim1961
