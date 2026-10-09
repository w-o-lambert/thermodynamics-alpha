import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches

namespace ClassicalThermodynamics.Models.Berthelot.Pure

/-- Paper Eq. (21), identical to Lekner's auxiliary function. -/
noncomputable def leknerY (chi : ℝ) : ℝ :=
  (chi * Real.cosh chi - Real.sinh chi) /
    (Real.sinh chi * Real.cosh chi - chi)

/-- Paper Eqs. (19)-(20). -/
noncomputable def reducedGasDensity (chi : ℝ) : ℝ :=
  3 * leknerY chi / (leknerY chi + Real.exp chi)
noncomputable def reducedLiquidDensity (chi : ℝ) : ℝ :=
  3 * leknerY chi / (leknerY chi + Real.exp (-chi))

/-- Paper Eq. (29). -/
noncomputable def K (chi : ℝ) : ℝ :=
  1 + 2 * leknerY chi * Real.cosh chi + (leknerY chi)^2

/-- The repository logarithmic branch parameter is `d = 2 chi`. -/
noncomputable def repositoryParameter (chi : ℝ) : ℝ := 2 * chi

/-- The common pure-fluid midpoint function used by the van der Waals and
Berthelot branch constructions. -/
noncomputable abbrev vdwGeometricMidpoint :=
  ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint

/-- Exact compatibility with the integrated repository's Lekner coordinate. -/
theorem vdwGeometricMidpoint_two_mul_eq_leknerY
    {chi : ℝ} (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    vdwGeometricMidpoint (repositoryParameter chi) = leknerY chi := by
  change
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
      (repositoryParameter chi) = leknerY chi
  have hchi : chi ≠ 0 := by
    intro hchi
    subst chi
    apply hden
    simp
  rw [ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint_eq_formula
    (by simp [repositoryParameter, hchi])]
  unfold ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpointFormula
    repositoryParameter leknerY
  have hs : Real.sinh (2 * chi) =
      2 * Real.sinh chi * Real.cosh chi := by
    rw [show 2 * chi = chi + chi by ring, Real.sinh_add]
    ring
  rw [hs]
  rw [show 2 * chi / 2 = chi by ring]
  have hden2 : 2 * Real.sinh chi * Real.cosh chi - 2 * chi ≠ 0 := by
    intro h
    apply hden
    nlinarith
  apply (div_eq_div_iff hden2 hden).2
  ring

/-- The common high branch recovers the liquid free-volume coordinate used by
the paper's `chi` parametrisation. -/
theorem vdwLiquidFreeVolume_two_mul_eq_leknerY_mul_exp
    {chi : ℝ} (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwLiquidFreeVolume
        (repositoryParameter chi) =
      leknerY chi * Real.exp chi := by
  rw [ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwLiquidFreeVolume]
  rw [show
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
        (repositoryParameter chi) = leknerY chi from
    vdwGeometricMidpoint_two_mul_eq_leknerY hden]
  unfold repositoryParameter
  rw [show (2 * chi) / 2 = chi by ring]

/-- The common low branch recovers the gas free-volume coordinate used by
the paper's `chi` parametrisation. -/
theorem vdwGasFreeVolume_two_mul_eq_leknerY_mul_exp_neg
    {chi : ℝ} (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGasFreeVolume
        (repositoryParameter chi) =
      leknerY chi * Real.exp (-chi) := by
  rw [ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGasFreeVolume]
  rw [show
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
        (repositoryParameter chi) = leknerY chi from
    vdwGeometricMidpoint_two_mul_eq_leknerY hden]
  unfold repositoryParameter
  rw [show -(2 * chi) / 2 = -chi by ring]

/-- Phase exchange is represented by `chi ↦ -chi`. -/
theorem leknerY_neg (chi : ℝ) : leknerY (-chi) = leknerY chi := by
  unfold leknerY
  rw [Real.cosh_neg, Real.sinh_neg]
  have hnum :
      (-chi) * Real.cosh chi - -Real.sinh chi =
        -(chi * Real.cosh chi - Real.sinh chi) := by ring
  have hden :
      -Real.sinh chi * Real.cosh chi - -chi =
        -(Real.sinh chi * Real.cosh chi - chi) := by ring
  rw [hnum, hden, neg_div_neg_eq]

end ClassicalThermodynamics.Models.Berthelot.Pure
