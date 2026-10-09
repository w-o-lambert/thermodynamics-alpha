import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Derivative provenance of the pure-fluid chemical potential from the free-energy assumption. -/
theorem hasDerivAt_freeEnergy
    (M : Model) {rho : ℝ}
    (hrho : rho ≠ 0)
    (hfree : 1 - M.excludedVolume * rho ≠ 0) :
    HasDerivAt (freeEnergy M) (chemicalPotential M rho) rho := by
  unfold freeEnergy chemicalPotential
  have hden :
      HasDerivAt (fun x : ℝ => 1 - M.excludedVolume * x)
        (-M.excludedVolume) rho := by
    convert (hasDerivAt_const (x := rho) 1).sub
      ((hasDerivAt_id rho).const_mul M.excludedVolume) using 1
    · funext x
      simp [Function.comp_def, id_eq]
    · simp
  have hratio :=
    (hasDerivAt_id rho).div hden hfree
  have hlog := hratio.log (div_ne_zero hrho hfree)
  have hfree' : 1 - rho * M.excludedVolume ≠ 0 := by
    simpa [mul_comm] using hfree
  convert (((hasDerivAt_id rho).mul (hlog.sub_const 1)).sub
      ((hasDerivAt_pow 2 rho).const_mul (alpha M))) using 1
  · funext x
    simp [id_eq]
  · simp [id_eq]
    field_simp [hfree'] <;> ring

end ClassicalThermodynamics.Models.VanDerWaals.Pure
