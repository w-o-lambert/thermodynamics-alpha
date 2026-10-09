import ClassicalThermodynamics.Models.VanDerWaals.Pure.Reconstruction
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceCompletion
import ClassicalThermodynamics.Models.VanDerWaals.Pure.TransformedThermodynamics

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Scalar closure reconstructs transformed pressure equality. -/
lemma transformedPressure_eq_of_vdwClosure
    {M : Model} {d : ℝ}
    (hclose : reducedAttraction_eq_pressureBranchValue M d)
    (hH : 1 + vdwLiquidFreeVolume d ≠ 0)
    (hL : 1 + vdwGasFreeVolume d ≠ 0)
    (hden : vdwLiquidFreeVolume d + vdwGasFreeVolume d +
      2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d ≠ 0) :
    transformedPressure (reducedAttraction M) (vdwLiquidFreeVolume d) =
      transformedPressure (reducedAttraction M) (vdwGasFreeVolume d) := by
  unfold reducedAttraction_eq_pressureBranchValue at hclose
  unfold attractionFromPressureEquality at hclose
  have hcore :
      reducedAttraction M *
          (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
            2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d) =
        (1 + vdwLiquidFreeVolume d)^2 * (1 + vdwGasFreeVolume d)^2 :=
    (eq_div_iff hden).mp hclose
  unfold transformedPressure
  field_simp [hH, hL]
  linear_combination
    -(vdwLiquidFreeVolume d - vdwGasFreeVolume d) * hcore

/-- If the reconstructed branches additionally satisfy the parameter-free relation,
scalar closure gives full transformed coexistence. -/
theorem transformedCoexistence_of_vdwClosure
    {M : Model} {d : ℝ}
    (hclose : reducedAttraction_eq_pressureBranchValue M d)
    (hpf : ParameterFreeCoexistence (vdwLiquidFreeVolume d) (vdwGasFreeVolume d))
    (hHpos : 0 < vdwLiquidFreeVolume d) (hLpos : 0 < vdwGasFreeVolume d)
    (hneq : vdwLiquidFreeVolume d ≠ vdwGasFreeVolume d)
    (hH : 1 + vdwLiquidFreeVolume d ≠ 0)
    (hL : 1 + vdwGasFreeVolume d ≠ 0)
    (hden : vdwLiquidFreeVolume d + vdwGasFreeVolume d +
      2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d ≠ 0) :
    CoexistAtReducedAttraction (reducedAttraction M)
      (vdwLiquidFreeVolume d) (vdwGasFreeVolume d) := by
  constructor
  · exact transformedPressure_eq_of_vdwClosure hclose hH hL hden
  · have hpf' := hpf
    unfold ParameterFreeCoexistence at hpf'
    rw [Real.log_div hHpos.ne' hLpos.ne'] at hpf'
    have hlog :
        (Real.log (vdwLiquidFreeVolume d) - Real.log (vdwGasFreeVolume d)) *
            (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
              2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d) =
          (2 + vdwLiquidFreeVolume d + vdwGasFreeVolume d) *
            (vdwLiquidFreeVolume d - vdwGasFreeVolume d) :=
      (div_eq_div_iff (sub_ne_zero.mpr hneq) hden).mp hpf'
    unfold reducedAttraction_eq_pressureBranchValue attractionFromPressureEquality at hclose
    unfold transformedChemicalPotential
    rw [hclose]
    have hrat :
        (vdwLiquidFreeVolume d -
            2 * (((1 + vdwLiquidFreeVolume d)^2 * (1 + vdwGasFreeVolume d)^2) /
              (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
                2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d)) *
              vdwLiquidFreeVolume d / (1 + vdwLiquidFreeVolume d)) -
          (vdwGasFreeVolume d -
            2 * (((1 + vdwLiquidFreeVolume d)^2 * (1 + vdwGasFreeVolume d)^2) /
              (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
                2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d)) *
              vdwGasFreeVolume d / (1 + vdwGasFreeVolume d)) =
        -((2 + vdwLiquidFreeVolume d + vdwGasFreeVolume d) *
          (vdwLiquidFreeVolume d - vdwGasFreeVolume d)) /
          (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
            2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d) := by
      field_simp [hH, hL, hden]
      ring
    have hlogDiv :
        Real.log (vdwLiquidFreeVolume d) - Real.log (vdwGasFreeVolume d) =
          ((2 + vdwLiquidFreeVolume d + vdwGasFreeVolume d) *
            (vdwLiquidFreeVolume d - vdwGasFreeVolume d)) /
            (vdwLiquidFreeVolume d + vdwGasFreeVolume d +
              2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d) := by
      apply (eq_div_iff hden).2
      simpa using hlog
    rw [← sub_eq_zero]
    linear_combination hlogDiv + hrat

end ClassicalThermodynamics.Models.VanDerWaals.Pure
