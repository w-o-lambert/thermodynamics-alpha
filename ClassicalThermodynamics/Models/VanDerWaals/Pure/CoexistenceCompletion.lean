import ClassicalThermodynamics.Models.VanDerWaals.Pure.Coexistence

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Full transformed coexistence implies the parameter-free relation. -/
theorem parameterFreeCoexistence_of_coexist
    {q yA yB : ℝ}
    (hApos : 0 < yA) (hBpos : 0 < yB)
    (hne : yA ≠ yB)
    (hAp1 : 1 + yA ≠ 0) (hBp1 : 1 + yB ≠ 0)
    (hden : yA + yB + 2 * yA * yB ≠ 0)
    (hcoex : CoexistAtReducedAttraction q yA yB) :
    ParameterFreeCoexistence yA yB := by
  rcases hcoex with ⟨hp, hmu⟩
  have hq := reducedAttraction_eq_of_pressure_eq hne hAp1 hBp1 hden hp
  have hlog :
      Real.log (yA / yB) *
          (yA + yB + 2 * yA * yB) =
        (2 + yA + yB) * (yA - yB) := by
    rw [Real.log_div hApos.ne' hBpos.ne']
    have hmu' := hmu
    unfold transformedChemicalPotential at hmu'
    rw [hq] at hmu'
    have hbalance :
        (Real.log yA - Real.log yB) + (yA - yB) =
          2 * attractionFromPressureEquality yA yB *
            (yA / (1 + yA) - yB / (1 + yB)) := by
      linear_combination hmu'
    have hfrac :
        yA / (1 + yA) - yB / (1 + yB) =
          (yA - yB) / ((1 + yA) * (1 + yB)) := by
      field_simp [hAp1, hBp1]
      ring
    rw [hfrac] at hbalance
    have hscaled :
        ((Real.log yA - Real.log yB) + (yA - yB)) *
            (yA + yB + 2 * yA * yB) =
          2 * (1 + yA) * (1 + yB) * (yA - yB) := by
      calc
        _ = (2 * attractionFromPressureEquality yA yB *
              ((yA - yB) / ((1 + yA) * (1 + yB)))) *
              (yA + yB + 2 * yA * yB) := by
          rw [hbalance]
        _ = 2 * (1 + yA) * (1 + yB) * (yA - yB) := by
          unfold attractionFromPressureEquality
          field_simp [hAp1, hBp1, hden]
    calc
      (Real.log yA - Real.log yB) *
          (yA + yB + 2 * yA * yB) =
          ((Real.log yA - Real.log yB) + (yA - yB)) *
            (yA + yB + 2 * yA * yB) -
            (yA - yB) * (yA + yB + 2 * yA * yB) := by ring
      _ = 2 * (1 + yA) * (1 + yB) * (yA - yB) -
            (yA - yB) * (yA + yB + 2 * yA * yB) := by rw [hscaled]
      _ = (2 + yA + yB) * (yA - yB) := by ring
  unfold ParameterFreeCoexistence
  exact (div_eq_div_iff (sub_ne_zero.mpr hne) hden).2 hlog

end ClassicalThermodynamics.Models.VanDerWaals.Pure
