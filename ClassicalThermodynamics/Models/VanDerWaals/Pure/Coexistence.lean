import ClassicalThermodynamics.Models.VanDerWaals.Pure.FreeVolume
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
def CoexistAtReducedAttraction (q yA yB : ℝ) : Prop :=
  transformedPressure q yA = transformedPressure q yB ∧
  transformedChemicalPotential q yA = transformedChemicalPotential q yB
noncomputable def attractionFromPressureEquality (yA yB : ℝ) : ℝ :=
  ((1 + yA)^2 * (1 + yB)^2) / (yA + yB + 2 * yA * yB)
theorem reducedAttraction_eq_of_pressure_eq {q yA yB : ℝ}
    (hne : yA ≠ yB) (hA : 1 + yA ≠ 0) (hB : 1 + yB ≠ 0)
    (hden : yA + yB + 2 * yA * yB ≠ 0)
    (hp : transformedPressure q yA = transformedPressure q yB) :
    q = attractionFromPressureEquality yA yB := by
  unfold transformedPressure at hp
  have hpoly :
      (yA - yB) *
        ((1 + yA)^2 * (1 + yB)^2 -
          q * (yA + yB + 2 * yA * yB)) = 0 := by
    field_simp [hA, hB] at hp
    nlinarith
  have hdiff : yA - yB ≠ 0 := sub_ne_zero.mpr hne
  have hcore :
      (1 + yA)^2 * (1 + yB)^2 =
        q * (yA + yB + 2 * yA * yB) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hpoly).resolve_left hdiff
  unfold attractionFromPressureEquality
  apply (eq_div_iff hden).2
  exact hcore.symm

def ParameterFreeCoexistence (yA yB : ℝ) : Prop :=
  Real.log (yA / yB) / (yA - yB) =
    (2 + yA + yB) / (yA + yB + 2 * yA * yB)
end ClassicalThermodynamics.Models.VanDerWaals.Pure
