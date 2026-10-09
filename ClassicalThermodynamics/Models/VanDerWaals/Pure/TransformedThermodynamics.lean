import ClassicalThermodynamics.Models.VanDerWaals.Pure.FreeVolume

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Chemical potential in free-volume coordinates, modulo the additive `-log b`. -/
theorem chemicalPotential_densityFromFreeVolume
    (M : Model) (y : ℝ)
    (hbpos : 0 < M.excludedVolume) (hypos : 0 < y) :
    chemicalPotential M (densityFromFreeVolume M y) =
      transformedChemicalPotential (reducedAttraction M) y -
        Real.log M.excludedVolume := by
  have hb : M.excludedVolume ≠ 0 := ne_of_gt hbpos
  have hy1 : 1 + y ≠ 0 := by positivity
  have hratio := densityFromFreeVolume_div_freeFraction M y hb hy1
  unfold chemicalPotential
  rw [hratio, Real.log_div hypos.ne' hbpos.ne']
  unfold densityFromFreeVolume transformedChemicalPotential reducedAttraction
  have hfree :
      1 - M.excludedVolume *
          (y / (M.excludedVolume * (1 + y))) = 1 / (1 + y) := by
    field_simp [hb, hy1]
    ring
  rw [hfree]
  field_simp [hb, hy1]
  ring

end ClassicalThermodynamics.Models.VanDerWaals.Pure
