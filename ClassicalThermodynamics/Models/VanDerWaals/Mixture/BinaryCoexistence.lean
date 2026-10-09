import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary

/-- Midpoint/difference reconstruction of two binary phases. -/
noncomputable def phaseHigh (m d : Fin 2 → ℝ) : State := fun i => m i + d i / 2
noncomputable def phaseLow (m d : Fin 2 → ℝ) : State := fun i => m i - d i / 2

@[simp] theorem phaseHigh_add_phaseLow (m d : Fin 2 → ℝ) (i : Fin 2) :
    phaseHigh m d i + phaseLow m d i = 2 * m i := by
  unfold phaseHigh phaseLow
  ring

@[simp] theorem phaseHigh_sub_phaseLow (m d : Fin 2 → ℝ) (i : Fin 2) :
    phaseHigh m d i - phaseLow m d i = d i := by
  unfold phaseHigh phaseLow
  ring

/-- Binary coexistence residuals in midpoint/difference coordinates. -/
def MidpointDifferenceCoexistence (M : Model) (m d : Fin 2 → ℝ) : Prop :=
  Coexist M (phaseHigh m d) (phaseLow m d)

end ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary
