import ClassicalThermodynamics.Models.Berthelot.Mixture.ResponseFunctions
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.FixedCompositionCoexistence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

open scoped BigOperators

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Component-density state on a ray with total density `rho` and composition
`x`. -/
noncomputable def stateAtComposition (x : ι → ℝ) (rho : ℝ) :
    State (ι := ι) :=
  fun i => rho * x i

omit [DecidableEq ι] in
theorem pressure_stateAtComposition_eq_effectiveDimensionlessPure
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) (hx : ∑ i, x i = 1) :
    pressure M temperature (stateAtComposition x rho) =
      dimensionlessPressureAtCompositionDensity M temperature x rho := by
  change
    ClassicalThermodynamics.Models.VanDerWaals.Mixture.pressure
        (dimensionlessVanDerWaalsModel M temperature)
        (ClassicalThermodynamics.Models.VanDerWaals.Mixture.stateAtComposition x rho) =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure
        (effectiveDimensionlessPureModel M temperature x) rho
  exact ClassicalThermodynamics.Models.VanDerWaals.Mixture.pressure_stateAtComposition_eq_effectivePure
    (dimensionlessVanDerWaalsModel M temperature) x rho hx

omit [DecidableEq ι] in
theorem dimensionalPressure_stateAtComposition_eq_pressureTV
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) (hx : ∑ i, x i = 1)
    (hR : M.gasConstant ≠ 0) (hT : temperature ≠ 0) (hrho : rho ≠ 0)
    (hfree : 1 - mixtureCovolume M x * rho ≠ 0) :
    dimensionalPressure M temperature (stateAtComposition x rho) =
      pressureTVAtComposition M x temperature rho⁻¹ := by
  have hvol : rho⁻¹ - mixtureCovolume M x ≠ 0 := by
    intro h
    apply hfree
    have heq :
        1 - mixtureCovolume M x * rho =
          rho * (rho⁻¹ - mixtureCovolume M x) := by
      field_simp [hrho]
    rw [heq, h]
    simp
  rw [show dimensionalPressure M temperature (stateAtComposition x rho) =
      M.gasConstant * temperature *
        pressure M temperature (stateAtComposition x rho) by rfl,
    pressure_stateAtComposition_eq_effectiveDimensionlessPure M temperature x rho hx]
  rw [dimensionlessPressureAtCompositionDensity_formula]
  unfold pressureTVAtComposition
  field_simp [hR, hT, hrho, hfree, hvol]

/-- Closed component chemical-potential formula restricted to a composition
ray, reusing the exact `aᵢⱼ/(R T²)` coefficient of the full mixture. -/
noncomputable def chemicalPotentialAtComposition
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) (i : ι) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotentialAtComposition
    (dimensionlessVanDerWaalsModel M temperature) x rho i

def FixedCompositionCoexistence
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rhoA rhoB : ℝ) : Prop :=
  pressure M temperature (stateAtComposition x rhoA) =
      pressure M temperature (stateAtComposition x rhoB) ∧
    ∀ i, chemicalPotentialAtComposition M temperature x rhoA i =
      chemicalPotentialAtComposition M temperature x rhoB i

omit [DecidableEq ι] in
theorem chemicalPotential_stateAtComposition
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) (i : ι)
    (hx : ∑ j, x j = 1) :
    chemicalPotential M temperature (stateAtComposition x rho) i =
      chemicalPotentialAtComposition M temperature x rho i := by
  exact ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential_stateAtComposition
    (dimensionlessVanDerWaalsModel M temperature) x rho i hx

omit [DecidableEq ι] in
theorem coexist_stateAtComposition_iff
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rhoA rhoB : ℝ)
    (hx : ∑ i, x i = 1) :
    Coexist M temperature
        (stateAtComposition x rhoA) (stateAtComposition x rhoB) ↔
      FixedCompositionCoexistence M temperature x rhoA rhoB := by
  unfold Coexist FixedCompositionCoexistence
  constructor
  · rintro ⟨hp, hmu⟩
    refine ⟨hp, fun i => ?_⟩
    rw [← chemicalPotential_stateAtComposition M temperature x rhoA i hx,
      ← chemicalPotential_stateAtComposition M temperature x rhoB i hx]
    exact hmu i
  · rintro ⟨hp, hmu⟩
    refine ⟨hp, fun i => ?_⟩
    rw [chemicalPotential_stateAtComposition M temperature x rhoA i hx,
      chemicalPotential_stateAtComposition M temperature x rhoB i hx]
    exact hmu i

end ClassicalThermodynamics.Models.Berthelot.Mixture
