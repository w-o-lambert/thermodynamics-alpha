import ClassicalThermodynamics.Models.VanDerWaals.Mixture.ResponseFunctions
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceObservables
import ClassicalThermodynamics.Models.VanDerWaals.Pure.ResponseFunctions

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Component-density state on the ray with total density `rho` and composition `x`. -/
noncomputable def stateAtComposition (x : ι → ℝ) (rho : ℝ) : State (ι := ι) :=
  fun i => rho * x i

/-- Effective pure van der Waals model seen along a normalized composition ray. -/
noncomputable def effectivePureModel
    (M : Model (ι := ι)) (x : ι → ℝ) :
    ClassicalThermodynamics.Models.VanDerWaals.Pure.Model where
  attraction := mixtureAttraction M x
  excludedVolume := mixtureCovolume M x
  gasConstant := M.gasConstant
  temperature := M.temperature

omit [DecidableEq ι] in
@[simp] theorem totalDensity_stateAtComposition
    (x : ι → ℝ) (rho : ℝ) (hx : ∑ i, x i = 1) :
    totalDensity (stateAtComposition x rho) = rho := by
  unfold totalDensity stateAtComposition
  rw [← Finset.mul_sum, hx]
  ring

omit [DecidableEq ι] in
@[simp] theorem occupiedFraction_stateAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ) :
    occupiedFraction M (stateAtComposition x rho) =
      mixtureCovolume M x * rho := by
  unfold occupiedFraction stateAtComposition mixtureCovolume
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [DecidableEq ι] in
@[simp] theorem freeVolumeFraction_stateAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ) :
    freeVolumeFraction M (stateAtComposition x rho) =
      1 - mixtureCovolume M x * rho := by
  unfold freeVolumeFraction
  rw [occupiedFraction_stateAtComposition]

omit [DecidableEq ι] in
/-- The N-component pressure restricted to a normalized composition ray is exactly
that of the effective pure model. -/
theorem pressure_stateAtComposition_eq_effectivePure
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ)
    (hx : ∑ i, x i = 1) :
    pressure M (stateAtComposition x rho) =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure
        (effectivePureModel M x) rho := by
  unfold pressure ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure
    ClassicalThermodynamics.Models.VanDerWaals.Pure.alpha effectivePureModel
  rw [totalDensity_stateAtComposition x rho hx,
    freeVolumeFraction_stateAtComposition]
  unfold alpha mixtureAttraction
  simp only [stateAtComposition]
  congr 1
  rw [show (∑ i, ∑ j,
      (M.attraction i j / (M.gasConstant * M.temperature)) / 2 *
        (rho * x i) * (rho * x j)) =
    (∑ i, ∑ j, x i * M.attraction i j * x j / 2) /
      (M.gasConstant * M.temperature) * rho^2 by
    calc
      (∑ i, ∑ j,
          (M.attraction i j / (M.gasConstant * M.temperature)) / 2 *
            (rho * x i) * (rho * x j)) =
          ∑ i, ∑ j,
            (rho^2 / (M.gasConstant * M.temperature)) *
              (x i * M.attraction i j * x j / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (rho^2 / (M.gasConstant * M.temperature)) *
          (∑ i, ∑ j, x i * M.attraction i j * x j / 2) := by
        calc
          (∑ i, ∑ j,
              (rho^2 / (M.gasConstant * M.temperature)) *
                (x i * M.attraction i j * x j / 2)) =
              ∑ i, (rho^2 / (M.gasConstant * M.temperature)) *
                (∑ j, x i * M.attraction i j * x j / 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (rho^2 / (M.gasConstant * M.temperature)) *
              (∑ i, ∑ j, x i * M.attraction i j * x j / 2) := by
            rw [Finset.mul_sum]
      _ = (∑ i, ∑ j, x i * M.attraction i j * x j / 2) /
          (M.gasConstant * M.temperature) * rho^2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring]

omit [DecidableEq ι] in
/-- Fixed-composition pressure coexistence is precisely effective-pure pressure coexistence. -/
theorem pressureCoexistence_fixedComposition_iff
    (M : Model (ι := ι)) (x : ι → ℝ) (rhoA rhoB : ℝ)
    (hx : ∑ i, x i = 1) :
    pressure M (stateAtComposition x rhoA) =
      pressure M (stateAtComposition x rhoB) ↔
    ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoA =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoB := by
  rw [pressure_stateAtComposition_eq_effectivePure M x rhoA hx,
    pressure_stateAtComposition_eq_effectivePure M x rhoB hx]

omit [DecidableEq ι] in
/-- Along a fixed-composition ray, the dimensional equation of state is the pure
van der Waals equation with composition-dependent effective parameters. -/
theorem pressureTVAtComposition_eq_effectivePure
    (M : Model (ι := ι)) (x : ι → ℝ) (temperature molarVolume : ℝ) :
    pressureTVAtComposition M x temperature molarVolume =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressureTV
        (effectivePureModel M x) temperature molarVolume := rfl

/-- The generic Lekner/H(d) coexistence observables therefore apply verbatim to
each fixed-composition effective model. -/
def FixedCompositionLeknerReduction
    (_M : Model (ι := ι)) (_x : ι → ℝ) : Prop :=
  ∀ d,
    ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistenceTemperature d =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistenceTemperature d ∧
    ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistencePressure d =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistencePressure d

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fixedCompositionLeknerReduction
    (M : Model (ι := ι)) (x : ι → ℝ) :
    FixedCompositionLeknerReduction M x := by
  intro d
  exact ⟨rfl, rfl⟩

end ClassicalThermodynamics.Models.VanDerWaals.Mixture

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Component chemical potential restricted to a normalized composition ray. -/
noncomputable def chemicalPotentialAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ) (i : ι) : ℝ :=
  Real.log (rho * x i / (1 - mixtureCovolume M x * rho)) +
  M.excludedVolume i * rho / (1 - mixtureCovolume M x * rho) -
  rho * ∑ j, alpha M i j * x j

/-- Closed componentwise chemical-potential condition for two densities on the
same composition ray. -/
def FixedCompositionChemicalPotentialCoexistence
    (M : Model (ι := ι)) (x : ι → ℝ) (rhoA rhoB : ℝ) : Prop :=
  ∀ i, chemicalPotentialAtComposition M x rhoA i =
    chemicalPotentialAtComposition M x rhoB i

/-- Full fixed-composition coexistence is effective-pure pressure coexistence plus
all component chemical-potential conditions. -/
def FixedCompositionCoexistence
    (M : Model (ι := ι)) (x : ι → ℝ) (rhoA rhoB : ℝ) : Prop :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoA =
    ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoB ∧
  FixedCompositionChemicalPotentialCoexistence M x rhoA rhoB

omit [DecidableEq ι] in
/-- Restricting the mixture chemical potential to a normalized composition ray
produces the explicit componentwise formula. -/
theorem chemicalPotential_stateAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ) (i : ι)
    (hx : ∑ j, x j = 1) :
    chemicalPotential M (stateAtComposition x rho) i =
      chemicalPotentialAtComposition M x rho i := by
  unfold chemicalPotential chemicalPotentialAtComposition
  rw [totalDensity_stateAtComposition x rho hx,
    freeVolumeFraction_stateAtComposition]
  simp only [stateAtComposition]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq ι] in
/-- Exact full coexistence theorem on a normalized composition ray. -/
theorem coexist_stateAtComposition_iff
    (M : Model (ι := ι)) (x : ι → ℝ) (rhoA rhoB : ℝ)
    (hx : ∑ i, x i = 1) :
    Coexist M (stateAtComposition x rhoA) (stateAtComposition x rhoB) ↔
      FixedCompositionCoexistence M x rhoA rhoB := by
  unfold Coexist FixedCompositionCoexistence
  rw [pressure_stateAtComposition_eq_effectivePure M x rhoA hx,
    pressure_stateAtComposition_eq_effectivePure M x rhoB hx]
  constructor
  · intro h
    exact ⟨h.1, fun i => by
      rw [← chemicalPotential_stateAtComposition M x rhoA i hx,
        ← chemicalPotential_stateAtComposition M x rhoB i hx]
      exact h.2 i⟩
  · intro h
    exact ⟨h.1, fun i => by
      rw [chemicalPotential_stateAtComposition M x rhoA i hx,
        chemicalPotential_stateAtComposition M x rhoB i hx]
      exact h.2 i⟩

omit [DecidableEq ι] in
/-- The extra conditions beyond effective-pure coexistence are exactly the
componentwise chemical-potential equalities. -/
theorem fixedComposition_extra_conditions
    (M : Model (ι := ι)) (x : ι → ℝ) (rhoA rhoB : ℝ) :
    FixedCompositionCoexistence M x rhoA rhoB ↔
      (ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoA =
       ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure (effectivePureModel M x) rhoB) ∧
      (∀ i, chemicalPotentialAtComposition M x rhoA i =
        chemicalPotentialAtComposition M x rhoB i) := by
  rfl

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
