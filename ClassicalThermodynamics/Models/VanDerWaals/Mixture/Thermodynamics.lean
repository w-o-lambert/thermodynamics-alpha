import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Dimensionless Helmholtz free-energy density for the N-component mixture. -/
noncomputable def freeEnergy (M : Model (ι := ι)) (rho : State (ι := ι)) : ℝ :=
  (∑ i, rho i * (Real.log (rho i) - 1)) -
  totalDensity rho * Real.log (freeVolumeFraction M rho) -
  ∑ i, ∑ j, alpha M i j / 2 * rho i * rho j

/-- Closed-form component chemical potential. -/
noncomputable def chemicalPotential (M : Model (ι := ι))
    (rho : State (ι := ι)) (i : ι) : ℝ :=
  Real.log (rho i / freeVolumeFraction M rho) +
  M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho -
  ∑ j, alpha M i j * rho j

/-- Dimensionless pressure `P/(R T)`. -/
noncomputable def pressure (M : Model (ι := ι)) (rho : State (ι := ι)) : ℝ :=
  totalDensity rho / freeVolumeFraction M rho -
  ∑ i, ∑ j, alpha M i j / 2 * rho i * rho j

/-- Symmetry of the dimensionless attraction matrix. -/
lemma alpha_isSymm {κ : Type*} (M : Model (ι := κ)) : (alpha M).IsSymm := by
  ext i j
  change M.attraction j i / (M.gasConstant * M.temperature) =
    M.attraction i j / (M.gasConstant * M.temperature)
  exact congrArg (fun x : ℝ => x / (M.gasConstant * M.temperature))
    (congrFun (congrFun M.symmetricAttraction i) j)

/-- Pressure is the Legendre combination `sum_i rho_i mu_i - f`. -/
theorem pressure_eq_sum_rho_mul_mu_sub_freeEnergy
    {κ : Type*} [Fintype κ]
    (M : Model (ι := κ)) (rho : State (ι := κ))
    (hfree : freeVolumeFraction M rho ≠ 0) :
    pressure M rho =
      (∑ i, rho i * chemicalPotential M rho i) - freeEnergy M rho := by
  have hlog :
      (∑ i, rho i * Real.log (rho i / freeVolumeFraction M rho)) =
        (∑ i, rho i * Real.log (rho i)) -
          totalDensity rho * Real.log (freeVolumeFraction M rho) := by
    rw [show (∑ i, rho i * Real.log (rho i / freeVolumeFraction M rho)) =
        ∑ i, (rho i * Real.log (rho i) -
          rho i * Real.log (freeVolumeFraction M rho)) by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hrho : rho i = 0
      · simp [hrho]
      · rw [Real.log_div hrho hfree]
        ring]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  have hcov :
      (∑ i, rho i *
        (M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho)) =
        totalDensity rho * occupiedFraction M rho /
          freeVolumeFraction M rho := by
    rw [show (∑ i, rho i *
        (M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho)) =
        (totalDensity rho / freeVolumeFraction M rho) *
          ∑ i, M.excludedVolume i * rho i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    unfold occupiedFraction
    ring
  have hattr :
      (∑ i, rho i * ∑ j, alpha M i j * rho j) =
        ∑ i, ∑ j, alpha M i j * rho i * rho j := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hhalf :
      (∑ i, ∑ j, alpha M i j / 2 * rho i * rho j) =
        (∑ i, ∑ j, alpha M i j * rho i * rho j) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hideal :
      (∑ i, rho i * (Real.log (rho i) - 1)) =
        (∑ i, rho i * Real.log (rho i)) - totalDensity rho := by
    unfold totalDensity
    rw [show (∑ i, rho i * (Real.log (rho i) - 1)) =
        ∑ i, (rho i * Real.log (rho i) - rho i) by
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [Finset.sum_sub_distrib]
  have hmu :
      (∑ i, rho i * chemicalPotential M rho i) =
        (∑ i, rho i * Real.log (rho i)) -
          totalDensity rho * Real.log (freeVolumeFraction M rho) +
          totalDensity rho * occupiedFraction M rho /
            freeVolumeFraction M rho -
          ∑ i, ∑ j, alpha M i j * rho i * rho j := by
    unfold chemicalPotential
    rw [show (∑ i, rho i *
        (Real.log (rho i / freeVolumeFraction M rho) +
          M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho -
          ∑ j, alpha M i j * rho j)) =
        (∑ i, rho i * Real.log (rho i / freeVolumeFraction M rho)) +
        (∑ i, rho i *
          (M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho)) -
        (∑ i, rho i * ∑ j, alpha M i j * rho j) by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [hlog, hcov, hattr]
  rw [hmu]
  unfold pressure freeEnergy
  rw [hideal, hhalf]
  have hphi : freeVolumeFraction M rho = 1 - occupiedFraction M rho := rfl
  rw [hphi] at hfree ⊢
  field_simp [hfree]
  ring

/-- N-component two-phase coexistence: equality of pressure and every chemical potential. -/
def Coexist (M : Model (ι := ι)) (rhoA rhoB : State (ι := ι)) : Prop :=
  pressure M rhoA = pressure M rhoB ∧
  ∀ i, chemicalPotential M rhoA i = chemicalPotential M rhoB i

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
