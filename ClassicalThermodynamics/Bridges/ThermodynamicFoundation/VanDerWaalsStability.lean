import ClassicalThermodynamics.Thermodynamics.Stability.Convexity
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.StabilityHierarchy

namespace ClassicalThermodynamics.Bridges.ThermodynamicFoundation
open scoped BigOperators
open ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hessianQuadraticForm_eq_dotProduct
    (M : Model (ι := ι)) (rho q : State (ι := ι)) :
    hessianQuadraticForm M rho q =
      dotProduct q (Matrix.mulVec (hessian M rho) q) := by
  simp only [hessianQuadraticForm, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem locallyStable_iff_foundation
    (M : Model (ι := ι)) (rho : State (ι := ι)) :
    LocallyStable M rho ↔
      ClassicalThermodynamics.Thermodynamics.Stability.StrictLocalThermodynamicStability
        (hessian M rho) := by
  constructor <;> intro h q hq
  · rw [← hessianQuadraticForm_eq_dotProduct]
    exact h q hq
  · rw [hessianQuadraticForm_eq_dotProduct]
    exact h q hq

theorem weaklyStable_iff_foundation
    (M : Model (ι := ι)) (rho : State (ι := ι)) :
    WeaklyStable M rho ↔
      ClassicalThermodynamics.Thermodynamics.Stability.LocalThermodynamicSemistability
        (hessian M rho) := by
  constructor <;> intro h q
  · rw [← hessianQuadraticForm_eq_dotProduct]
    exact h q
  · rw [hessianQuadraticForm_eq_dotProduct]
    exact h q

end ClassicalThermodynamics.Bridges.ThermodynamicFoundation
