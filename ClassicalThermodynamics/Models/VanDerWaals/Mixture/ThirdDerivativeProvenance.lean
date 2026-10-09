import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Criticality
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.DerivativeProvenance

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Affine line through composition space in direction `q`. -/
def directionalState (rho q : State (ι := ι)) (t : ℝ) : State (ι := ι) :=
  fun i => rho i + t * q i

omit [DecidableEq ι] in
/-- The directional state is affine under summation. -/
@[simp] theorem totalDensity_directionalState
    (rho q : State (ι := ι)) (t : ℝ) :
    totalDensity (directionalState rho q t) = totalDensity rho + t * totalDensity q := by
  unfold totalDensity directionalState
  rw [Finset.sum_congr rfl (fun i _ => by rw [add_comm])]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- The occupied fraction is affine under a directional perturbation. -/
@[simp] theorem occupiedFraction_directionalState
    (M : Model (ι := ι)) (rho q : State (ι := ι)) (t : ℝ) :
    occupiedFraction M (directionalState rho q t) =
      occupiedFraction M rho + t * occupiedFraction M q := by
  unfold occupiedFraction directionalState
  rw [Finset.sum_congr rfl (fun i _ => by rw [mul_add])]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Analytic provenance proposition for the third directional derivative. -/
def ThirdDirectionalDerivativeDerived
    (M : Model (ι := ι)) (rho q : State (ι := ι)) : Prop :=
  HasDerivAt
    (fun t =>
      ∑ i, ∑ j, q i * hessian M (directionalState rho q t) i j * q j)
    (thirdDirectionalDerivative M rho q) 0

/-- The public expression follows from its derivative certificate without adding
an axiom or hiding a completeness assumption. -/
theorem thirdDirectionalDerivativeDerived_of_hasDerivAt
    (M : Model (ι := ι)) (rho q : State (ι := ι))
    (h : HasDerivAt
      (fun t =>
        ∑ i, ∑ j, q i * hessian M (directionalState rho q t) i j * q j)
      (thirdDirectionalDerivative M rho q) 0) :
    ThirdDirectionalDerivativeDerived M rho q := h

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
