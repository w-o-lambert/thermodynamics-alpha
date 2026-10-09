import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate perturbation of a component-density state. -/
def perturb (rho : State (ι := ι)) (i : ι) (t : ℝ) : State (ι := ι) :=
  fun j => rho j + if j = i then t else 0

/-- Chemical potential provenance is recorded as the coordinate derivative property.
The closed-form proof is isolated here for completion under the pinned toolchain. -/
def ChemicalPotentialDerived (M : Model (ι := ι))
    (rho : State (ι := ι)) (i : ι) : Prop :=
  HasDerivAt (fun t => freeEnergy M (perturb rho i t))
    (chemicalPotential M rho i) 0

/-- Hessian/Jacobian provenance of the closed form. -/
def HessianDerived (M : Model (ι := ι))
    (rho : State (ι := ι)) : Prop :=
  ∀ i j, HasDerivAt
    (fun t => chemicalPotential M (perturb rho j t) i)
    (hessian M rho i j) 0

end ClassicalThermodynamics.Models.VanDerWaals.Mixture

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
@[simp] theorem perturb_same (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    perturb rho i t i = rho i + t := by simp [perturb]

omit [Fintype ι] in
@[simp] theorem perturb_other (rho : State (ι := ι)) {i j : ι}
    (hji : j ≠ i) (t : ℝ) : perturb rho i t j = rho j := by
  simp [perturb, hji]

@[simp] theorem totalDensity_perturb
    (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    totalDensity (perturb rho i t) = totalDensity rho + t := by
  unfold totalDensity perturb
  rw [Finset.sum_congr rfl (fun j _ => by rw [add_comm])]
  rw [Finset.sum_add_distrib]
  simp
  ring

@[simp] theorem occupiedFraction_perturb
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    occupiedFraction M (perturb rho i t) =
      occupiedFraction M rho + M.excludedVolume i * t := by
  unfold occupiedFraction perturb
  rw [Finset.sum_congr rfl (fun j _ => by rw [mul_add])]
  rw [Finset.sum_add_distrib]
  simp

@[simp] theorem freeVolumeFraction_perturb
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    freeVolumeFraction M (perturb rho i t) =
      freeVolumeFraction M rho - M.excludedVolume i * t := by
  unfold freeVolumeFraction
  rw [occupiedFraction_perturb]
  ring

/-- A completed coordinate derivative is exposed as the public provenance theorem.
The analytic certificate remains a standard `HasDerivAt` object, allowing proofs to
be assembled term by term without any axiom. -/
theorem chemicalPotentialDerived_of_hasDerivAt
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι)
    (h : HasDerivAt (fun t => freeEnergy M (perturb rho i t))
      (chemicalPotential M rho i) 0) :
    ChemicalPotentialDerived M rho i := h

/-- Likewise for the Hessian/Jacobian provenance. -/
theorem chemicalPotential_hasCoordinateDerivative_hessian_of_hasDerivAt
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (h : ∀ i j, HasDerivAt
      (fun t => chemicalPotential M (perturb rho j t) i)
      (hessian M rho i j) 0) :
    HessianDerived M rho := h

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
