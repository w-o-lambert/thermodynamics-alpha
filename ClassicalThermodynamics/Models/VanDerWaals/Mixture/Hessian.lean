import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Closed-form Hessian of the mixture free energy. -/
noncomputable def hessian (M : Model (ι := ι))
    (rho : State (ι := ι)) : Matrix ι ι ℝ :=
  fun i j =>
    (if i = j then (rho i)⁻¹ else 0) +
    (M.excludedVolume i + M.excludedVolume j) / freeVolumeFraction M rho +
    M.excludedVolume i * M.excludedVolume j * totalDensity rho /
      (freeVolumeFraction M rho)^2 -
    alpha M i j

/-- The mixture Hessian is symmetric. -/
lemma hessian_isSymm (M : Model (ι := ι))
    (rho : State (ι := ι)) : (hessian M rho).IsSymm := by
  ext i j
  change hessian M rho j i = hessian M rho i j
  unfold hessian
  have ha : alpha M j i = alpha M i j :=
    congrFun (congrFun (alpha_isSymm M) i) j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ite_false]
    rw [ha]
    ring

/-- A stability-boundary candidate has a nonzero Hessian null direction. -/
def BoundaryCandidate (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  ∃ q : ι → ℝ, q ≠ 0 ∧ Matrix.mulVec (hessian M rho) q = 0

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
