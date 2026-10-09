import ClassicalThermodynamics.Thermodynamics.Stability
import ClassicalThermodynamics.Thermodynamics.LocalStability
import ClassicalThermodynamics.Thermodynamics.Stability.Convexity

namespace ClassicalThermodynamics.Thermodynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive-semidefinite local stability. -/
def LocallySemistableMatrix (H : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ dotProduct x (Matrix.mulVec H x)

/-- A semistable Hessian with a nonzero kernel direction is a genuine local
stability-boundary matrix, stronger than determinant zero alone. -/
def IsLocalStabilityBoundaryMatrix (H : Matrix ι ι ℝ) : Prop :=
  LocallySemistableMatrix H ∧ HasKernelDirection H

omit [DecidableEq ι] in
/-- A semistable Hessian with a nonzero zero-second-variation direction is a
stability-boundary matrix. -/
theorem stabilityBoundary_of_zeroSecondVariation
    {H : Matrix ι ι ℝ} {secondVariation : (ι → ℝ) → ℝ}
    (hH : H.PosSemidef)
    (hRepresentation :
      Stability.SecondVariationRepresentedByHessian secondVariation H)
    (q : ι → ℝ) (hq : q ≠ 0) (hzero : secondVariation q = 0) :
    IsLocalStabilityBoundaryMatrix H := by
  constructor
  · intro x
    simpa using hH.dotProduct_mulVec_nonneg x
  · refine ⟨q, hq, ?_⟩
    exact (Stability.zeroSecondVariation_iff_hessianKernel_of_semistable
      hH secondVariation hRepresentation q).mp hzero

omit [DecidableEq ι] in
/-- Every locally stable matrix is locally semistable. -/
lemma locallyStableMatrix_implies_semistable
    {H : Matrix ι ι ℝ} (h : LocallyStableMatrix H) :
    LocallySemistableMatrix H := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [dotProduct]
  · exact le_of_lt (h x hx)

/-- A genuine local boundary matrix is singular. -/
lemma localStabilityBoundary_det_eq_zero [Nonempty ι]
    {H : Matrix ι ι ℝ} (h : IsLocalStabilityBoundaryMatrix H) :
    H.det = 0 :=
  det_eq_zero_of_hasKernelDirection h.2

omit [DecidableEq ι] in
/-- Strict local stability excludes the local-boundary predicate. -/
lemma locallyStable_not_localStabilityBoundary
    {H : Matrix ι ι ℝ} (h : LocallyStableMatrix H) :
    ¬ IsLocalStabilityBoundaryMatrix H := by
  intro hb
  exact not_hasKernelDirection_of_locallyStableMatrix h hb.2

/-- At a state-dependent Hessian, the stronger boundary predicate implies the
existing determinant-zero candidate. -/
theorem localBoundary_implies_candidate [Nonempty ι]
    {State : Type*} (H : State → Matrix ι ι ℝ) (x : State)
    (h : IsLocalStabilityBoundaryMatrix (H x)) :
    IsStabilityBoundaryCandidate ι State H x := by
  exact localStabilityBoundary_det_eq_zero h

end ClassicalThermodynamics.Thermodynamics
