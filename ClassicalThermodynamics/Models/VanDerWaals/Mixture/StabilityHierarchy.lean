import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def hessianQuadraticForm
    (M : Model (ι := ι)) (rho q : State (ι := ι)) : ℝ :=
  ∑ i, ∑ j, q i * hessian M rho i j * q j

def LocallyStable (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  ∀ q, q ≠ 0 → 0 < hessianQuadraticForm M rho q

def WeaklyStable (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  ∀ q, 0 ≤ hessianQuadraticForm M rho q

def StabilityBoundary (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  WeaklyStable M rho ∧ BoundaryCandidate M rho

def Unstable (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  ∃ q, hessianQuadraticForm M rho q < 0

/-- A true crossing records stable and unstable states on opposite sides of a path. -/
def TrueSpinodalCrossing (M : Model (ι := ι))
    (path : ℝ → State (ι := ι)) (t0 : ℝ) : Prop :=
  StabilityBoundary M (path t0) ∧
  (∃ t, t < t0 ∧ LocallyStable M (path t)) ∧
  (∃ t, t0 < t ∧ Unstable M (path t))

/-- Positive definiteness implies positive semidefiniteness. -/
theorem locallyStable_implies_weaklyStable
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (h : LocallyStable M rho) : WeaklyStable M rho := by
  intro q
  by_cases hq : q = 0
  · subst q
    simp [hessianQuadraticForm]
  · exact le_of_lt (h q hq)

/-- A stability boundary is, in particular, a kernel boundary candidate. -/
theorem stabilityBoundary_boundaryCandidate
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (h : StabilityBoundary M rho) : BoundaryCandidate M rho := h.2

/-- Stable and unstable classifications are disjoint. -/
theorem locallyStable_not_unstable
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (hs : LocallyStable M rho) : ¬ Unstable M rho := by
  intro hu
  rcases hu with ⟨q, hq⟩
  by_cases hzero : q = 0
  · subst q
    simp [hessianQuadraticForm] at hq
  · linarith [hs q hzero]

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
