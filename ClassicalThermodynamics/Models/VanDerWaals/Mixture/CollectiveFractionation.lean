import ClassicalThermodynamics.Models.VanDerWaals.Mixture.LogarithmicCoexistenceCoordinates

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted collective logarithmic separation. -/
noncomputable def collectiveLogDifference
    (w d : State (ι := ι)) : ℝ := ∑ i, w i * d i

/-- Fractionation residual after subtracting the collective mode. -/
noncomputable def fractionationLogDifference
    (w d : State (ι := ι)) : State (ι := ι) :=
  fun i => d i - collectiveLogDifference w d

/-- Exact collective plus fractionation decomposition. -/
theorem collective_add_fractionation
    (w d : State (ι := ι)) (i : ι) :
    collectiveLogDifference w d + fractionationLogDifference w d i = d i := by
  unfold fractionationLogDifference
  ring

/-- For normalized weights, the fractionation residual has zero weighted mean. -/
theorem weightedSum_fractionation_eq_zero
    (w d : State (ι := ι)) (hw : ∑ i, w i = 1) :
    ∑ i, w i * fractionationLogDifference w d i = 0 := by
  unfold fractionationLogDifference collectiveLogDifference
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i, w i * (∑ j, w j * d j)) =
      (∑ i, w i) * (∑ j, w j * d j) by
    rw [Finset.sum_mul]]
  rw [hw]
  ring

/-- Constant logarithmic separation has no fractionation component. -/
theorem fractionation_constant_eq_zero
    (w : State (ι := ι)) (c : ℝ) (hw : ∑ i, w i = 1) :
    fractionationLogDifference w (fun _ => c) = 0 := by
  funext i
  unfold fractionationLogDifference collectiveLogDifference
  rw [show (∑ j, w j * c) = (∑ j, w j) * c by rw [Finset.sum_mul], hw]
  simp

/-- Vanishing fractionation means the logarithmic vector is purely collective. -/
theorem fractionation_eq_zero_iff
    (w d : State (ι := ι)) :
    fractionationLogDifference w d = 0 ↔
      d = fun _ => collectiveLogDifference w d := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    unfold fractionationLogDifference at hi
    simp at hi
    linarith
  · intro h
    funext i
    unfold fractionationLogDifference
    rw [congrFun h i]
    ring

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
