import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Math
/-- A pointwise nonzero function on a nonempty type is not the zero function. -/
theorem fun_ne_zero_of_forall_ne_zero {ι : Type*} [Nonempty ι]
    {q : ι → ℝ} (hq : ∀ i, q i ≠ 0) : q ≠ 0 := by
  intro hq0
  let i : ι := Classical.choice ‹Nonempty ι›
  exact hq i (by simp [hq0])
end ClassicalThermodynamics.Math
