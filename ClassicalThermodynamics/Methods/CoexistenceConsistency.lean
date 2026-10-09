import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Methods

open scoped BigOperators

/-- Model-independent pairwise coexistence consistency functional used by the
2023 and 2024 ACS Omega application layers. -/
noncomputable def coexistenceConsistency
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  (∑ i, (a i - b i)) +
    (1 / 2 : ℝ) * ∑ i, (a i + b i) * Real.log (b i / a i)

/-- Reversing the two phases negates the pairwise consistency functional. -/
theorem coexistenceConsistency_swap
    {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hposA : ∀ i, 0 < a i) (hposB : ∀ i, 0 < b i) :
    coexistenceConsistency b a = -coexistenceConsistency a b := by
  unfold coexistenceConsistency
  have hlog : ∀ i, Real.log (a i / b i) = -Real.log (b i / a i) := by
    intro i
    rw [Real.log_div (ne_of_gt (hposA i)) (ne_of_gt (hposB i)),
      Real.log_div (ne_of_gt (hposB i)) (ne_of_gt (hposA i))]
    ring
  calc
    (∑ i, (b i - a i)) + (1 / 2 : ℝ) *
        ∑ i, (b i + a i) * Real.log (a i / b i) =
      -(∑ i, (a i - b i)) - (1 / 2 : ℝ) *
        ∑ i, (a i + b i) * Real.log (b i / a i) := by
          rw [show (∑ i, (b i - a i)) = -(∑ i, (a i - b i)) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
          rw [show (∑ i, (b i + a i) * Real.log (a i / b i)) =
              -(∑ i, (a i + b i) * Real.log (b i / a i)) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hlog i]
            ring]
          ring
    _ = -((∑ i, (a i - b i)) + (1 / 2 : ℝ) *
        ∑ i, (a i + b i) * Real.log (b i / a i)) := by ring

end ClassicalThermodynamics.Methods
