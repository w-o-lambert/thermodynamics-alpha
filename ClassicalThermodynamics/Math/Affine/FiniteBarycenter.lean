import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.Affine

open scoped BigOperators

variable {κ V : Type*} [Fintype κ] [AddCommGroup V] [Module ℝ V]

/-- Arithmetic mean of a finite family of vectors. -/
noncomputable def barycenter (x : κ → V) : V :=
  ((Fintype.card κ : ℝ)⁻¹) • ∑ k, x k

/-- Deviation of one family member from the finite-family barycenter. -/
noncomputable def deviation (x : κ → V) (k : κ) : V := x k - barycenter x

/-- The sum of deviations from the barycenter vanishes for a nonempty family. -/
theorem sum_deviation_eq_zero [Nonempty κ] (x : κ → V) :
    ∑ k, deviation x k = 0 := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconst : (∑ _k : κ, barycenter x) =
      (Fintype.card κ : ℝ) • barycenter x := by
    rw [Finset.sum_const]
    exact (Nat.cast_smul_eq_nsmul ℝ (Fintype.card κ) (barycenter x)).symm
  unfold deviation
  rw [Finset.sum_sub_distrib, hconst]
  unfold barycenter
  rw [← mul_smul]
  simp [hn]

/-- For two real points, the finite barycenter is the usual midpoint. -/
theorem barycenter_fin_two (x : Fin 2 → ℝ) :
    barycenter x = (x 0 + x 1) / 2 := by
  simp [barycenter, Fin.sum_univ_succ]
  ring

end ClassicalThermodynamics.Math.Affine
