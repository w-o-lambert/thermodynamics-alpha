import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots

/-!
# Lean 4.19 compatibility layer for the zero-sign-variation case of Descartes

The pinned Mathlib 4.19 checkout does not expose the later module
`Mathlib.Algebra.Polynomial.RuleOfSigns`.  The ClassicalThermodynamics spinodal argument
only needs its simplest corollary: a nonzero real polynomial whose nonzero
coefficients all have one sign cannot have a positive real root.

Rather than backport the full later Mathlib file, this module proves directly the
strict-coefficient case needed for characteristic polynomials, by expanding
`Polynomial.eval` as a finite sum.  When the project is upgraded to a Mathlib
release containing `Mathlib.Algebra.Polynomial.RuleOfSigns`, this module should
be replaced by a thin wrapper around `Polynomial.signVariations` and
`Polynomial.roots_countP_pos_le_signVariations`; downstream ClassicalThermodynamics APIs
should remain unchanged.
-/

namespace ClassicalThermodynamics.Math.DescartesCompatibility
open Polynomial

/-- A fixed-degree polynomial has strictly positive coefficients through degree
`n`.  This deliberately stronger certificate is exactly what the strict
alternating characteristic-polynomial convention becomes after `X ↦ -X` and an
overall sign normalization. -/
def StrictPositiveCoefficientsThrough (p : Polynomial ℝ) (n : ℕ) : Prop :=
  ∀ k, k ≤ n → 0 < p.coeff k

/-- Direct Lean-4.19 substitute for the zero-sign-variation corollary of
Descartes' rule: if every coefficient through the actual degree is positive,
the polynomial is positive on the positive half-line. -/
theorem eval_pos_of_strictPositiveCoefficients
    (p : Polynomial ℝ) (n : ℕ)
    (hdeg : p.natDegree = n)
    (hcoeff : StrictPositiveCoefficientsThrough p n)
    {x : ℝ} (hx : 0 < x) :
    0 < p.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos
  · intro k hk
    have hk' : k ≤ n := by
      have : k < p.natDegree + 1 := Finset.mem_range.mp hk
      simpa [hdeg] using (Nat.lt_succ_iff.mp this)
    exact mul_pos (hcoeff k hk') (pow_pos hx k)
  · simp

/-- Consequently such a polynomial has no positive real root. -/
theorem no_positive_root_of_strictPositiveCoefficients
    (p : Polynomial ℝ) (n : ℕ)
    (hdeg : p.natDegree = n)
    (hcoeff : StrictPositiveCoefficientsThrough p n) :
    ∀ x : ℝ, 0 < x → ¬ p.IsRoot x := by
  intro x hx hroot
  unfold Polynomial.IsRoot at hroot
  have hp := eval_pos_of_strictPositiveCoefficients p n hdeg hcoeff hx
  rw [hroot] at hp
  exact (lt_irrefl 0 hp)

end ClassicalThermodynamics.Math.DescartesCompatibility
