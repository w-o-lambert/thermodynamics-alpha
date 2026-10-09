import ClassicalThermodynamics.Math.Polynomial.DescartesCompatibility
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
## Characteristic-polynomial sign certificates

This is the ClassicalThermodynamics-facing API for the ACS Omega 2025 true/ghost-spinodal
argument. It is intentionally independent of the later Mathlib
`Polynomial.RuleOfSigns` module so that the repository remains buildable on its
pinned Lean/Mathlib 4.19 baseline.

The key proof is carried out directly on the coefficient expansion of `p.eval x`.
This avoids relying on newer APIs for transformed polynomial degrees or matrix
spectrum/characteristic-root conversion. For `x < 0`, multiplication by the fixed
sign `(-1)^n` turns every summand into

`(((-1)^(n-k)) * p.coeff k) * (-x)^k`,

which is positive under strict alternation.
-/

namespace ClassicalThermodynamics.Math.CharacteristicPolynomialSigns
open Polynomial

/-- Repository convention for a degree-`n` polynomial whose coefficients
strictly alternate when read from highest degree to constant term. -/
def StrictAlternatingCoefficients (p : Polynomial ℝ) (n : ℕ) : Prop :=
  ∀ k, k ≤ n → 0 < ((-1 : ℝ) ^ (n - k)) * p.coeff k

/-- Strict alternation excludes negative real roots. This is the exact
zero-sign-variation consequence needed by the spinodal classifier, proved locally
for Mathlib 4.19 by positivity of the finite coefficient expansion. -/
theorem no_negative_root_of_strictAlternation
    (p : Polynomial ℝ) (n : ℕ) (hdeg : p.natDegree = n)
    (halt : StrictAlternatingCoefficients p n) :
    ∀ x : ℝ, x < 0 → ¬ p.IsRoot x := by
  intro x hx hroot
  let y : ℝ := -x
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hscaled : 0 < ((-1 : ℝ) ^ n) * p.eval x := by
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_pos
    · intro k hk
      have hklt : k < p.natDegree + 1 := Finset.mem_range.mp hk
      have hkn : k ≤ n := by
        rw [hdeg] at hklt
        exact Nat.lt_succ_iff.mp hklt
      have hxpow : x ^ k = (-1 : ℝ) ^ k * y ^ k := by
        have hxy : x = -y := by
          dsimp [y]
          ring
        rw [hxy, neg_pow]
      have hpow : (-1 : ℝ) ^ n =
          (-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ k := by
        rw [← pow_add]
        congr
        omega
      have hterm :
          0 < (((-1 : ℝ) ^ (n - k)) * p.coeff k) * y ^ k :=
        mul_pos (halt k hkn) (pow_pos hy k)
      rw [hxpow, hpow]
      have heven : (-1 : ℝ) ^ (k * 2) = 1 := by
        rw [mul_comm k 2, pow_mul]
        norm_num
      ring_nf
      rw [heven, mul_one]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hterm
    · simp
  unfold Polynomial.IsRoot at hroot
  rw [hroot, mul_zero] at hscaled
  exact (lt_irrefl 0 hscaled)

/-- Matrix specialization of strict alternation. -/
def MatrixStrictAlternatingCoefficients
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) : Prop :=
  StrictAlternatingCoefficients H.charpoly (Fintype.card ι)

/-- A real number is a characteristic root of `H` precisely in the sense needed
for the coefficient-sign classifier. Keeping this predicate at the charpoly layer
avoids a version-specific matrix-spectrum API. -/
def IsCharacteristicRoot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (x : ℝ) : Prop :=
  H.charpoly.IsRoot x

/-- Strict characteristic-polynomial alternation excludes negative real
characteristic roots. -/
theorem no_negative_characteristicRoot_of_strictAlternation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (halt : MatrixStrictAlternatingCoefficients H) :
    ∀ x : ℝ, x < 0 → ¬ IsCharacteristicRoot H x := by
  intro x hx
  unfold IsCharacteristicRoot
  exact no_negative_root_of_strictAlternation
    H.charpoly (Fintype.card ι)
    (by simp) halt x hx

end ClassicalThermodynamics.Math.CharacteristicPolynomialSigns
