import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.Projective

/-- Signed ratio coordinates used for tangent directions. -/
noncomputable def signedRatio {ι : Type*} (q : ι → ℝ) (i j : ι) : ℝ :=
  -q i / q j

/-- Signed ratios are invariant under nonzero common rescaling. -/
theorem signedRatio_smul {ι : Type*} (a : ℝ) (ha : a ≠ 0)
    (q : ι → ℝ) (i j : ι) :
    signedRatio (a • q) i j = signedRatio q i j := by
  unfold signedRatio
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hqj : q j = 0
  · simp [hqj]
  · have haj : a * q j ≠ 0 := mul_ne_zero ha hqj
    apply (div_eq_div_iff haj hqj).2
    ring

/-- Ratio coordinates satisfy the change-of-reference rule. -/
theorem signedRatio_change_reference {ι : Type*}
    (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (i j r : ι) :
    signedRatio q i j = -signedRatio q i r / signedRatio q j r := by
  unfold signedRatio
  field_simp [hq i, hq j, hq r]

/-- Reciprocal relation between two reference choices. -/
theorem signedRatio_reciprocal {ι : Type*}
    (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (i j : ι) :
    (signedRatio q i j)⁻¹ = signedRatio q j i := by
  unfold signedRatio
  field_simp [hq i, hq j]

end ClassicalThermodynamics.Math.Projective
