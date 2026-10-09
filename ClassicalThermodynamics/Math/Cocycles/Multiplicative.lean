import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import ClassicalThermodynamics.Math.Projective.RatioCoordinates
namespace ClassicalThermodynamics.Math.Cocycles
variable {ι : Type*}
noncomputable def ratioCocycle (q : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ClassicalThermodynamics.Math.Projective.signedRatio q i j
@[simp] theorem ratioCocycle_diagonal (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (i : ι) :
    ratioCocycle q i i = -1 := by simp [ratioCocycle, ClassicalThermodynamics.Math.Projective.signedRatio, hq i]
theorem ratioCocycle_triangle (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (i j k : ι) :
    ratioCocycle q i j * ratioCocycle q j k * ratioCocycle q k i = -1 := by
  unfold ratioCocycle ClassicalThermodynamics.Math.Projective.signedRatio
  field_simp [hq i, hq j, hq k]

/-- The tangent-ratio cocycle depends only on the projective direction. -/
theorem ratioCocycle_smul (a : ℝ) (ha : a ≠ 0) (q : ι → ℝ) :
    ratioCocycle (a • q) = ratioCocycle q := by
  funext i j
  exact ClassicalThermodynamics.Math.Projective.signedRatio_smul a ha q i j

/-- Reconstruction of any ratio from ratios to an arbitrary reference component. -/
theorem ratioCocycle_change_reference (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (i j r : ι) :
    ratioCocycle q i j = -ratioCocycle q i r / ratioCocycle q j r :=
  ClassicalThermodynamics.Math.Projective.signedRatio_change_reference q hq i j r

end ClassicalThermodynamics.Math.Cocycles
