import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring.RingNF

open scoped BigOperators

namespace ClassicalThermodynamics.Math.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Replace row `r` of a square matrix by the row vector `v`.
This is the algebraic operation used in the Reid--Beegle `M_i` determinants. -/
def replaceRow (A : Matrix ι ι ℝ) (r : ι) (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = r then v j else A i j

omit [Fintype ι] in
@[simp] theorem replaceRow_apply_same
    (A : Matrix ι ι ℝ) (r : ι) (v : ι → ℝ) (j : ι) :
    replaceRow A r v r j = v j := by
  simp [replaceRow]

omit [Fintype ι] in
@[simp] theorem replaceRow_apply_of_ne
    (A : Matrix ι ι ℝ) (r : ι) (v : ι → ℝ)
    {i : ι} (hir : i ≠ r) (j : ι) :
    replaceRow A r v i j = A i j := by
  simp [replaceRow, hir]

/-- Matrix-vector multiplication after a row replacement.
All unchanged rows act as before; the replaced row is the dot product `v · q`. -/
theorem replaceRow_mulVec
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ) :
    Matrix.mulVec (replaceRow A r v) q =
      fun i => if i = r then dotProduct v q else (Matrix.mulVec A q) i := by
  funext i
  by_cases hir : i = r
  · subst i
    simp [replaceRow, Matrix.mulVec, dotProduct]
  · simp [replaceRow, Matrix.mulVec, dotProduct, hir]

/-- A kernel vector of `A` remains a kernel vector after replacing one row by `v`,
provided `v` is orthogonal to that kernel vector. -/
theorem replaceRow_mulVec_eq_zero
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ)
    (hAq : Matrix.mulVec A q = 0)
    (hvq : dotProduct v q = 0) :
    Matrix.mulVec (replaceRow A r v) q = 0 := by
  rw [replaceRow_mulVec]
  funext i
  by_cases hir : i = r
  · simp [hir, hvq]
  · have hi := congrFun hAq i
    simp [hir, hi]

/-- Reid--Beegle determinant lemma: a nonzero null direction shared by the original
matrix and the replacement row forces the row-replaced determinant to vanish. -/
theorem det_replaceRow_eq_zero_of_kernel
    [Nonempty ι]
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ)
    (hq : q ≠ 0)
    (hAq : Matrix.mulVec A q = 0)
    (hvq : dotProduct v q = 0) :
    (replaceRow A r v).det = 0 := by
  exact Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨q, hq, replaceRow_mulVec_eq_zero A r v q hAq hvq⟩

end ClassicalThermodynamics.Math.Matrix

namespace ClassicalThermodynamics.Math.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Converse row-replacement lemma under an explicit pivot-row and
one-dimensional-kernel hypothesis.

The hypothesis `hkerOff` states that satisfying all rows of `A` except row `r`
already forces a vector to be a scalar multiple of `q`. This is the precise
non-degeneracy condition for a determinant formed by replacing row `r`. -/
theorem dotProduct_eq_zero_of_det_replaceRow_eq_zero
    [Nonempty ι]
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ)
    (hkerOff : ∀ x : ι → ℝ,
      (∀ i, i ≠ r → (Matrix.mulVec A x) i = 0) → ∃ a : ℝ, x = a • q)
    (hdet : (replaceRow A r v).det = 0) :
    dotProduct v q = 0 := by
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hx, hRx⟩
  have hxOff : ∀ i, i ≠ r → (Matrix.mulVec A x) i = 0 := by
    intro i hir
    have hi := congrFun hRx i
    simpa [replaceRow_mulVec, hir] using hi
  rcases hkerOff x hxOff with ⟨a, hxa⟩
  have ha : a ≠ 0 := by
    intro ha0
    apply hx
    rw [hxa, ha0]
    simp
  have hr := congrFun hRx r
  rw [replaceRow_mulVec] at hr
  simp only [ite_eq_left] at hr
  rw [hxa] at hr
  have hscale : dotProduct v (a • q) = a * dotProduct v q := by
    unfold dotProduct
    calc
      (∑ i, v i * (a * q i)) = ∑ i, a * (v i * q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = a * ∑ i, v i * q i := by
        exact (Finset.mul_sum Finset.univ (fun i => v i * q i) a).symm
  rw [hscale] at hr
  exact (mul_eq_zero.mp hr).resolve_left ha

/-- Under the same non-degeneracy assumptions, singularity of the row-replaced
matrix is equivalent to orthogonality of the replacement row to the selected
kernel direction. -/
theorem det_replaceRow_eq_zero_iff_dotProduct_eq_zero
    [Nonempty ι]
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ)
    (hq : q ≠ 0)
    (hAq : Matrix.mulVec A q = 0)
    (hkerOff : ∀ x : ι → ℝ,
      (∀ i, i ≠ r → (Matrix.mulVec A x) i = 0) → ∃ a : ℝ, x = a • q) :
    (replaceRow A r v).det = 0 ↔ dotProduct v q = 0 := by
  constructor
  · exact dotProduct_eq_zero_of_det_replaceRow_eq_zero A r v q hkerOff
  · exact det_replaceRow_eq_zero_of_kernel A r v q hq hAq

end ClassicalThermodynamics.Math.Matrix

namespace ClassicalThermodynamics.Math.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Canonical nondegeneracy assumption for the selected deleted row. -/
def KernelOffRowGeneratedBy (A : Matrix ι ι ℝ) (r : ι) (q : ι → ℝ) : Prop :=
  ∀ x : ι → ℝ,
    (∀ i, i ≠ r → (Matrix.mulVec A x) i = 0) → ∃ a : ℝ, x = a • q

/-- Canonical row-replacement equivalence under off-row kernel uniqueness. -/
theorem det_replaceRow_eq_zero_iff [Nonempty ι]
    (A : Matrix ι ι ℝ) (r : ι) (v q : ι → ℝ)
    (hq : q ≠ 0) (hAq : Matrix.mulVec A q = 0)
    (hunique : KernelOffRowGeneratedBy A r q) :
    (replaceRow A r v).det = 0 ↔ dotProduct v q = 0 :=
  det_replaceRow_eq_zero_iff_dotProduct_eq_zero A r v q hq hAq hunique

end ClassicalThermodynamics.Math.Matrix
