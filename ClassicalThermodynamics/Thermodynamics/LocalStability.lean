import ClassicalThermodynamics.Math.MatrixKernel
namespace ClassicalThermodynamics.Thermodynamics
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def LocallyStableMatrix (H : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < dotProduct x (Matrix.mulVec H x)
def HasKernelDirection (H : Matrix ι ι ℝ) : Prop :=
  ∃ q : ι → ℝ, q ≠ 0 ∧ Matrix.mulVec H q = 0
lemma det_eq_zero_of_hasKernelDirection [Nonempty ι]
    {H : Matrix ι ι ℝ} (h : HasKernelDirection H) : H.det = 0 := by
  rcases h with ⟨q, hq, hHq⟩
  exact ClassicalThermodynamics.Math.det_eq_zero_of_mulVec_eq_zero H q hq hHq
omit [DecidableEq ι] in
lemma not_hasKernelDirection_of_locallyStableMatrix {H : Matrix ι ι ℝ}
    (h : LocallyStableMatrix H) : ¬ HasKernelDirection H := by
  rintro ⟨q, hq, hzero⟩
  have hp := h q hq
  rw [hzero] at hp
  simp only [dotProduct_zero, lt_self_iff_false] at hp
end ClassicalThermodynamics.Thermodynamics
