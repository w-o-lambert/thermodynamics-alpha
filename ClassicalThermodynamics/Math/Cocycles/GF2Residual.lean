import ClassicalThermodynamics.Math.Cocycles.GF2
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# ACS Omega 2025, Appendix A, statements A-5--A-12

A standalone formalisation of the second half of Appendix A of

A. Bot, R. Brussee, P. Venema,
"Associative Phase Behavior and Negative Second-Order Virial Coefficients in
Analytical Calculations of the Spinodal for Complex Mixtures Composed of Many
Components", ACS Omega 10 (2025), 35170--35186.

The coefficient type is `ZMod 2`.  A sign matrix is represented as a function
`ι → ι → ZMod 2`; the results therefore do not require a particular finite
matrix size.  The distinguished index `r` is the paper's first/top row.

The file intentionally imports only Mathlib and does not depend on the
ClassicalThermodynamics repository.  It can therefore be compiled separately and later
moved into the repository's Math or Applications layer.
-/

namespace ClassicalThermodynamics.Math.Cocycles.GF2.Residual

variable {ι : Type*}

/-- Row `i` is the zero row. -/
def ZeroRow (A : SignMatrix (ι := ι)) (i : ι) : Prop := ∀ j, A i j = 0

/-- Matrices agree on row `i`. -/
def SameRow (A B : SignMatrix (ι := ι)) (i : ι) : Prop := ∀ j, A i j = B i j

/-- A minimal algebraic proxy for an admissible/physical orthant.

The thermodynamic implication from a zero sign row to failure of the strict
inequality in Equation (4) belongs in the model-facing wrapper.  This predicate
captures exactly the combinatorial condition used by A-6. -/
def RowAdmissible (A : SignMatrix (ι := ι)) : Prop := ∀ i, ¬ ZeroRow A i

/-- The cocycle selected by row `r` of `β`. -/
def cocyclePart (β : SignMatrix (ι := ι)) (r : ι) : SignMatrix (ι := ι) :=
  fun i j => β r i + β r j

/-- The residual/noncocycle part selected by row `r`. -/
def residualPart (β : SignMatrix (ι := ι)) (r : ι) : SignMatrix (ι := ι) :=
  fun i j => β i j + cocyclePart β r i j

/-- A row translated by the distinguished row `r`.
This is the row-vector form of `Δβ + β(1) 1_N` in A-12. -/
def translatedRow (Δ β : SignMatrix (ι := ι)) (r i : ι) : ι → ZMod 2 :=
  fun j => Δ i j + β r j

/-! ## A-5 and A-6 -/

/-- **A-5.** Equal rows cancel in characteristic two. -/
theorem A5_same_row_gives_zero_row
    (β σ : SignMatrix (ι := ι)) (i : ι) (hrow : SameRow β σ i) :
    ZeroRow (fun p q => β p q + σ p q) i := by
  intro j
  change β i j + σ i j = 0
  rw [hrow j]
  exact add_self_zmod2 (σ i j)

/-- **A-6, combinatorial core.** If `β` and `σ` share a row, their sum is not
row-admissible.  The paper's thermodynamic conclusion follows by combining
this theorem with Equation (4), whose inequality is strict. -/
theorem A6_same_row_not_admissible
    (β σ : SignMatrix (ι := ι)) (i : ι) (hrow : SameRow β σ i) :
    ¬ RowAdmissible (fun p q => β p q + σ p q) := by
  intro h
  exact h i (A5_same_row_gives_zero_row β σ i hrow)

/-! ## A-7: canonical decomposition -/

/-- The explicit row-generated part is a cocycle. -/
theorem cocyclePart_isCocycle
    (β : SignMatrix (ι := ι)) (r : ι) : IsCocycle (cocyclePart β r) := by
  constructor
  · intro i
    exact add_self_zmod2 (β r i)
  · intro i j k
    simp only [cocyclePart]
    calc
      (β r i + β r j) + (β r j + β r k) + (β r k + β r i) =
          (β r i + β r i) + (β r j + β r j) + (β r k + β r k) := by abel
      _ = 0 := by simp [add_self_zmod2]
/-- If `β` is symmetric and has zero diagonal, its residual is symmetric. -/
theorem residualPart_symmetric
    (β : SignMatrix (ι := ι)) (r : ι) (hsym : β.IsSymm) :
    (residualPart β r).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, residualPart, cocyclePart]
  have hβ : β j i = β i j := congrFun (congrFun hsym i) j
  rw [hβ]
  abel
/-- Under the paper's zero-diagonal hypothesis, the selected row of the
residual vanishes. -/
theorem residualPart_zero_row
    (β : SignMatrix (ι := ι)) (r : ι) (hdiag : β r r = 0) :
    ZeroRow (residualPart β r) r := by
  intro j
  simp only [residualPart, cocyclePart, hdiag, zero_add]
  exact add_self_zmod2 (β r j)
/-- Reconstruction identity for the canonical decomposition. -/
theorem canonical_decomposition
    (β : SignMatrix (ι := ι)) (r i j : ι) :
    β i j = cocyclePart β r i j + residualPart β r i j := by
  simp only [cocyclePart, residualPart]
  calc
    β i j = β i j + 0 := by rw [add_zero]
    _ = β i j + ((β r i + β r j) + (β r i + β r j)) := by rw [add_self_zmod2]
    _ = (β r i + β r j) + (β i j + (β r i + β r j)) := by abel
/-- A cocycle is determined by any one of its rows.  This is the row-`r`
formula used in A-2 and in the uniqueness argument of A-7. -/
theorem cocycle_eq_row_formula
    (σ : SignMatrix (ι := ι)) (r i j : ι) (hσ : IsCocycle σ) :
    σ i j = σ r i + σ r j := by
  rw [cocycle_eq_from_row σ hσ r i j, cocycle_symm σ hσ i r]

/-- A cocycle with zero distinguished row is the zero matrix. -/
theorem cocycle_zero_of_zero_row
    (σ : SignMatrix (ι := ι)) (r : ι) (hσ : IsCocycle σ) (hrow : ZeroRow σ r) :
    σ = 0 := by
  funext i j
  rw [cocycle_eq_row_formula σ r i j hσ, hrow i, hrow j]
  simp

/-- **A-7.** Existence and uniqueness of the decomposition into a cocycle and
a symmetric residual with zero distinguished row.

Rather than reproducing the paper's dimension count, Lean proves uniqueness
constructively from A-2: the zero-row condition forces the cocycle part to be
exactly `cocyclePart β r`. -/
theorem A7_unique_decomposition
    (β σ Δ : SignMatrix (ι := ι)) (r : ι)
    (hβdiag : β r r = 0)
    (hσ : IsCocycle σ)
    (hΔrow : ZeroRow Δ r)
    (hdecomp : ∀ i j, β i j = σ i j + Δ i j) :
    σ = cocyclePart β r ∧ Δ = residualPart β r := by
  have _ := hβdiag
  have hσrow : ∀ j, σ r j = β r j := by
    intro j
    have h := hdecomp r j
    rw [hΔrow j, add_zero] at h
    exact h.symm
  constructor
  · funext i j
    rw [cocycle_eq_row_formula σ r i j hσ, hσrow i, hσrow j]
    rfl
  · funext i j
    have h := hdecomp i j
    have hs : σ i j = cocyclePart β r i j := by
      rw [cocycle_eq_row_formula σ r i j hσ, hσrow i, hσrow j]
      rfl
    rw [hs] at h
    simp only [residualPart]
    calc
      Δ i j = 0 + Δ i j := by rw [zero_add]
      _ = (cocyclePart β r i j + cocyclePart β r i j) + Δ i j := by
        rw [add_self_zmod2]
      _ = cocyclePart β r i j + (cocyclePart β r i j + Δ i j) := by abel
      _ = cocyclePart β r i j + β i j := by rw [← h]
      _ = β i j + cocyclePart β r i j := by abel

/-! ## A-8 and A-9: dependence on the residual -/

/-- **A-8, algebraic identity.** The cocycle part translates the orthant:
`β + σ = Δβ + (σ + σ')`. -/
theorem A8_orthant_translation
    (σ σ' Δ : SignMatrix (ι := ι)) (i j : ι) :
    (σ' i j + Δ i j) + σ i j = Δ i j + (σ i j + σ' i j) := by
  ring_nf

/-- The sum of two cocycles is a cocycle, used in A-8 and A-9. -/
theorem add_cocycle
    (σ σ' : SignMatrix (ι := ι)) (hσ : IsCocycle σ) (hσ' : IsCocycle σ') :
    IsCocycle (fun i j => σ i j + σ' i j) := by
  constructor
  · intro i
    change σ i i + σ' i i = 0
    rw [hσ.1 i, hσ'.1 i, zero_add]
  · intro i j k
    have h1 := hσ.2 i j k
    have h2 := hσ'.2 i j k
    calc
      (σ i j + σ' i j) + (σ j k + σ' j k) + (σ k i + σ' k i) =
          (σ i j + σ j k + σ k i) + (σ' i j + σ' j k + σ' k i) := by abel
      _ = 0 := by rw [h1, h2, add_zero]

/-- **A-9, precise combinatorial form.** Two matrices with the same residual
produce exactly the same family of sum matrices when the orthant cocycle ranges
over all cocycles. -/
theorem A9_same_residual_same_sum_family
    (σ₁ σ₂ Δ τ : SignMatrix (ι := ι))
    (hσ₁ : IsCocycle σ₁) (hσ₂ : IsCocycle σ₂) (hτ : IsCocycle τ) :
    ∃ τ' : SignMatrix (ι := ι),
      IsCocycle τ' ∧
      (∀ i j, (σ₁ i j + Δ i j) + τ i j = (σ₂ i j + Δ i j) + τ' i j) := by
  let τ' : SignMatrix (ι := ι) := fun i j => τ i j + σ₁ i j + σ₂ i j
  refine ⟨τ', ?_, ?_⟩
  · exact add_cocycle (fun i j => τ i j + σ₁ i j) σ₂
      (add_cocycle τ σ₁ hτ hσ₁) hσ₂
  · intro i j
    dsimp [τ']
    calc
      σ₁ i j + Δ i j + τ i j = σ₁ i j + Δ i j + τ i j + 0 := by rw [add_zero]
      _ = σ₁ i j + Δ i j + τ i j + (σ₂ i j + σ₂ i j) := by
        rw [add_self_zmod2]
      _ = σ₂ i j + Δ i j + (τ i j + σ₁ i j + σ₂ i j) := by abel

/-! ## A-10--A-12: empty-orthant signatures -/

/-- **A-10, cancellation form.** If row `i` of `Δ` equals row `i` of `σ`,
then row `i` of their sum is zero.

The Appendix derives the row equality from its top-row/cocycle hypotheses.
Keeping that derivation separate makes the exact logical requirement explicit. -/
theorem A10_matching_row_gives_zero_row
    (σ Δ : SignMatrix (ι := ι)) (i : ι) (hrow : SameRow Δ σ i) :
    ZeroRow (fun p q => σ p q + Δ p q) i := by
  intro j
  change σ i j + Δ i j = 0
  rw [hrow j]
  exact add_self_zmod2 (σ i j)

/-- The paper's top-row criterion implies the row equality needed by A-10. -/
theorem A10_top_row_criterion
    (σ Δ : SignMatrix (ι := ι)) (r i : ι)
    (hσ : IsCocycle σ)
    (hσri : σ r i = 0)
    (hrow : ∀ j, Δ i j = σ r j) :
    ZeroRow (fun p q => σ p q + Δ p q) i := by
  apply A10_matching_row_gives_zero_row σ Δ i
  intro j
  rw [hrow j, cocycle_eq_row_formula σ r i j hσ, hσri]
  simp

/-- **A-11, injective counting core.** Distinct residual row patterns give
distinct orthant signatures after translation by the same row. -/
theorem A11_distinct_rows_give_distinct_signatures
    (Δ β : SignMatrix (ι := ι)) (r i k : ι)
    (hneq : (fun j => Δ i j) ≠ (fun j => Δ k j)) :
    translatedRow Δ β r i ≠ translatedRow Δ β r k := by
  intro h
  apply hneq
  funext j
  have hj := congrFun h j
  simp only [translatedRow] at hj
  exact add_right_cancel hj

/-- **A-12, translation invariance.** Adding the same row `v` to both sign
matrices leaves their sum unchanged.  This is the algebraic reason that the
rows of `Δβ + β(1) 1_N` list the empty orthants for a general `β`. -/
theorem A12_common_row_translation_invariant
    (A B : SignMatrix (ι := ι)) (v : ι → ZMod 2) (i j : ι) :
    (A i j + v j) + (B i j + v j) = A i j + B i j := by
  calc
    (A i j + v j) + (B i j + v j) = (A i j + B i j) + (v j + v j) := by abel
    _ = A i j + B i j := by rw [add_self_zmod2, add_zero]

/-- Matrix-level version of A-12. -/
theorem A12_common_translation_preserves_zero_row
    (A B : SignMatrix (ι := ι)) (v : ι → ZMod 2) (i : ι) :
    ZeroRow (fun p q => A p q + B p q) i ↔
      ZeroRow (fun p q => (A p q + v q) + (B p q + v q)) i := by
  constructor
  · intro h j
    change (A i j + v j) + (B i j + v j) = 0
    rw [A12_common_row_translation_invariant A B v i j]
    exact h j
  · intro h j
    have hj := h j
    change (A i j + v j) + (B i j + v j) = 0 at hj
    rw [A12_common_row_translation_invariant A B v i j] at hj
    exact hj

end ClassicalThermodynamics.Math.Cocycles.GF2.Residual
