import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
import ClassicalThermodynamics.Thermodynamics.Extensivity.PressureIdentity

namespace ClassicalThermodynamics.Thermodynamics.Extensivity

open scoped BigOperators

/-- A pointwise second Frechet derivative certificate.

`D` is a (chosen) Frechet derivative field for `f`, and `K` is the Frechet
derivative of that field.  Keeping the derivative field explicit is useful
for model provenance: a model can expose `D` and its derivative without
having to identify either one with `fderiv`. -/
def HasSecondFDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F)
    (K : E → E →L[ℝ] (E →L[ℝ] F)) (x : E) : Prop :=
  HasFDerivAt f (D x) x ∧ HasFDerivAt D (K x) x

lemma HasSecondFDerivAt.first
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : E → E →L[ℝ] F}
    {K : E → E →L[ℝ] (E →L[ℝ] F)} {x : E}
    (h : HasSecondFDerivAt f D K x) :
    HasFDerivAt f (D x) x :=
  h.1

lemma HasSecondFDerivAt.second
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : E → E →L[ℝ] F}
    {K : E → E →L[ℝ] (E →L[ℝ] F)} {x : E}
    (h : HasSecondFDerivAt f D K x) :
    HasFDerivAt D (K x) x :=
  h.2

/-- Transfer a genuine second derivative across the zero-volume branch.

The derivative field `D` is deliberately shared by the two certificates.
Thus this is not a statement about a merely equal value: it transfers the
derivative of the derivative field as well.  This theorem transfers a certificate for the
already-composed product expression; a separate second-order chain-rule
construction is still needed to turn a density-level Hessian field into such
a `D`/`K` pair.  Keeping that distinction explicit prevents a first-derivative
certificate from being mistaken for genuine Hessian provenance. -/
theorem extensiveFreeEnergy_hasSecondFDerivAt_of_product
    {ι : Type*} [Fintype ι]
    (densityFreeEnergy : (ι → ℝ) → ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    {D : (ℝ × (ι → ℝ)) → (ℝ × (ι → ℝ)) →L[ℝ] ℝ}
    {K : (ℝ × (ι → ℝ)) →
      (ℝ × (ι → ℝ)) →L[ℝ] ((ℝ × (ι → ℝ)) →L[ℝ] ℝ)}
    (hproduct :
      HasSecondFDerivAt
        (fun x : ℝ × (ι → ℝ) =>
          x.1 * densityFreeEnergy (densityState x.1 x.2)) D K
        (volume, amount)) :
    HasSecondFDerivAt
      (fun x : ℝ × (ι → ℝ) =>
        extensiveFreeEnergy densityFreeEnergy x.1 x.2) D K
      (volume, amount) :=
  ⟨extensiveFreeEnergy_hasFDerivAt_of_product densityFreeEnergy hvolume
      amount hproduct.1, hproduct.2⟩

/-- The derivative-level conjugate condition used to identify pressure.

Unlike an evaluation hypothesis, this records that the model Frechet
derivative is the thermodynamic covector `-P dV + ∑ μᵢ dNᵢ`. -/
def IsThermodynamicConjugate
    {ι : Type*} [Fintype ι]
    (G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ) (P : ℝ) (mu : ι → ℝ) : Prop :=
  G =
    (-P) • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) +
      ∑ i, mu i •
        (ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))

/-- Pressure canonically read from a Frechet derivative covector. -/
noncomputable def pressureOfExtensiveDerivative
    {ι : Type*} (G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ) : ℝ :=
  -G (1, 0)

/-- Chemical potentials canonically read on the composition coordinate basis. -/
noncomputable def chemicalPotentialOfExtensiveDerivative
    {ι : Type*} [DecidableEq ι]
    (G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ) (i : ι) : ℝ :=
  G (0, Pi.single i 1)

theorem extensiveDerivative_isThermodynamicConjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ) :
    IsThermodynamicConjugate G
      (pressureOfExtensiveDerivative G) (chemicalPotentialOfExtensiveDerivative G) := by
  apply ContinuousLinearMap.ext
  intro x
  rcases x with ⟨v, n⟩
  simp [IsThermodynamicConjugate, pressureOfExtensiveDerivative,
    chemicalPotentialOfExtensiveDerivative]
  have hn : n = ∑ i, n i • Pi.single i 1 := by
    ext j
    classical
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro a ha hne
      simp [Pi.single_apply, hne]
    · simp
  rw [hn]
  have hv : (v, (0 : ι → ℝ)) = v • (1, 0) := by
    ext <;> simp
  have hdecomp :
      (v, ∑ i, n i • Pi.single i 1) =
        (v, 0) + (0, ∑ i, n i • Pi.single i 1) := by
    ext <;> simp
  have hsum :
      G (0, ∑ i : ι, n i • Pi.single i 1) =
        ∑ i : ι, n i * G (0, Pi.single i 1) := by
    calc
      G (0, ∑ i : ι, n i • Pi.single i 1) =
          (G.comp (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)))
            (∑ i : ι, n i • Pi.single i 1) := by rfl
      _ = ∑ i : ι, (G.comp (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)))
          (n i • Pi.single i 1) := by
        rw [map_sum]
      _ = ∑ i : ι, n i * G (0, Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [map_smul]
  rw [hdecomp, map_add, hv, map_smul]
  rw [hsum]
  rw [← hn]
  apply congrArg₂ (· + ·) (by ring)
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem extensiveEuler_pressure_identity_of_conjugate
    {ι : Type*} [Fintype ι]
    (F : (ℝ × (ι → ℝ)) → ℝ) (V : ℝ) (N : ι → ℝ)
    (P : ℝ) (mu : ι → ℝ)
    {G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ}
    (hF : HasFDerivAt F G (V, N))
    (hconj : IsThermodynamicConjugate G P mu)
    (hhom : OneHomogeneous F) :
    P * V = -F (V, N) + ∑ i, mu i * N i := by
  have hEuler : G (V, N) = F (V, N) :=
    euler_of_oneHomogeneous F (V, N) G hhom hF
  have hvalue : G (V, N) = -P * V + ∑ i, mu i * N i := by
    rw [hconj]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply]
    simp
  rw [← hEuler, hvalue]
  ring

theorem extensiveEuler_pressure_identity_of_frechet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ℝ × (ι → ℝ)) → ℝ) (V : ℝ) (N : ι → ℝ)
    {G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ}
    (hF : HasFDerivAt F G (V, N))
    (hhom : OneHomogeneous F) :
    pressureOfExtensiveDerivative G * V =
      -F (V, N) +
        ∑ i, chemicalPotentialOfExtensiveDerivative G i * N i := by
  exact extensiveEuler_pressure_identity_of_conjugate
    F V N (pressureOfExtensiveDerivative G)
    (chemicalPotentialOfExtensiveDerivative G) hF
    (extensiveDerivative_isThermodynamicConjugate G) hhom

end ClassicalThermodynamics.Thermodynamics.Extensivity
