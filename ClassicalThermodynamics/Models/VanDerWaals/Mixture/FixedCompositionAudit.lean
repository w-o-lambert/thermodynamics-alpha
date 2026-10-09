import ClassicalThermodynamics.Models.VanDerWaals.Mixture.FixedCompositionCoexistence

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Dimensionless attraction experienced by component `i` along composition `x`. -/
noncomputable def componentAttractionAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, alpha M i j * x j

omit [DecidableEq ι] in
/-- Audited decomposition of the fixed-composition chemical potential into ideal,
free-volume, covolume, and attraction contributions. -/
theorem chemicalPotentialAtComposition_decomposition
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ) (i : ι)
    (hnum : rho * x i ≠ 0)
    (hfree : 1 - mixtureCovolume M x * rho ≠ 0) :
    chemicalPotentialAtComposition M x rho i =
      Real.log (rho * x i) - Real.log (1 - mixtureCovolume M x * rho) +
      M.excludedVolume i * rho / (1 - mixtureCovolume M x * rho) -
      rho * componentAttractionAtComposition M x i := by
  unfold chemicalPotentialAtComposition componentAttractionAtComposition
  rw [Real.log_div hnum hfree]

omit [DecidableEq ι] in
/-- The attraction contribution is consistent with differentiating the symmetric
quadratic free-energy term: its composition-weighted mean is twice the effective
quadratic coefficient. -/
theorem sum_x_mul_componentAttraction
    (M : Model (ι := ι)) (x : ι → ℝ) :
    ∑ i, x i * componentAttractionAtComposition M x i =
      2 * mixtureAttraction M x / (M.gasConstant * M.temperature) := by
  unfold componentAttractionAtComposition mixtureAttraction alpha
  have hsum :
      (∑ i, x i * ∑ j, (M.attraction i j /
        (M.gasConstant * M.temperature)) * x j) =
      (∑ i, ∑ j, x i * M.attraction i j * x j) /
        (M.gasConstant * M.temperature) := by
    calc
      (∑ i, x i * ∑ j, (M.attraction i j /
          (M.gasConstant * M.temperature)) * x j) =
          ∑ i, ∑ j, x i * (M.attraction i j /
            (M.gasConstant * M.temperature)) * x j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, ∑ j,
          (x i * M.attraction i j * x j) /
            (M.gasConstant * M.temperature) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ i, ∑ j, x i * M.attraction i j * x j) /
          (M.gasConstant * M.temperature) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
  rw [hsum]
  have htwice :
      2 * (∑ i, ∑ j, x i * M.attraction i j * x j / 2) =
        ∑ i, ∑ j, x i * M.attraction i j * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [htwice]

omit [DecidableEq ι] in
/-- Along a normalized composition ray, the weighted component chemical potentials
obey the same Legendre identity as the full mixture theory. -/
theorem pressure_eq_rho_mul_weightedChemicalPotential_sub_freeEnergy
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ)
    (hx : ∑ i, x i = 1)
    (hfree : 1 - mixtureCovolume M x * rho ≠ 0) :
    pressure M (stateAtComposition x rho) =
      rho * (∑ i, x i * chemicalPotentialAtComposition M x rho i) -
        freeEnergy M (stateAtComposition x rho) := by
  have hleg := pressure_eq_sum_rho_mul_mu_sub_freeEnergy
    M (stateAtComposition x rho)
    (by simpa [freeVolumeFraction_stateAtComposition] using hfree)
  rw [hleg]
  congr 1
  rw [show (∑ i, stateAtComposition x rho i *
      chemicalPotential M (stateAtComposition x rho) i) =
      rho * ∑ i, x i * chemicalPotentialAtComposition M x rho i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [chemicalPotential_stateAtComposition M x rho i hx]
    unfold stateAtComposition
    ring]

omit [DecidableEq ι] in
/-- Audit conclusion: the restricted formula is exactly the general mixture
chemical potential on a normalized composition ray. -/
theorem fixedCompositionChemicalPotential_thermodynamicallyConsistent
    (M : Model (ι := ι)) (x : ι → ℝ) (rho : ℝ)
    (hx : ∑ i, x i = 1) :
    ∀ i, chemicalPotentialAtComposition M x rho i =
      chemicalPotential M (stateAtComposition x rho) i := by
  intro i
  exact (chemicalPotential_stateAtComposition M x rho i hx).symm

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
