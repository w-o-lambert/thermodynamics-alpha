import ClassicalThermodynamics.Thermodynamics.Differentials.Maxwell
namespace ClassicalThermodynamics.Thermodynamics.Differentials

/-- Equality of composition cross derivatives of chemical potentials. -/
def ChemicalPotentialCrossDerivativesCommute {ι : Type*}
    (dmu : ι → ι → ℝ) : Prop := ∀ i j, dmu i j = dmu j i

/-- Temperature-composition Maxwell relation: ∂T μ_i = -∂_{N_i} S. -/
def TemperatureChemicalPotentialMaxwell {ι : Type*}
    (dmu_dT dS_dN : ι → ℝ) : Prop := ∀ i, dmu_dT i = -dS_dN i

/-- Volume-composition Maxwell relation: ∂V μ_i = -∂_{N_i} P. -/
def VolumeChemicalPotentialMaxwell {ι : Type*}
    (dmu_dV dP_dN : ι → ℝ) : Prop := ∀ i, dmu_dV i = -dP_dN i

lemma chemicalPotentialCrossDerivativesCommute_symm {ι : Type*}
    {dmu : ι → ι → ℝ} (h : ChemicalPotentialCrossDerivativesCommute dmu) :
    ∀ i j, dmu j i = dmu i j := by
  intro i j
  exact (h i j).symm

lemma entropy_amountDerivative_eq_neg_chemicalPotential_temperatureDerivative {ι : Type*}
    {dmu_dT dS_dN : ι → ℝ}
    (h : TemperatureChemicalPotentialMaxwell dmu_dT dS_dN) :
    ∀ i, dS_dN i = -dmu_dT i := by
  intro i
  linarith [h i]

end ClassicalThermodynamics.Thermodynamics.Differentials
