import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Defs
namespace ClassicalThermodynamics.Thermodynamics.Fundamental
open scoped BigOperators
structure FirstLawData (ι : Type*) [Fintype ι] where
  temperature : ℝ
  pressure : ℝ
  entropyRate : ℝ
  volumeRate : ℝ
  chemicalPotential : ι → ℝ
  amountRate : ι → ℝ

def internalEnergyRate {ι : Type*} [Fintype ι] (D : FirstLawData ι) : ℝ :=
  D.temperature * D.entropyRate - D.pressure * D.volumeRate +
    ∑ i, D.chemicalPotential i * D.amountRate i

lemma firstLaw_formula {ι : Type*} [Fintype ι] (D : FirstLawData ι) :
    internalEnergyRate D = D.temperature * D.entropyRate - D.pressure * D.volumeRate +
      ∑ i, D.chemicalPotential i * D.amountRate i := rfl
end ClassicalThermodynamics.Thermodynamics.Fundamental
