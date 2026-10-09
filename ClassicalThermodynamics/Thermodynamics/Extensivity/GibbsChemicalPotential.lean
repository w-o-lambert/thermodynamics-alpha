import ClassicalThermodynamics.Thermodynamics.Extensivity.PressureIdentity
namespace ClassicalThermodynamics.Thermodynamics.Extensivity
open scoped BigOperators

theorem gibbs_eq_sum_chemicalPotentials {ι : Type*} [Fintype ι]
    {G F P V : ℝ} {mu N : ι → ℝ}
    (hG : G = F + P*V) (hF : F = -P*V + ∑ i, mu i*N i) :
    G = ∑ i, mu i*N i := by rw [hG, hF]; ring
end ClassicalThermodynamics.Thermodynamics.Extensivity
