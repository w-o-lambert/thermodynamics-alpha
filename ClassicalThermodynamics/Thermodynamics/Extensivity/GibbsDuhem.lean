import ClassicalThermodynamics.Thermodynamics.Extensivity.Euler
import ClassicalThermodynamics.Thermodynamics.Fundamental.FirstLaw
namespace ClassicalThermodynamics.Thermodynamics.Extensivity
open scoped BigOperators

def GibbsDuhem {ι : Type*} [Fintype ι]
    (S dT V dP : ℝ) (N dmu : ι → ℝ) : Prop :=
  S*dT - V*dP + ∑ i, N i*dmu i = 0

/-- Gibbs-Duhem follows by subtracting the first-law differential from the
product-rule differential of the Euler relation. -/
theorem gibbsDuhem_of_eulerDifferential_and_firstLaw
    {ι : Type*} [Fintype ι]
    (T S P V dT dS dP dV dU : ℝ)
    (mu N dmu dN : ι → ℝ)
    (hEulerDiff :
      dU = T*dS + S*dT - P*dV - V*dP +
        ∑ i, (mu i*dN i + N i*dmu i))
    (hFirstLaw : dU = T*dS - P*dV + ∑ i, mu i*dN i) :
    GibbsDuhem S dT V dP N dmu := by
  unfold GibbsDuhem
  have hsplit :
      (∑ i, (mu i*dN i + N i*dmu i)) =
        (∑ i, mu i*dN i) + ∑ i, N i*dmu i := by
    rw [Finset.sum_add_distrib]
  rw [hsplit] at hEulerDiff
  linarith

/-- Constant-temperature, constant-pressure composition form. -/
lemma gibbsDuhem_isothermal_isobaric
    {ι : Type*} [Fintype ι]
    {S V : ℝ} {N dmu : ι → ℝ}
    (h : GibbsDuhem S 0 V 0 N dmu) :
    ∑ i, N i*dmu i = 0 := by
  simpa [GibbsDuhem] using h

end ClassicalThermodynamics.Thermodynamics.Extensivity
