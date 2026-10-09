import ClassicalThermodynamics.Thermodynamics.Fundamental.FirstLaw
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Thermodynamics.Fundamental
open scoped BigOperators

def helmholtzRate (dU T dS S dT : ℝ) : ℝ := dU - (T*dS + S*dT)
def enthalpyRate (dU P dV V dP : ℝ) : ℝ := dU + (P*dV + V*dP)
def gibbsRate (dF P dV V dP : ℝ) : ℝ := dF + (P*dV + V*dP)

theorem helmholtzRate_of_firstLaw {ι : Type*} [Fintype ι]
    (T P dS dV S dT : ℝ) (mu dN : ι → ℝ)
    (hU : dU = T*dS - P*dV + ∑ i, mu i*dN i) :
    helmholtzRate dU T dS S dT = -S*dT - P*dV + ∑ i, mu i*dN i := by
  unfold helmholtzRate; rw [hU]; ring

theorem enthalpyRate_of_firstLaw {ι : Type*} [Fintype ι]
    (T P dS dV V dP : ℝ) (mu dN : ι → ℝ)
    (hU : dU = T*dS - P*dV + ∑ i, mu i*dN i) :
    enthalpyRate dU P dV V dP = T*dS + V*dP + ∑ i, mu i*dN i := by
  unfold enthalpyRate; rw [hU]; ring

theorem gibbsRate_of_helmholtz {ι : Type*} [Fintype ι]
    (S dT P dV V dP : ℝ) (mu dN : ι → ℝ)
    (hF : dF = -S*dT - P*dV + ∑ i, mu i*dN i) :
    gibbsRate dF P dV V dP = -S*dT + V*dP + ∑ i, mu i*dN i := by
  unfold gibbsRate; rw [hF]; ring
end ClassicalThermodynamics.Thermodynamics.Fundamental
