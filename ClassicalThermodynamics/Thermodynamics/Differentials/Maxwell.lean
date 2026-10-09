import ClassicalThermodynamics.Math.Calculus.MixedPartials
import ClassicalThermodynamics.Thermodynamics.Differentials.Gibbs
namespace ClassicalThermodynamics.Thermodynamics.Differentials
open ClassicalThermodynamics.Math.Calculus

/-- U(S,V): (∂T/∂V)_S = -(∂P/∂S)_V. -/
theorem internalEnergy_maxwell
    {dT_dV dP_dS : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => dT_dV) (fun _ _ => -dP_dS) 0 0) :
    dT_dV = -dP_dS := by
  exact hMixed

/-- F(T,V): (∂S/∂V)_T = (∂P/∂T)_V. -/
theorem helmholtz_maxwell
    {dS_dV dP_dT : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => -dS_dV) (fun _ _ => -dP_dT) 0 0) :
    dS_dV = dP_dT := by
  unfold MixedPartialsCommute at hMixed
  have hEq : -dS_dV = -dP_dT := by
    simpa [MixedPartialsCommute] using hMixed
  linarith

/-- H(S,P): (∂T/∂P)_S = (∂V/∂S)_P. -/
theorem enthalpy_maxwell
    {dT_dP dV_dS : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => dT_dP) (fun _ _ => dV_dS) 0 0) :
    dT_dP = dV_dS := by
  exact hMixed

/-- G(T,P): (∂S/∂P)_T = -(∂V/∂T)_P. -/
theorem gibbs_maxwell
    {dS_dP dV_dT : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => -dS_dP) (fun _ _ => dV_dT) 0 0) :
    dS_dP = -dV_dT := by
  unfold MixedPartialsCommute at hMixed
  have hEq : -dS_dP = dV_dT := by
    simpa [MixedPartialsCommute] using hMixed
  linarith

end ClassicalThermodynamics.Thermodynamics.Differentials
