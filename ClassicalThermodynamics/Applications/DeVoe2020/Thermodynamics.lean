import ClassicalThermodynamics.Thermodynamics.Fundamental.FirstLaw
import ClassicalThermodynamics.Thermodynamics.Fundamental.SecondLaw
import ClassicalThermodynamics.Thermodynamics.Fundamental.ThirdLaw
import ClassicalThermodynamics.Thermodynamics.Fundamental.LegendreDifferentials
import ClassicalThermodynamics.Thermodynamics.Potentials.Identities
import ClassicalThermodynamics.Thermodynamics.Differentials.Maxwell
import ClassicalThermodynamics.Thermodynamics.Relations.Clapeyron
import ClassicalThermodynamics.Thermodynamics.Relations.GibbsHelmholtz
import ClassicalThermodynamics.Thermodynamics.Relations.JouleThomson
import ClassicalThermodynamics.Thermodynamics.Relations.Kirchhoff
import ClassicalThermodynamics.Thermodynamics.Relations.VanTHoff
import ClassicalThermodynamics.Thermodynamics.Equilibrium.GibbsPhaseRule
import ClassicalThermodynamics.Math.Calculus.MixedPartials

/-!
# DeVoe (2020): general thermodynamic relations

Thin equation wrappers for Howard DeVoe, *Thermodynamics and Chemistry*,
second edition (2020). They reuse the current formal declarations and do not
replace their hypotheses with stronger source claims.

The source assumptions matter: DeVoe's Maxwell relations in Sec. 5.4 are for a
closed, single-component system with expansion work only. The current
certificate-style Maxwell declarations retain their mixed-partial premise and
do not derive it from state functions.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

open scoped BigOperators
open ClassicalThermodynamics.Thermodynamics.Fundamental
open ClassicalThermodynamics.Thermodynamics.Potentials
open ClassicalThermodynamics.Thermodynamics.Differentials
open ClassicalThermodynamics.Thermodynamics.Equilibrium
open ClassicalThermodynamics.Thermodynamics.Relations
open ClassicalThermodynamics.Math.Calculus

section Potentials

/-- DeVoe (2020), Eq. (5.3.1): `H = U + p V`. -/
theorem eq_5_3_1_enthalpy (U p V : ℝ) :
    enthalpyFromInternal U p V = U + p * V := rfl

/-- DeVoe (2020), Eq. (5.3.2): `A = U - T S`. -/
theorem eq_5_3_2_helmholtz (U T S : ℝ) :
    helmholtzFromInternal U T S = U - T * S := rfl

/-- DeVoe (2020), Eq. (5.3.3): `G = U - T S + p V`. -/
theorem eq_5_3_3_gibbs (U T S p V : ℝ) :
    gibbsFromHelmholtz (helmholtzFromInternal U T S) p V =
      U - T * S + p * V :=
  by
    rw [gibbsFromHelmholtz_eq_internal]
    ring

/-- DeVoe (2020), Eq. (5.3.4): `dH = dU + p dV + V dp`. -/
theorem eq_5_3_4_enthalpy_differential
    (dU p dV V dp : ℝ) :
    enthalpyRate dU p dV V dp = dU + (p * dV + V * dp) := rfl

/-- DeVoe (2020), Eq. (5.3.5): `dA = dU - T dS - S dT`. -/
theorem eq_5_3_5_helmholtz_differential
    (dU T dS S dT : ℝ) :
    helmholtzRate dU T dS S dT = dU - (T * dS + S * dT) := rfl

/-- DeVoe (2020), Eq. (5.3.6): `dG = dA + p dV + V dp`. -/
theorem eq_5_3_6_gibbs_differential
    (dA p dV V dp : ℝ) :
    gibbsRate dA p dV V dp = dA + (p * dV + V * dp) := rfl

variable {ι : Type*} [Fintype ι]

/-- DeVoe (2020), Eq. (5.5.6), open-system internal-energy differential. -/
theorem eq_5_5_6_internal_energy (D : FirstLawData ι) :
    internalEnergyRate D =
      D.temperature * D.entropyRate - D.pressure * D.volumeRate +
        ∑ i, D.chemicalPotential i * D.amountRate i :=
  firstLaw_formula D

/-- DeVoe (2020), Eq. (5.5.7), enthalpy differential given Eq. (5.5.6). -/
theorem eq_5_5_7_enthalpy
    (dU T p dS dV V dp : ℝ) (mu dn : ι → ℝ)
    (hU : dU = T * dS - p * dV + ∑ i, mu i * dn i) :
    enthalpyRate dU p dV V dp =
      T * dS + V * dp + ∑ i, mu i * dn i :=
  enthalpyRate_of_firstLaw T p dS dV V dp mu dn hU

/-- DeVoe (2020), Eq. (5.5.8), Helmholtz-energy differential given Eq. (5.5.6). -/
theorem eq_5_5_8_helmholtz
    (dU T p dS dV S dT : ℝ) (mu dn : ι → ℝ)
    (hU : dU = T * dS - p * dV + ∑ i, mu i * dn i) :
    helmholtzRate dU T dS S dT =
      -S * dT - p * dV + ∑ i, mu i * dn i :=
  helmholtzRate_of_firstLaw T p dS dV S dT mu dn hU

/-- DeVoe (2020), Eq. (5.5.9), Gibbs-energy differential given Eq. (5.5.8). -/
theorem eq_5_5_9_gibbs
    (dA S dT p dV V dp : ℝ) (mu dn : ι → ℝ)
    (hA : dA = -S * dT - p * dV + ∑ i, mu i * dn i) :
    gibbsRate dA p dV V dp =
      -S * dT + V * dp + ∑ i, mu i * dn i :=
  gibbsRate_of_helmholtz S dT p dV V dp mu dn hA

end Potentials

section MaxwellRelations

/-- DeVoe (2020), Eq. (5.4.15), the internal-energy Maxwell relation.

The formal theorem retains the mixed-partial certificate as an explicit
hypothesis; it does not establish differentiability of a thermodynamic state
function.
-/
theorem eq_5_4_15_internal_energy_maxwell
    {dT_dV dP_dS : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => dT_dV) (fun _ _ => -dP_dS) 0 0) :
    dT_dV = -dP_dS :=
  internalEnergy_maxwell hMixed

/-- DeVoe (2020), Eq. (5.4.16), the enthalpy Maxwell relation. -/
theorem eq_5_4_16_enthalpy_maxwell
    {dT_dP dV_dS : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => dT_dP) (fun _ _ => dV_dS) 0 0) :
    dT_dP = dV_dS :=
  enthalpy_maxwell hMixed

/-- DeVoe (2020), Eq. (5.4.17), the Helmholtz-energy Maxwell relation. -/
theorem eq_5_4_17_helmholtz_maxwell
    {dS_dV dP_dT : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => -dS_dV) (fun _ _ => -dP_dT) 0 0) :
    dS_dV = dP_dT :=
  helmholtz_maxwell hMixed

/-- DeVoe (2020), Eq. (5.4.18), the Gibbs-energy Maxwell relation. -/
theorem eq_5_4_18_gibbs_maxwell
    {dS_dP dV_dT : ℝ}
    (hMixed : MixedPartialsCommute
      (fun _ _ => -dS_dP) (fun _ _ => dV_dT) 0 0) :
    dS_dP = -dV_dT :=
  gibbs_maxwell hMixed

end MaxwellRelations

section FundamentalLaws

/-- DeVoe (2020), Eq. (4.4.3), the discrete-reservoir form of the Clausius
cyclic inequality. -/
theorem eq_4_4_3_clausius_inequality
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hCycle : D.entropyChange = 0) :
    entropyTransfer D ≤ 0 :=
  clausiusInequality_of_cycle D hCycle

/-- Weak form of DeVoe (2020), Eq. (4.5.4), using the finite-reservoir
entropy-transfer sum in `SecondLawData`. This form also allows reversible
processes.
-/
theorem eq_4_5_4_entropy_inequality_weak
    {ι : Type*} [Fintype ι] (D : SecondLawData ι) :
    entropyTransfer D ≤ D.entropyChange :=
  entropyChange_ge_entropyTransfer D

/-- DeVoe (2020), Eq. (4.5.4), for an irreversible process represented by
strictly positive internal entropy generation in `SecondLawData`. -/
theorem eq_4_5_4_entropy_inequality_irreversible
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hIrreversible : Irreversible D) :
    entropyTransfer D < D.entropyChange :=
  entropyChange_gt_entropyTransfer_of_irreversible D hIrreversible

/-- DeVoe (2020), Eq. (6.0.1), abstract Nernst-form predicate.

DeVoe states the zero-temperature entropy-difference limit for pure,
perfectly ordered crystals. The scope of `admissible` remains an explicit
formal input and must be restricted accordingly when interpreting this as
that physical statement.
-/
theorem eq_6_0_1_nernst_heat_theorem
    {State : Type*} (entropy : ℝ → State → ℝ)
    (admissible : State → Prop)
    (hNernst : NernstHeatTheorem entropy admissible) :
    NernstHeatTheorem entropy admissible :=
  hNernst

end FundamentalLaws

end ClassicalThermodynamics.Applications.DeVoe2020
