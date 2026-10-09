import ClassicalThermodynamics.Thermodynamics.Extensivity.Euler
import ClassicalThermodynamics.Thermodynamics.Extensivity.GibbsDuhem

/-!
# DeVoe (2020): extensivity relations

Section-level wrappers for the thermodynamic Euler relation and the
Gibbs-Duhem relation in Section 5.5. These preserve the formal hypotheses:
one-homogeneity and a conjugate-variable differential for Euler, and the
Euler differential plus first law for Gibbs-Duhem.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

open scoped BigOperators
open ClassicalThermodynamics.Thermodynamics.Extensivity

/-- DeVoe (2020), Section 5.5: the thermodynamic Euler relation follows from
one-homogeneity and the conjugate-variable representation of the differential.

The formalization requires the Fréchet derivative and conjugate-variable
identity explicitly; it does not establish that a physical system is
extensive. -/
theorem section5_5_thermodynamicEulerRelation
    {ι : Type*} [Fintype ι]
    (Ufun : (ℝ × ℝ × (ι → ℝ)) → ℝ)
    (S V : ℝ) (N : ι → ℝ) (T P : ℝ) (mu : ι → ℝ)
    (U' : (ℝ × ℝ × (ι → ℝ)) →L[ℝ] ℝ)
    (hhom : OneHomogeneous Ufun)
    (hDiff : HasFDerivAt Ufun U' (S, V, N))
    (hConjugates :
      U' (S, V, N) = T * S - P * V + ∑ i, mu i * N i) :
    EulerRelation (Ufun (S, V, N)) T S P V mu N :=
  thermodynamicEuler_of_oneHomogeneous
    Ufun S V N T P mu U' hhom hDiff hConjugates

/-- DeVoe (2020), Section 5.5: Gibbs-Duhem relation from the differential
Euler relation and the open-system first law.

The premises make explicit the differential identities assumed by the
formalization rather than deriving them from state functions. -/
theorem section5_5_gibbsDuhem
    {ι : Type*} [Fintype ι]
    (T S P V dT dS dP dV dU : ℝ)
    (mu N dmu dN : ι → ℝ)
    (hEulerDiff :
      dU = T * dS + S * dT - P * dV - V * dP +
        ∑ i, (mu i * dN i + N i * dmu i))
    (hFirstLaw :
      dU = T * dS - P * dV + ∑ i, mu i * dN i) :
    GibbsDuhem S dT V dP N dmu :=
  gibbsDuhem_of_eulerDifferential_and_firstLaw
    T S P V dT dS dP dV dU mu N dmu dN hEulerDiff hFirstLaw

/-- Constant-temperature, constant-pressure specialization of the
Gibbs-Duhem relation in DeVoe (2020), Section 5.5. -/
theorem section5_5_gibbsDuhem_constantTP
    {ι : Type*} [Fintype ι]
    {S V : ℝ} {N dmu : ι → ℝ}
    (h : GibbsDuhem S 0 V 0 N dmu) :
    ∑ i, N i * dmu i = 0 :=
  gibbsDuhem_isothermal_isobaric h

end ClassicalThermodynamics.Applications.DeVoe2020
