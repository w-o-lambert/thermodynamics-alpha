import ClassicalThermodynamics.Thermodynamics.Relations.Clapeyron
import ClassicalThermodynamics.Thermodynamics.Relations.GibbsHelmholtz
import ClassicalThermodynamics.Thermodynamics.Relations.JouleThomson
import ClassicalThermodynamics.Thermodynamics.Relations.Kirchhoff
import ClassicalThermodynamics.Thermodynamics.Relations.VanTHoff

/-!
# DeVoe (2020): classical thermodynamic relations

The wrappers below preserve the certificate/predicate form of the underlying
relations. In particular, they do not claim to derive the path differentials
for Clapeyron or Joule--Thomson from a concrete state-function model.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

open ClassicalThermodynamics.Thermodynamics.Relations

/-- DeVoe (2020), Eq. (8.4.4), the Clapeyron equation. -/
theorem eq_8_4_4_clapeyron
    (P deltaS deltaV : ℝ → ℝ) (T : ℝ)
    (h : ClapeyronAt P deltaS deltaV T) :
    deltaV T ≠ 0 ∧ HasDerivAt P (deltaS T / deltaV T) T :=
  h

/-- DeVoe (2020), Eq. (8.4.5), the enthalpy form of the Clapeyron equation.

The repository predicate is named `ClausiusClapeyronAt`; DeVoe uses this
equation as an alternative Clapeyron form and reserves the Clausius--Clapeyron
name for an approximation.
-/
theorem eq_8_4_5_enthalpy_clapeyron
    (P latentHeat deltaV : ℝ → ℝ) (T : ℝ)
    (h : ClausiusClapeyronAt P latentHeat deltaV T) :
    T ≠ 0 ∧ deltaV T ≠ 0 ∧
      HasDerivAt P (latentHeat T / (T * deltaV T)) T :=
  h

/-- DeVoe (2020), Eq. (7.5.10), the Joule--Thomson coefficient. -/
theorem eq_7_5_10_joule_thomson
    (T V dVdT_atP Cp : ℝ) :
    jouleThomsonCoefficient T V dVdT_atP Cp =
      (T * dVdT_atP - V) / Cp :=
  rfl

/-- Differential form associated with DeVoe (2020), Eq. (11.3.9),
Kirchhoff's equation. DeVoe gives the integrated finite-temperature form. -/
theorem eq_11_3_9_kirchhoff_differential
    (deltaH deltaCp : ℝ → ℝ) (T : ℝ)
    (h : KirchhoffAt deltaH deltaCp T) :
    HasDerivAt deltaH (deltaCp T) T :=
  h

/-- DeVoe (2020), Eq. (12.1.4), the Gibbs--Helmholtz equation. -/
theorem eq_12_1_4_gibbs_helmholtz
    (G H : ℝ → ℝ) (T : ℝ)
    (h : GibbsHelmholtzAt G H T) :
    T ≠ 0 ∧ HasDerivAt (fun t => G t / t) (-H T / T^2) T :=
  h

/-- DeVoe (2020), Eq. (12.1.13), the van 't Hoff differential equation. -/
theorem eq_12_1_13_van_t_hoff
    (K deltaH : ℝ → ℝ) (R T : ℝ)
    (h : VanTHoffAt K deltaH R T) :
    K T ≠ 0 ∧ R ≠ 0 ∧ T ≠ 0 ∧
      HasDerivAt (fun t => Real.log (K t))
        (deltaH T / (R * T^2)) T :=
  h

end ClassicalThermodynamics.Applications.DeVoe2020
