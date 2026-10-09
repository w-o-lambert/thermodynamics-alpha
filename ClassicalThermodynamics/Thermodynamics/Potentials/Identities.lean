import ClassicalThermodynamics.Thermodynamics.Potentials.Enthalpy
import ClassicalThermodynamics.Thermodynamics.Potentials.Gibbs
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Thermodynamics.Potentials

theorem gibbsFromHelmholtz_eq_internal
    (U temperature entropy pressure volume : ℝ) :
    gibbsFromHelmholtz (helmholtzFromInternal U temperature entropy) pressure volume =
      U + pressure * volume - temperature * entropy := by
  unfold gibbsFromHelmholtz helmholtzFromInternal
  ring

theorem enthalpy_eq_helmholtz_add_ts
    (U temperature entropy pressure volume : ℝ) :
    enthalpyFromInternal U pressure volume =
      helmholtzFromInternal U temperature entropy + temperature * entropy +
        pressure * volume := by
  unfold enthalpyFromInternal helmholtzFromInternal
  ring

end ClassicalThermodynamics.Thermodynamics.Potentials
