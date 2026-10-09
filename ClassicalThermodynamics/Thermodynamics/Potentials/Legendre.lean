import ClassicalThermodynamics.Math.LegendreTransform
import ClassicalThermodynamics.Thermodynamics.Potentials.Identities
namespace ClassicalThermodynamics.Thermodynamics.Potentials

theorem helmholtz_is_entropy_legendre_value (U temperature entropy : ℝ) :
    helmholtzFromInternal U temperature entropy =
      ClassicalThermodynamics.Math.legendreValue U entropy temperature := by
  rfl

theorem gibbs_is_inverse_volume_legendre_value (F pressure volume : ℝ) :
    gibbsFromHelmholtz F pressure volume =
      ClassicalThermodynamics.Math.inverseLegendreValue F volume pressure := by
  rfl

end ClassicalThermodynamics.Thermodynamics.Potentials
