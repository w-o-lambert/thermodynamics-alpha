import ClassicalThermodynamics.Thermodynamics.Potentials.InternalEnergy
namespace ClassicalThermodynamics.Thermodynamics.Potentials
noncomputable def enthalpyFromInternal (U pressure volume : ℝ) : ℝ :=
  U + pressure * volume
end ClassicalThermodynamics.Thermodynamics.Potentials
