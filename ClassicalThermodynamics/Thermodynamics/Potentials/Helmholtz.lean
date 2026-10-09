import ClassicalThermodynamics.Thermodynamics.Potentials.InternalEnergy
namespace ClassicalThermodynamics.Thermodynamics.Potentials
abbrev HelmholtzEnergy (Control State : Type*) := Control → State → ℝ
noncomputable def helmholtzFromInternal (U temperature entropy : ℝ) : ℝ :=
  U - temperature * entropy
end ClassicalThermodynamics.Thermodynamics.Potentials
