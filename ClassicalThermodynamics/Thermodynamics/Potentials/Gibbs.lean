import ClassicalThermodynamics.Thermodynamics.Potentials.Helmholtz
namespace ClassicalThermodynamics.Thermodynamics.Potentials
noncomputable def gibbsFromHelmholtz (F pressure volume : ℝ) : ℝ :=
  F + pressure * volume
end ClassicalThermodynamics.Thermodynamics.Potentials
