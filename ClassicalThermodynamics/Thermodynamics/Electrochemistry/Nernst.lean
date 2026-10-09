import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace ClassicalThermodynamics.Thermodynamics.Electrochemistry
noncomputable def nernstPotential (standardPotential R T n F reactionQuotient : ℝ) : ℝ :=
  standardPotential - (R*T)/(n*F) * Real.log reactionQuotient
end ClassicalThermodynamics.Thermodynamics.Electrochemistry
