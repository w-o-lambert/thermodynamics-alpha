import ClassicalThermodynamics.Models.RedlichKwong.Mixture.Model
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

open scoped BigOperators

namespace ClassicalThermodynamics.Models.RedlichKwong.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def attractionQuotient (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  pairAttraction M rho / occupiedFraction M rho

noncomputable def attractionQuotientDerivative (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  (occupiedFraction M rho / (1 + occupiedFraction M rho) -
      Real.log (1 + occupiedFraction M rho)) /
    occupiedFraction M rho ^ 2

/-- Fixed-temperature Helmholtz free-energy density of the RK mixture. -/
noncomputable def helmholtzDensity (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  M.gasConstant * M.temperature *
      ((∑ i, rho i * (Real.log (rho i) - 1)) -
        totalDensity rho * Real.log (freeVolumeFraction M rho)) -
    attractionScale M * attractionQuotient M rho *
      Real.log (1 + occupiedFraction M rho)

/-- Component chemical potential compatible with `helmholtzDensity`. -/
noncomputable def chemicalPotential (M : Model (ι := ι))
    (rho : State (ι := ι)) (i : ι) : ℝ :=
  M.gasConstant * M.temperature *
      (Real.log (rho i) - Real.log (freeVolumeFraction M rho) +
        M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho) -
    attractionScale M *
      ((2 * ∑ j, M.attraction i j * rho j) *
          (Real.log (1 + occupiedFraction M rho) /
            occupiedFraction M rho) +
        pairAttraction M rho *
          attractionQuotientDerivative M rho * M.excludedVolume i)

/-- Redlich--Kwong pressure in component-density coordinates. -/
noncomputable def densityPressure (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  M.gasConstant * M.temperature * totalDensity rho /
      freeVolumeFraction M rho -
    attractionScale M * pairAttraction M rho /
      (1 + occupiedFraction M rho)

lemma freeVolume_pos (M : Model (ι := ι)) (rho : State (ι := ι))
    (hphysical : Physical M rho) :
    0 < freeVolumeFraction M rho := by
  unfold freeVolumeFraction
  linarith [hphysical.2.2]

lemma occupiedFraction_pos [Nonempty ι] (M : Model (ι := ι)) (rho : State (ι := ι))
    (hphysical : Physical M rho) :
    0 < occupiedFraction M rho := by
  unfold occupiedFraction
  exact Finset.sum_pos' (fun i hi => le_of_lt (mul_pos (hphysical.1.2.2 i) (hphysical.2.1 i)))
    ⟨Classical.choice inferInstance, Finset.mem_univ _,
      mul_pos (hphysical.1.2.2 (Classical.choice inferInstance))
        (hphysical.2.1 (Classical.choice inferInstance))⟩

lemma attractionDenominator_pos [Nonempty ι] (M : Model (ι := ι)) (rho : State (ι := ι))
    (hphysical : Physical M rho) :
    0 < 1 + occupiedFraction M rho := by
  linarith [occupiedFraction_pos M rho hphysical]

def Coexist (M : Model (ι := ι)) (rhoA rhoB : State (ι := ι)) : Prop :=
  densityPressure M rhoA = densityPressure M rhoB ∧
  ∀ i, chemicalPotential M rhoA i = chemicalPotential M rhoB i

end ClassicalThermodynamics.Models.RedlichKwong.Mixture
