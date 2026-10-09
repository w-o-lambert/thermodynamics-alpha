import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
import ClassicalThermodynamics.Thermodynamics.Derivatives.Provenance

namespace ClassicalThermodynamics.Thermodynamics.Extensivity

open ClassicalThermodynamics.Thermodynamics.Derivatives

noncomputable def extensiveChemicalPotential {ι : Type*} [DecidableEq ι]
    (mu : (ι → ℝ) → ι → ℝ) (volume : ℝ) (amount : ι → ℝ) (i : ι) : ℝ :=
  mu (densityState volume amount) i

def ExtensiveChemicalPotentialHasCoordinateDerivative {ι : Type*} [DecidableEq ι]
    (mu : (ι → ℝ) → ι → ℝ) (H : (ι → ℝ) → ι → ι → ℝ)
    (volume : ℝ) (amount : ι → ℝ) : Prop :=
  ∀ i j, HasDerivAt
    (fun t => extensiveChemicalPotential mu volume
      (coordinatePerturb amount j t) i)
    (H (densityState volume amount) i j / volume) 0

theorem extensiveChemicalPotential_hasCoordinateDerivative_hessian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : (ι → ℝ) → ι → ℝ)
    (H : (ι → ℝ) → ι → ι → ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0)
    (amount : ι → ℝ)
    (hH : HessianDerived mu H (densityState volume amount)) :
    ExtensiveChemicalPotentialHasCoordinateDerivative mu H volume amount := by
  intro i j
  have hcoordinate := hH i j
  have hscale : HasDerivAt (fun t : ℝ => t / volume) (1 / volume) 0 := by
    convert (hasDerivAt_id (x := (0 : ℝ))).div_const volume using 1 <;>
      simp [hvolume]
  have hcoordinate0 :
      HasDerivAt (fun t => mu (coordinatePerturb (densityState volume amount) j t) i)
        (H (densityState volume amount) i j) (0 / volume) := by
    simpa using hcoordinate
  have hcomposed := hcoordinate0.comp 0 hscale
  convert hcomposed using 1
  · funext t
    simp only [Function.comp_apply, extensiveChemicalPotential]
    congr 1
    funext k
    by_cases h : k = j
    · subst k
      simp [densityState, coordinatePerturb,
        ClassicalThermodynamics.Math.Functions.coordinatePerturb]
      field_simp [hvolume]
    · simp [densityState, coordinatePerturb,
        ClassicalThermodynamics.Math.Functions.coordinatePerturb, h]
  · ring

end ClassicalThermodynamics.Thermodynamics.Extensivity
