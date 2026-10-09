import ClassicalThermodynamics.Models.VanDerWaals.Mixture.LogarithmicCoexistenceCoordinates
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Unit-component embedding of the scalar pure-fluid logarithmic coordinate. -/
noncomputable def pureLeknerMidpoint (d : ℝ) : State (ι := Unit) :=
  fun _ => vdwGeometricMidpoint d

noncomputable def pureLeknerDifference (d : ℝ) : State (ι := Unit) :=
  fun _ => d

/-- The N-component logarithmic high reconstruction reduces exactly to the pure
Lekner/high branch in a one-component state space. -/
theorem logarithmicHigh_pureLekner (d : ℝ) :
    logarithmicHigh (pureLeknerMidpoint d) (pureLeknerDifference d) () =
      vdwLiquidFreeVolume d := by
  rfl

/-- The low reconstruction likewise reduces to the pure Lekner/low branch. -/
theorem logarithmicLow_pureLekner (d : ℝ) :
    logarithmicLow (pureLeknerMidpoint d) (pureLeknerDifference d) () =
      vdwGasFreeVolume d := by
  rfl

/-- The scalar pure-fluid parameter is the unique component of the general
logarithmic-difference vector. -/
theorem pureLeknerDifference_apply (d : ℝ) : pureLeknerDifference d () = d := rfl

/-- The pure branch ratio theorem is a specialization of the general logarithmic
coordinate ratio theorem. -/
theorem pureLekner_ratio_from_mixture_coordinates
    {d : ℝ} (hm : vdwGeometricMidpoint d ≠ 0) :
    vdwLiquidFreeVolume d / vdwGasFreeVolume d = Real.exp d := by
  simpa [pureLeknerMidpoint, pureLeknerDifference] using
    logarithmicHigh_div_logarithmicLow
      (pureLeknerMidpoint d) (pureLeknerDifference d) () hm

/-- A nonfractionating fixed-composition density pair has the same logarithmic
separation in every component with positive composition. -/
theorem logarithmicDifference_fixedComposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {rhoA rhoB : ℝ}
    (hA : 0 < rhoA) (hB : 0 < rhoB)
    (hx : ∀ i, 0 < x i) :
    logarithmicDifference (stateAtComposition x rhoA)
      (stateAtComposition x rhoB) = fun _ => Real.log (rhoA / rhoB) := by
  funext i
  unfold logarithmicDifference stateAtComposition
  have hxi : x i ≠ 0 := ne_of_gt (hx i)
  congr 1
  field_simp [hxi]

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
