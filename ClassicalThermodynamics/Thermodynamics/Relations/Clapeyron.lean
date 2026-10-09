import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Thermodynamics.Relations

/-- Clapeyron slope certificate dP/dT = ΔS/ΔV. -/
def ClapeyronAt (P deltaS deltaV : ℝ → ℝ) (T : ℝ) : Prop :=
  deltaV T ≠ 0 ∧ HasDerivAt P (deltaS T / deltaV T) T

/-- Clausius-Clapeyron specialization dP/dT = L/(T ΔV). -/
def ClausiusClapeyronAt (P latentHeat deltaV : ℝ → ℝ) (T : ℝ) : Prop :=
  T ≠ 0 ∧ deltaV T ≠ 0 ∧ HasDerivAt P (latentHeat T / (T * deltaV T)) T

/-- Gibbs differential along a coexistence curve parameterised by temperature:
`dG/dT = -S + V dP/dT`. -/
def GibbsPathDifferential (g entropy volume pressureSlope : ℝ → ℝ) (T : ℝ) : Prop :=
  HasDerivAt g (-entropy T + volume T * pressureSlope T) T

/-- Equality of the phase Gibbs potentials forces the coexistence-curve slope
to be ΔS/ΔV, provided the Gibbs path differentials hold. -/
theorem clapeyron_of_equal_gibbs
    (P entropyAlpha entropyBeta volumeAlpha volumeBeta gibbsAlpha gibbsBeta
      pressureSlope : ℝ → ℝ) (T : ℝ)
    (hCoexist : ∀ t, gibbsAlpha t = gibbsBeta t)
    (hAlpha : GibbsPathDifferential gibbsAlpha entropyAlpha volumeAlpha
      pressureSlope T)
    (hBeta : GibbsPathDifferential gibbsBeta entropyBeta volumeBeta
      pressureSlope T)
    (hPressure : HasDerivAt P (pressureSlope T) T)
    (hVolume : volumeAlpha T - volumeBeta T ≠ 0) :
    ClapeyronAt P (fun t => entropyAlpha t - entropyBeta t)
      (fun t => volumeAlpha t - volumeBeta t) T := by
  change volumeAlpha T - volumeBeta T ≠ 0 ∧
    HasDerivAt P
      ((entropyAlpha T - entropyBeta T) /
        (volumeAlpha T - volumeBeta T)) T
  have hGibbs : gibbsAlpha = gibbsBeta := funext hCoexist
  have hAlpha' :
      HasDerivAt gibbsAlpha
        (-entropyAlpha T + volumeAlpha T * pressureSlope T) T := hAlpha
  have hBeta' :
      HasDerivAt gibbsBeta
        (-entropyBeta T + volumeBeta T * pressureSlope T) T := hBeta
  rw [hGibbs] at hAlpha'
  have hDerivative :
      -entropyAlpha T + volumeAlpha T * pressureSlope T =
        -entropyBeta T + volumeBeta T * pressureSlope T :=
    hAlpha'.unique hBeta'
  have hSlope :
      pressureSlope T =
        (entropyAlpha T - entropyBeta T) /
          (volumeAlpha T - volumeBeta T) := by
    apply (eq_div_iff hVolume).2
    nlinarith
  rw [hSlope] at hPressure
  exact ⟨hVolume, hPressure⟩

/-- Latent heat `L = T ΔS` specializes the Clapeyron equation to
Clausius-Clapeyron. -/
theorem clausiusClapeyron_of_equal_gibbs
    (P entropyAlpha entropyBeta volumeAlpha volumeBeta gibbsAlpha gibbsBeta
      pressureSlope latentHeat : ℝ → ℝ) (T : ℝ)
    (hCoexist : ∀ t, gibbsAlpha t = gibbsBeta t)
    (hAlpha : GibbsPathDifferential gibbsAlpha entropyAlpha volumeAlpha
      pressureSlope T)
    (hBeta : GibbsPathDifferential gibbsBeta entropyBeta volumeBeta
      pressureSlope T)
    (hPressure : HasDerivAt P (pressureSlope T) T)
    (hTemperature : T ≠ 0)
    (hVolume : volumeAlpha T - volumeBeta T ≠ 0)
    (hLatentHeat : latentHeat T =
      T * (entropyAlpha T - entropyBeta T)) :
    ClausiusClapeyronAt P latentHeat
      (fun t => volumeAlpha t - volumeBeta t) T := by
  have hClapeyron := clapeyron_of_equal_gibbs P entropyAlpha entropyBeta
    volumeAlpha volumeBeta gibbsAlpha gibbsBeta pressureSlope T
    hCoexist hAlpha hBeta hPressure hVolume
  change T ≠ 0 ∧ volumeAlpha T - volumeBeta T ≠ 0 ∧
    HasDerivAt P
      (latentHeat T / (T * (volumeAlpha T - volumeBeta T))) T
  have hSlope :
      (entropyAlpha T - entropyBeta T) /
          (volumeAlpha T - volumeBeta T) =
        latentHeat T / (T * (volumeAlpha T - volumeBeta T)) := by
    rw [hLatentHeat]
    field_simp [hTemperature, hVolume]
  change volumeAlpha T - volumeBeta T ≠ 0 ∧
    HasDerivAt P
      ((entropyAlpha T - entropyBeta T) /
        (volumeAlpha T - volumeBeta T)) T at hClapeyron
  rcases hClapeyron with ⟨hVolume', hPressure'⟩
  rw [hSlope] at hPressure'
  exact ⟨hTemperature, hVolume', hPressure'⟩

end ClassicalThermodynamics.Thermodynamics.Relations
