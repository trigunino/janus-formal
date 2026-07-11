import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusDiracSeeleyDeWittCandidate

namespace JanusFormal
namespace P0EFTJanusTruncatedSpectralActionNoGo

set_option autoImplicit false

open P0EFTJanusProductThroatLocalInvariants
open P0EFTJanusDiracSeeleyDeWittCandidate

/-- Cutoff moments multiplying the reduced `a0`, `a2` and `a4` coefficients. -/
structure TruncatedSpectralMoments where
  cutoff : ℝ
  volumeMoment : ℝ
  curvatureMoment : ℝ
  quadraticMoment : ℝ
  cutoffPositive : 0 < cutoff

/-- Local truncated spectral action through `a4`. -/
noncomputable def truncatedLocalSpectralAction
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData) : ℝ :=
  moments.volumeMoment * moments.cutoff ^ 3 * reducedDiracA0 geometry +
    moments.curvatureMoment * moments.cutoff * reducedDiracA2 geometry +
    moments.quadraticMoment * moments.cutoff⁻¹ * reducedDiracA4 geometry

/-- Coefficient of the circle modulus in the truncated local action. -/
noncomputable def truncatedLocalSlope
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData) : ℝ :=
  moments.volumeMoment * moments.cutoff ^ 3 *
      (8 * geometry.piConstant * geometry.geometricLength ^ 3) +
    moments.curvatureMoment * moments.cutoff *
      (-(4 * geometry.piConstant * geometry.geometricLength) / 3) +
    moments.quadraticMoment * moments.cutoff⁻¹ *
      (2 * geometry.piConstant *
        (5 * (geometry.monopoleNumber : ℝ) ^ 2 - 1) /
        (15 * geometry.geometricLength))

/-- The entire local spectral action factors as `T` times one slope. -/
theorem truncated_local_action_factors_circle_modulus
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData) :
    truncatedLocalSpectralAction moments geometry =
      geometry.circleModulus * truncatedLocalSlope moments geometry := by
  unfold truncatedLocalSpectralAction truncatedLocalSlope
  rw [reduced_dirac_a0_formula,
    reduced_dirac_a2_formula,
    reduced_dirac_a4_formula]
  ring

/-- Replace only the circle modulus in the product geometry. -/
def withCircleModulus
    (geometry : ProductThroatInvariantData)
    (circleModulus : ℝ) : ProductThroatInvariantData :=
  { geometricLength := geometry.geometricLength
    circleModulus := circleModulus
    piConstant := geometry.piConstant
    monopoleNumber := geometry.monopoleNumber
    geometricLengthPositive := geometry.geometricLengthPositive
    circleModulusPositive := by
      by_cases h : 0 < circleModulus
      · exact h
      · exact False.elim (by
          have := geometry.circleModulusPositive
          omega)
    piConstantPositive := geometry.piConstantPositive }

/-- Algebraic local action at an arbitrary modulus, avoiding positivity packaging. -/
noncomputable def localActionAtModulus
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (circleModulus : ℝ) : ℝ :=
  circleModulus * truncatedLocalSlope moments geometry

/-- Exact difference law. -/
theorem local_action_at_modulus_difference
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (firstModulus secondModulus : ℝ) :
    localActionAtModulus moments geometry secondModulus -
        localActionAtModulus moments geometry firstModulus =
      (secondModulus - firstModulus) *
        truncatedLocalSlope moments geometry := by
  unfold localActionAtModulus
  ring

/-- Positive slope means strict increase in `T`. -/
theorem positive_slope_strictly_increases
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (firstModulus secondModulus : ℝ)
    (hSlope : 0 < truncatedLocalSlope moments geometry)
    (hModuli : firstModulus < secondModulus) :
    localActionAtModulus moments geometry firstModulus <
      localActionAtModulus moments geometry secondModulus := by
  have hDifference := local_action_at_modulus_difference
    moments geometry firstModulus secondModulus
  have hPositive :
      0 < (secondModulus - firstModulus) *
        truncatedLocalSlope moments geometry :=
    mul_pos (sub_pos.mpr hModuli) hSlope
  linarith

/-- Negative slope means strict decrease in `T`. -/
theorem negative_slope_strictly_decreases
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (firstModulus secondModulus : ℝ)
    (hSlope : truncatedLocalSlope moments geometry < 0)
    (hModuli : firstModulus < secondModulus) :
    localActionAtModulus moments geometry secondModulus <
      localActionAtModulus moments geometry firstModulus := by
  have hDifference := local_action_at_modulus_difference
    moments geometry firstModulus secondModulus
  have hNegative :
      (secondModulus - firstModulus) *
        truncatedLocalSlope moments geometry < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hModuli) hSlope
  linarith

/-- Zero slope leaves an exactly flat circle direction. -/
theorem zero_slope_is_flat_direction
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (hSlope : truncatedLocalSlope moments geometry = 0) :
    ∀ firstModulus secondModulus : ℝ,
      localActionAtModulus moments geometry firstModulus =
        localActionAtModulus moments geometry secondModulus := by
  intro firstModulus secondModulus
  unfold localActionAtModulus
  rw [hSlope]
  ring

/-- Trichotomy: increasing, decreasing or flat; never a strict interior local minimum. -/
theorem local_spectral_action_trichotomy
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData) :
    0 < truncatedLocalSlope moments geometry \/
      truncatedLocalSlope moments geometry < 0 \/
      truncatedLocalSlope moments geometry = 0 := by
  rcases lt_trichotomy
      (truncatedLocalSlope moments geometry) 0 with hNeg | hZero | hPos
  · exact Or.inr (Or.inl hNeg)
  · exact Or.inr (Or.inr hZero)
  · exact Or.inl hPos

/-- No strict symmetric minimum exists for the local truncated spectral action. -/
theorem truncated_local_spectral_action_no_strict_minimum
    (moments : TruncatedSpectralMoments)
    (geometry : ProductThroatInvariantData)
    (center displacement : ℝ)
    (hDisplacement : 0 < displacement) :
    Not (
      localActionAtModulus moments geometry center <
        localActionAtModulus moments geometry (center - displacement) /\
      localActionAtModulus moments geometry center <
        localActionAtModulus moments geometry (center + displacement)) := by
  intro hStrict
  have hMidpoint :
      2 * localActionAtModulus moments geometry center =
        localActionAtModulus moments geometry (center - displacement) +
          localActionAtModulus moments geometry (center + displacement) := by
    unfold localActionAtModulus
    ring
  linarith

/--
The UV-local spectral action determines slopes and counterterms but cannot
select a finite circle modulus.  A stable modulus must involve nonlocal winding
terms or genuinely nonlinear interactions, and its finite local coefficients
must be fixed independently of the target radius.
-/
structure TruncatedSpectralActionClosureStatus where
  momentsDerivedFromCutoffFunction : Prop
  actualDiracCoefficientsVerified : Prop
  localSlopeComputed : Prop
  nonlocalWindingActionAdded : Prop
  finiteCountertermsFixed : Prop
  stableModulusDerived : Prop
  schemeIndependenceProved : Prop


def truncatedSpectralActionClosure
    (s : TruncatedSpectralActionClosureStatus) : Prop :=
  s.momentsDerivedFromCutoffFunction /\
  s.actualDiracCoefficientsVerified /\
  s.localSlopeComputed /\
  s.nonlocalWindingActionAdded /\
  s.finiteCountertermsFixed /\
  s.stableModulusDerived /\
  s.schemeIndependenceProved

end P0EFTJanusTruncatedSpectralActionNoGo
end JanusFormal
