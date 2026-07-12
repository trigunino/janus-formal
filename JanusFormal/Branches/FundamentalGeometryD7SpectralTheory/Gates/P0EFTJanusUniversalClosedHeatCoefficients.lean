import Mathlib

namespace JanusFormal
namespace P0EFTJanusUniversalClosedHeatCoefficients

set_option autoImplicit false

/--
Integrated data for a Laplace-type operator written in the convention

`P = -(g^{mu nu} nabla_mu nabla_nu + E)`

on a compact manifold without boundary. Total derivative terms are absent
after integration. All traces over the vector bundle are already included.
The common factor `(4*pi)^(-dimension/2)` is intentionally omitted.
-/
structure ClosedLaplaceHeatData where
  bundleRank : ℝ
  volume : ℝ
  integratedScalarCurvature : ℝ
  integratedScalarCurvatureSquared : ℝ
  integratedRicciSquared : ℝ
  integratedRiemannSquared : ℝ
  integratedTraceE : ℝ
  integratedTraceScalarCurvatureE : ℝ
  integratedTraceESquared : ℝ
  integratedTraceConnectionCurvatureSquared : ℝ

/-- Reduced integrated coefficient `a0`, without `(4*pi)^(-d/2)`. -/
def reducedA0 (s : ClosedLaplaceHeatData) : ℝ :=
  s.bundleRank * s.volume

/-- Reduced integrated coefficient `a2`, without `(4*pi)^(-d/2)`. -/
noncomputable def reducedA2 (s : ClosedLaplaceHeatData) : ℝ :=
  s.integratedTraceE +
    s.bundleRank * s.integratedScalarCurvature / 6

/--
Reduced integrated coefficient `a4`, without `(4*pi)^(-d/2)` and with the
integrated total derivatives removed.
-/
noncomputable def reducedA4 (s : ClosedLaplaceHeatData) : ℝ :=
  (
    s.bundleRank *
      (5 * s.integratedScalarCurvatureSquared -
        2 * s.integratedRicciSquared +
        2 * s.integratedRiemannSquared) +
    60 * s.integratedTraceScalarCurvatureE +
    180 * s.integratedTraceESquared +
    30 * s.integratedTraceConnectionCurvatureSquared
  ) / 360

/-- Direct-sum/additive combination of two operator sectors. -/
def addHeatData
    (first second : ClosedLaplaceHeatData) : ClosedLaplaceHeatData :=
  { bundleRank := first.bundleRank + second.bundleRank
    volume := first.volume
    integratedScalarCurvature := first.integratedScalarCurvature
    integratedScalarCurvatureSquared := first.integratedScalarCurvatureSquared
    integratedRicciSquared := first.integratedRicciSquared
    integratedRiemannSquared := first.integratedRiemannSquared
    integratedTraceE := first.integratedTraceE + second.integratedTraceE
    integratedTraceScalarCurvatureE :=
      first.integratedTraceScalarCurvatureE +
        second.integratedTraceScalarCurvatureE
    integratedTraceESquared :=
      first.integratedTraceESquared + second.integratedTraceESquared
    integratedTraceConnectionCurvatureSquared :=
      first.integratedTraceConnectionCurvatureSquared +
        second.integratedTraceConnectionCurvatureSquared }

/-- `a0` is additive for sectors living on the same geometry. -/
theorem reduced_a0_additive
    (first second : ClosedLaplaceHeatData)
    (hVolume : second.volume = first.volume) :
    reducedA0 (addHeatData first second) =
      reducedA0 first + reducedA0 second := by
  unfold reducedA0 addHeatData
  rw [hVolume]
  ring

/-- `a2` is additive when both sectors use the same geometric scalar integral. -/
theorem reduced_a2_additive
    (first second : ClosedLaplaceHeatData)
    (hScalar :
      second.integratedScalarCurvature =
        first.integratedScalarCurvature) :
    reducedA2 (addHeatData first second) =
      reducedA2 first + reducedA2 second := by
  unfold reducedA2 addHeatData
  rw [hScalar]
  ring

/-- `a4` is additive when the two sectors live on the same background geometry. -/
theorem reduced_a4_additive
    (first second : ClosedLaplaceHeatData)
    (hScalarSquared :
      second.integratedScalarCurvatureSquared =
        first.integratedScalarCurvatureSquared)
    (hRicciSquared :
      second.integratedRicciSquared = first.integratedRicciSquared)
    (hRiemannSquared :
      second.integratedRiemannSquared = first.integratedRiemannSquared) :
    reducedA4 (addHeatData first second) =
      reducedA4 first + reducedA4 second := by
  unfold reducedA4 addHeatData
  rw [hScalarSquared, hRicciSquared, hRiemannSquared]
  ring

/--
Convention-specific integrated trace reduction for a complex rank-two Dirac
operator coupled to one unit-charge Abelian connection:

* `tr E = -R/2`;
* `tr (R E) = -R^2/2`;
* `tr E^2 = R^2/8 + F^2`;
* `tr Omega^2 = -Riem^2/4 - 2 F^2`.

These are the precise assumptions behind the Dirac candidate used in Program D.
-/
structure RankTwoDiracTraceData where
  volume : ℝ
  integratedScalarCurvature : ℝ
  integratedScalarCurvatureSquared : ℝ
  integratedRicciSquared : ℝ
  integratedRiemannSquared : ℝ
  integratedGaugeFieldSquared : ℝ

/-- Convert the rank-two Dirac trace convention to universal Laplace data. -/
noncomputable def rankTwoDiracAsLaplaceData
    (s : RankTwoDiracTraceData) : ClosedLaplaceHeatData :=
  { bundleRank := 2
    volume := s.volume
    integratedScalarCurvature := s.integratedScalarCurvature
    integratedScalarCurvatureSquared :=
      s.integratedScalarCurvatureSquared
    integratedRicciSquared := s.integratedRicciSquared
    integratedRiemannSquared := s.integratedRiemannSquared
    integratedTraceE := -s.integratedScalarCurvature / 2
    integratedTraceScalarCurvatureE :=
      -s.integratedScalarCurvatureSquared / 2
    integratedTraceESquared :=
      s.integratedScalarCurvatureSquared / 8 +
        s.integratedGaugeFieldSquared
    integratedTraceConnectionCurvatureSquared :=
      -s.integratedRiemannSquared / 4 -
        2 * s.integratedGaugeFieldSquared }

/-- Rank-two Dirac `a0`. -/
theorem rank_two_dirac_reduced_a0
    (s : RankTwoDiracTraceData) :
    reducedA0 (rankTwoDiracAsLaplaceData s) = 2 * s.volume := by
  rfl

/-- Rank-two Dirac `a2 = - integral R / 6`. -/
theorem rank_two_dirac_reduced_a2
    (s : RankTwoDiracTraceData) :
    reducedA2 (rankTwoDiracAsLaplaceData s) =
      -s.integratedScalarCurvature / 6 := by
  unfold reducedA2 rankTwoDiracAsLaplaceData
  ring

/--
Rank-two Dirac `a4`:

`(5 R^2 - 8 Ric^2 - 7 Riem^2)/720 + F^2/3`.
-/
theorem rank_two_dirac_reduced_a4
    (s : RankTwoDiracTraceData) :
    reducedA4 (rankTwoDiracAsLaplaceData s) =
      (5 * s.integratedScalarCurvatureSquared -
        8 * s.integratedRicciSquared -
        7 * s.integratedRiemannSquared) / 720 +
      s.integratedGaugeFieldSquared / 3 := by
  unfold reducedA4 rankTwoDiracAsLaplaceData
  ring

/--
The universal coefficients determine UV-local data only. Their promotion to a
physical one-loop action additionally requires the common heat prefactor,
statistics, zero-mode treatment, zeta/eta continuation and a renormalization
prescription.
-/
structure UniversalHeatKernelPhysicalStatus where
  laplaceTypeOperatorConstructed : Prop
  signConventionMatched : Prop
  bundleTraceIdentitiesProved : Prop
  totalDerivativeTermsControlled : Prop
  commonHeatPrefactorRestored : Prop
  statisticsAndMultiplicityIncluded : Prop
  zeroModesSeparated : Prop
  zetaContinuationDerived : Prop
  finiteRenormalizationConditionDerived : Prop


def universalHeatKernelPhysicalClosed
    (s : UniversalHeatKernelPhysicalStatus) : Prop :=
  s.laplaceTypeOperatorConstructed /\
  s.signConventionMatched /\
  s.bundleTraceIdentitiesProved /\
  s.totalDerivativeTermsControlled /\
  s.commonHeatPrefactorRestored /\
  s.statisticsAndMultiplicityIncluded /\
  s.zeroModesSeparated /\
  s.zetaContinuationDerived /\
  s.finiteRenormalizationConditionDerived

end P0EFTJanusUniversalClosedHeatCoefficients
end JanusFormal
