import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D

/-!
# Positive smooth dualizer for the throat-metric pairing

This gate closes the measure-theoretic globalization step for the Lorentzian
throat pairing.  A smooth positive dualizer turns one tensor pair into a
single separating test.  Continuity, compactness and the canonical
full-support throat measure then promote vanishing of the integrated pairing
to pointwise vanishing.

The concrete finite-frame smooth dualizer is supplied by the downstream
frame-covector gate; this file isolates the globalization interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricPositiveDualizer4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev ThroatPair :=
  SmoothThroatGeneralMetricTensorPair period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact smooth-geometric input needed after the pointwise Lorentz algebra:
one canonical test whose pairing density is continuous, nonnegative and
pointwise separating. -/
structure ThroatMetricSmoothPositiveDualizerData where
  dualize : ThroatPair period hPeriod → ThroatPair period hPeriod
  pairingContinuous :
    ∀ antifield,
      Continuous
        (fun point : EffectiveThroat period hPeriod =>
          intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (dualize antifield) point)
  pairingNonnegative :
    ∀ antifield point,
      0 ≤ intrinsicThroatTensorPairPairingAt period hPeriod
        antifield (dualize antifield) point
  pointwiseSeparates :
    ∀ antifield,
      (∀ point,
        intrinsicThroatTensorPairPairingAt period hPeriod
          antifield (dualize antifield) point = 0) →
      antifield = 0

/-- The positive dualizer and the existing canonical full-support measure
close bilinear separation of the integrated throat pairing. -/
theorem canonicalIntrinsicThroatTensorPairPairing_separates_of_positiveDualizer
    (data : ThroatMetricSmoothPositiveDualizerData period hPeriod) :
    ∀ antifield : ThroatPair period hPeriod,
      (∀ field,
        canonicalIntrinsicThroatTensorPairPairing
          period hPeriod antifield field = 0) →
      antifield = 0 := by
  intro antifield hZero
  let μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  letI : IsFiniteMeasure μ :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure μ :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  have hIntegral := hZero (data.dualize antifield)
  change (∫ point,
    intrinsicThroatTensorPairPairingAt period hPeriod
      antifield (data.dualize antifield) point ∂μ) = 0 at hIntegral
  have hIntegrable :
      Integrable
        (fun point : EffectiveThroat period hPeriod =>
          intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (data.dualize antifield) point) μ :=
    (data.pairingContinuous antifield).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAE :
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatTensorPairPairingAt period hPeriod
          antifield (data.dualize antifield) point) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (data.pairingNonnegative antifield) hIntegrable).mp hIntegral
  have hEverywhere :
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatTensorPairPairingAt period hPeriod
          antifield (data.dualize antifield) point) =
        (fun _ => 0) :=
    (Continuous.ae_eq_iff_eq μ
      (data.pairingContinuous antifield) continuous_const).mp hAE
  exact data.pointwiseSeparates antifield
    (fun point => congrFun hEverywhere point)

/-- A positive smooth dualizer makes the geometric realization in the
algebraic BRST dual faithful. -/
theorem throatMetricGeometricAntifieldToAlgebraicDual_injective_of_positiveDualizer
    (data : ThroatMetricSmoothPositiveDualizerData period hPeriod) :
    Function.Injective
      (throatMetricGeometricAntifieldToAlgebraicDual period hPeriod) :=
  (throatMetricGeometricAntifieldToAlgebraicDual_injective_iff
    period hPeriod).2
    (canonicalIntrinsicThroatTensorPairPairing_separates_of_positiveDualizer
      period hPeriod data)

/-- The dualizer closes nondegeneracy; integrated skew-adjointness is then the
only remaining input for the faithful coadjoint bridge. -/
def throatMetricGeometricCoadjointBridgeData_of_positiveDualizer_skew
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (ThroatPair period hPeriod))
    (data : ThroatMetricSmoothPositiveDualizerData period hPeriod)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  throatMetricGeometricCoadjointBridgeData_of_separation_skew
    period hPeriod representation
    (canonicalIntrinsicThroatTensorPairPairing_separates_of_positiveDualizer
      period hPeriod data)
    hSkew

end
end P0EFTJanusProgramPThroatMetricPositiveDualizer4D
end JanusFormal
