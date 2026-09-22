import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! Exact signed realization on the completed paired Abelian off-shell graph. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12SignedBRSTGram4D

local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

/-- Explicit signed squares of the actual Lorenz, B, antighost and FP maps. -/
def pairedAbelianSignedRiesz
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  abelianSignedGram
    (globalPairedAbelianOffShellLorenzProjection period hPeriod metric)
    (globalPairedAbelianOffShellBProjection period hPeriod metric)
    (globalPairedAbelianOffShellAntighostProjection period hPeriod metric)
    (globalPairedAbelianOffShellFPProjection period hPeriod metric)

/-- Equality holds on the whole completed graph, not just on smooth fields. -/
theorem pairedAbelianSignedRiesz_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    inner Real (pairedAbelianSignedRiesz period hPeriod metric first) second =
      globalPairedAbelianOffShellHessian period hPeriod metric first second := by
  rw [pairedAbelianSignedRiesz, abelianSignedGram_pairing]
  rfl

/-- The signed construction is the actual BRST Riesz operator. -/
theorem pairedAbelianSignedRiesz_eq_actual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    pairedAbelianSignedRiesz period hPeriod metric =
      globalPairedAbelianOffShellRieszOperator period hPeriod metric := by
  apply ContinuousLinearMap.ext
  intro first
  apply ext_inner_right Real
  intro second
  rw [pairedAbelianSignedRiesz_pairing,
    globalPairedAbelianOffShellRieszOperator_pairing]

/-- The original integrated BRST action is retained on the smooth core. -/
theorem pairedAbelianSignedRiesz_smooth_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    inner Real
      (pairedAbelianSignedRiesz period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric first))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric second) =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric first second (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [pairedAbelianSignedRiesz_pairing,
    globalPairedAbelianOffShellHessian_smooth_eq_BRST]

end
end P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D
end JanusFormal
