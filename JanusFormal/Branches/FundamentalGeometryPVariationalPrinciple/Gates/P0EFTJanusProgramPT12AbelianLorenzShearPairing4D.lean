import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

/-! Exact auxiliary square separation on the actual geometric Abelian graph. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianLorenzShearPairing4D
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


local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

@[simp] theorem abelianLorenzProjection_shear
    (vector : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellLorenzProjection period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric vector) =
      globalPairedAbelianOffShellLorenzProjection period hPeriod metric vector := by
  change globalPairedAbelianOffShellLorenzProjection period hPeriod metric vector + 0 = _
  exact add_zero _

@[simp] theorem abelianBProjection_shear
    (vector : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellBProjection period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric vector) =
      globalPairedAbelianOffShellBProjection period hPeriod metric vector +
        globalPairedAbelianOffShellLorenzProjection period hPeriod metric vector := rfl

@[simp] theorem abelianAntighostProjection_shear
    (vector : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellAntighostProjection period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric vector) =
      globalPairedAbelianOffShellAntighostProjection period hPeriod metric vector := by
  change globalPairedAbelianOffShellAntighostProjection period hPeriod metric vector + 0 = _
  exact add_zero _

@[simp] theorem abelianFPProjection_shear
    (vector : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellFPProjection period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric vector) =
      globalPairedAbelianOffShellFPProjection period hPeriod metric vector := by
  change globalPairedAbelianOffShellFPProjection period hPeriod metric vector + 0 = _
  exact add_zero _

/-- The shear removes the Lorenz--B cross terms on the whole completed graph.
The ghost pairing retains the actual geometric Faddeev--Popov map. -/
theorem abelianLorenzShear_hessian_pairing
    (first second : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellHessian period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric first)
        (abelianLorenzGraphShear period hPeriod metric second) =
      inner Real (globalPairedAbelianOffShellLorenzProjection period hPeriod metric first)
        (globalPairedAbelianOffShellLorenzProjection period hPeriod metric second) -
      inner Real (globalPairedAbelianOffShellBProjection period hPeriod metric first)
        (globalPairedAbelianOffShellBProjection period hPeriod metric second) +
      inner Real (globalPairedAbelianOffShellAntighostProjection period hPeriod metric first)
        (globalPairedAbelianOffShellFPProjection period hPeriod metric second) +
      inner Real (globalPairedAbelianOffShellFPProjection period hPeriod metric first)
        (globalPairedAbelianOffShellAntighostProjection period hPeriod metric second) := by
  simp only [globalPairedAbelianOffShellHessian_apply, abelianLorenzProjection_shear,
    abelianBProjection_shear, abelianAntighostProjection_shear, abelianFPProjection_shear,
    inner_add_left, inner_add_right]
  ring

/-- Operator congruence, rather than an isometric conjugacy in the raw L2 norm. -/
def abelianLorenzShearedRiesz :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (abelianLorenzGraphShear period hPeriod metric).toContinuousLinearMap.adjoint.comp
    ((globalPairedAbelianOffShellRieszOperator period hPeriod metric).comp
      (abelianLorenzGraphShear period hPeriod metric).toContinuousLinearMap)

theorem abelianLorenzShearedRiesz_pairing
    (first second : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    inner Real (abelianLorenzShearedRiesz period hPeriod metric first) second =
      globalPairedAbelianOffShellHessian period hPeriod metric
        (abelianLorenzGraphShear period hPeriod metric first)
        (abelianLorenzGraphShear period hPeriod metric second) := by
  unfold abelianLorenzShearedRiesz
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  exact globalPairedAbelianOffShellRieszOperator_pairing period hPeriod metric _ _

end
end P0EFTJanusProgramPT12AbelianLorenzShearPairing4D
end JanusFormal

