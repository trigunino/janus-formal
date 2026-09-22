import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NilpotentGraphShear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D

/-! Continuous inclusion of the potential Lorenz graph with zero nonminimal fields. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianPotentialGraphInclusion4D
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

/-- The physical potential, with all three nonminimal fields zero. -/
def abelianPurePotential (potential : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod := ⟨potential, 0⟩

def abelianPotentialAmbientInclusion : GlobalPairedAbelianLorenzGraphAmbient period hPeriod →ₗᵢ[Real]
    GlobalPairedAbelianOffShellAmbient period hPeriod where
  toFun vector := WithLp.toLp 2 (vector, 0)
  map_add' x y := by change WithLp.toLp 2 (x + y, 0) = WithLp.toLp 2 (x + y, 0 + 0); rw [zero_add]
  map_smul' r x := by change WithLp.toLp 2 (r • x, 0) = WithLp.toLp 2 (r • x, r • 0); rw [smul_zero]
  norm_map' x := WithLp.norm_toLp_fst 2 _ _ x

theorem abelianPotentialAmbientInclusion_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    abelianPotentialAmbientInclusion period hPeriod
      (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric potential) =
    globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric
      (abelianPurePotential period hPeriod potential) := by
  change WithLp.toLp 2 (_, 0) = WithLp.toLp 2 (_, WithLp.toLp 2
    (globalPairedGaugeLieL2LinearMap period hPeriod 0, WithLp.toLp 2
      (globalPairedGaugeLieL2LinearMap period hPeriod 0, WithLp.toLp 2
        (globalPairedGaugeLieL2LinearMap period hPeriod 0,
          globalPairedAbelianFPL2LinearMap period hPeriod metric 0))))
  simp only [map_zero]
  rfl

theorem abelianPotentialAmbientInclusion_mem
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∀ x ∈ globalPairedAbelianLorenzGraphSubmodule period hPeriod metric,
      abelianPotentialAmbientInclusion period hPeriod x ∈
        globalPairedAbelianOffShellGraphSubmodule period hPeriod metric := by
  have h : globalPairedAbelianLorenzGraphSubmodule period hPeriod metric ≤
      (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric).comap
        (abelianPotentialAmbientInclusion period hPeriod).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨potential, rfl⟩
      change abelianPotentialAmbientInclusion period hPeriod
        (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric potential) ∈
          globalPairedAbelianOffShellGraphSubmodule period hPeriod metric
      rw [abelianPotentialAmbientInclusion_smooth]
      exact (LinearMap.range (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric)).le_topologicalClosure
        ⟨abelianPurePotential period hPeriod potential, rfl⟩
    · exact (LinearMap.range (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric)).isClosed_topologicalClosure.preimage
        (abelianPotentialAmbientInclusion period hPeriod).continuous
  exact h

/-- Bounded inclusion of the entire Lorenz graph, not only its smooth image. -/
def abelianPotentialGraphInclusion (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (((abelianPotentialAmbientInclusion period hPeriod).toContinuousLinearMap).comp
    (globalPairedAbelianLorenzGraphSubmodule period hPeriod metric).subtypeL).codRestrict
      (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric)
      (fun x => abelianPotentialAmbientInclusion_mem period hPeriod metric x.val x.property)

theorem abelianPotentialGraphInclusion_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    abelianPotentialGraphInclusion period hPeriod metric
      (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric potential) =
    globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
      (abelianPurePotential period hPeriod potential) :=
  Subtype.ext (abelianPotentialAmbientInclusion_smooth period hPeriod metric potential)

end
end P0EFTJanusProgramPT12AbelianPotentialGraphInclusion4D
end JanusFormal
