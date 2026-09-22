import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NilpotentGraphShear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D

/-! The genuine geometric Lorenz shear is an automorphism of the completed
paired Abelian graph. No spectral transform or L2 closability is assumed. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
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

open P0EFTJanusProgramPT12NilpotentGraphShear4D
open P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D

/-- Insert an L2 auxiliary field in the ambient feature Hilbert space. -/
def abelianBAmbientInclusion : GlobalPairedGaugeLieL2 period hPeriod →ₗᵢ[Real]
    GlobalPairedAbelianOffShellAmbient period hPeriod where
  toFun vector := WithLp.toLp 2 (0, WithLp.toLp 2 (vector, 0))
  map_add' first second := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (first + second, 0)) =
      WithLp.toLp 2 (0 + 0, WithLp.toLp 2 (first + second, 0 + 0))
    rw [zero_add, zero_add]
  map_smul' scalar vector := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (scalar • vector, 0)) =
      WithLp.toLp 2 (scalar • 0, WithLp.toLp 2 (scalar • vector, scalar • 0))
    rw [smul_zero, smul_zero]
  norm_map' vector :=
    (WithLp.norm_toLp_snd 2 _ _ _).trans (WithLp.norm_toLp_fst 2 _ _ vector)

def abelianLorenzAmbientIncrement : GlobalPairedAbelianOffShellAmbient period hPeriod →L[Real]
    GlobalPairedAbelianOffShellAmbient period hPeriod :=
  (abelianBAmbientInclusion period hPeriod).toContinuousLinearMap.comp
    ((WithLp.sndL 2 Real _ _).comp (WithLp.fstL 2 Real _ _))

def abelianLorenzSmoothIncrement
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod :=
  pureAbelianNakanishiLautrup period hPeriod (fun sector =>
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod
      (metric sector) (state.potential sector))

theorem abelianLorenzAmbientIncrement_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianLorenzAmbientIncrement period hPeriod
        (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric state) =
      globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric
        (abelianLorenzSmoothIncrement period hPeriod metric state) := by
  change WithLp.toLp 2 (0, WithLp.toLp 2
      (globalPairedAbelianLorenzL2LinearMap period hPeriod metric state.potential, 0)) =
    WithLp.toLp 2
      (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric 0,
        WithLp.toLp 2
          (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
            globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric sector) (state.potential sector)),
            WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod 0,
              WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod 0,
                globalPairedAbelianFPL2LinearMap period hPeriod metric 0))))
  simp only [map_zero]
  rfl

theorem abelianLorenzAmbientIncrement_preserves_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∀ vector ∈ globalPairedAbelianOffShellGraphSubmodule period hPeriod metric,
      abelianLorenzAmbientIncrement period hPeriod vector ∈
        globalPairedAbelianOffShellGraphSubmodule period hPeriod metric := by
  apply topologicalClosure_invariant
  rintro vector ⟨state, rfl⟩
  exact ⟨abelianLorenzSmoothIncrement period hPeriod metric state,
    (abelianLorenzAmbientIncrement_smooth period hPeriod metric state).symm⟩

def abelianLorenzGraphIncrement
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (abelianLorenzAmbientIncrement period hPeriod).restrict
    (abelianLorenzAmbientIncrement_preserves_graph period hPeriod metric)

theorem abelianLorenzGraphIncrement_square_zero
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (vector : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    abelianLorenzGraphIncrement period hPeriod metric
      (abelianLorenzGraphIncrement period hPeriod metric vector) = 0 := by
  apply Subtype.ext
  rfl

/-- The bounded geometric change B -> B + delta_g A, with bounded inverse. -/
def abelianLorenzGraphShear
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric ≃L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  nilpotentShear (abelianLorenzGraphIncrement period hPeriod metric)
    (abelianLorenzGraphIncrement_square_zero period hPeriod metric)

theorem abelianLorenzGraphIncrement_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianLorenzGraphIncrement period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric state) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianLorenzSmoothIncrement period hPeriod metric state) :=
  Subtype.ext (abelianLorenzAmbientIncrement_smooth period hPeriod metric state)

theorem abelianLorenzGraphShear_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianLorenzGraphShear period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric state) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (state + abelianLorenzSmoothIncrement period hPeriod metric state) := by
  rw [abelianLorenzGraphShear, nilpotentShear_apply,
    abelianLorenzGraphIncrement_smooth, map_add]

end
end P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
end JanusFormal
