import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TwoSidedGhostAmbient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D

/-! The closed actual Abelian feature graph additionally controlling FP(antighost). -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
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

open P0EFTJanusProgramPT12GhostRotationDefect4D

open P0EFTJanusProgramPT12TwoSidedGhostAmbient4D
open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPT12NilpotentGraphShear4D

abbrev AbelianTwoSidedAmbient := TwoSidedGhostAmbient
  (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)

def abelianAntighostLinearMap : GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
    GlobalPairedGaugeLieSmooth period hPeriod where
  toFun := abelianAntighost period hPeriod
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def abelianTwoSidedAmbientSmooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real] AbelianTwoSidedAmbient period hPeriod :=
  (WithLp.linearEquiv 2 Real _).symm.toLinearMap.comp
    ((globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric).prod
      ((globalPairedAbelianFPL2LinearMap period hPeriod metric).comp
        (abelianAntighostLinearMap period hPeriod)))

def abelianTwoSidedGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (AbelianTwoSidedAmbient period hPeriod) :=
  (abelianTwoSidedAmbientSmooth period hPeriod metric).range.topologicalClosure

abbrev AbelianTwoSidedGraph (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  abelianTwoSidedGraphSubmodule period hPeriod metric

instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (AbelianTwoSidedGraph period hPeriod metric) :=
  Submodule.topologicalClosure.completeSpace _

def abelianTwoSidedSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real] AbelianTwoSidedGraph period hPeriod metric :=
  (abelianTwoSidedAmbientSmooth period hPeriod metric).codRestrict _
    (fun state => (abelianTwoSidedAmbientSmooth period hPeriod metric).range.le_topologicalClosure
      ⟨state, rfl⟩)

theorem abelianTwoSidedSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange (abelianTwoSidedSmoothEmbedding period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (abelianTwoSidedSmoothEmbedding period hPeriod metric) =
      ((abelianTwoSidedAmbientSmooth period hPeriod metric).range : Set (AbelianTwoSidedAmbient period hPeriod)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨state, rfl⟩, rfl⟩
      exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact ⟨abelianTwoSidedSmoothEmbedding period hPeriod metric state, ⟨state, rfl⟩, rfl⟩
  change closure ((abelianTwoSidedAmbientSmooth period hPeriod metric).range : Set (AbelianTwoSidedAmbient period hPeriod)) ⊆ _
  exact (congrArg closure hRange).symm.le

/-- The full signed rotation commutes with the authentic feature map. -/
theorem abelianTwoSidedAmbient_rotate_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    twoSidedGhostRotate (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
      (GlobalPairedGaugeLieL2 period hPeriod) 1
      (abelianTwoSidedAmbientSmooth period hPeriod metric state) =
    abelianTwoSidedAmbientSmooth period hPeriod metric (abelianGhostSignedState period hPeriod state) :=
  twoSidedGhostRotate_features _ _
    (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)
    (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric state.potential)
    (globalPairedGaugeLieL2LinearMap period hPeriod
      (fun sector => (state.nonminimal sector).nakanishiLautrup.field))
    (abelianAntighost period hPeriod state) (abelianGhost period hPeriod state)
/-- The inverse rotation also preserves the same smooth feature range. -/
theorem abelianTwoSidedAmbient_inverse_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    (twoSidedGhostEquiv (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
      (GlobalPairedGaugeLieL2 period hPeriod)).symm
      (abelianTwoSidedAmbientSmooth period hPeriod metric state) =
    abelianTwoSidedAmbientSmooth period hPeriod metric
      (abelianGhostSignedReconstruct period hPeriod state) := by
  apply (twoSidedGhostEquiv (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
    (GlobalPairedGaugeLieL2 period hPeriod)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change _ = twoSidedGhostRotate _ _ 1 _
  rw [abelianTwoSidedAmbient_rotate_smooth, abelianGhostSignedState_reconstruct]

end
end P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
end JanusFormal
