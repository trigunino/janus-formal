import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D

/-! Continuous signed ghost rotation and dense forgetful map on the actual stronger graph. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
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

open P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D

private abbrev ambientRotation := twoSidedGhostEquiv
  (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)

private theorem rotation_preserves_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∀ x ∈ abelianTwoSidedGraphSubmodule period hPeriod metric,
      ambientRotation period hPeriod x ∈ abelianTwoSidedGraphSubmodule period hPeriod metric := by
  apply topologicalClosure_invariant (ambientRotation period hPeriod).toContinuousLinearMap
  rintro x ⟨state, rfl⟩
  exact ⟨abelianGhostSignedState period hPeriod state,
    (abelianTwoSidedAmbient_rotate_smooth period hPeriod metric state).symm⟩

private theorem inverse_preserves_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∀ x ∈ abelianTwoSidedGraphSubmodule period hPeriod metric,
      (ambientRotation period hPeriod).symm x ∈ abelianTwoSidedGraphSubmodule period hPeriod metric := by
  apply topologicalClosure_invariant (ambientRotation period hPeriod).symm.toContinuousLinearMap
  rintro x ⟨state, rfl⟩
  exact ⟨abelianGhostSignedReconstruct period hPeriod state,
    (abelianTwoSidedAmbient_inverse_smooth period hPeriod metric state).symm⟩

private theorem rotation_maps_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    (abelianTwoSidedGraphSubmodule period hPeriod metric).map
      (ambientRotation period hPeriod).toLinearEquiv.toLinearMap =
    abelianTwoSidedGraphSubmodule period hPeriod metric := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact rotation_preserves_graph period hPeriod metric y hy
  · intro x hx
    exact ⟨(ambientRotation period hPeriod).symm x,
      inverse_preserves_graph period hPeriod metric x hx,
      (ambientRotation period hPeriod).apply_symm_apply x⟩

def abelianTwoSidedGhostRotation
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AbelianTwoSidedGraph period hPeriod metric ≃L[Real] AbelianTwoSidedGraph period hPeriod metric :=
  (ambientRotation period hPeriod).ofSubmodules _ _ (rotation_maps_graph period hPeriod metric)

theorem abelianTwoSidedGhostRotation_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianTwoSidedGhostRotation period hPeriod metric
      (abelianTwoSidedSmoothEmbedding period hPeriod metric state) =
    abelianTwoSidedSmoothEmbedding period hPeriod metric (abelianGhostSignedState period hPeriod state) :=
  Subtype.ext (abelianTwoSidedAmbient_rotate_smooth period hPeriod metric state)

theorem abelianTwoSidedGhostRotation_inverse_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    (abelianTwoSidedGhostRotation period hPeriod metric).symm
      (abelianTwoSidedSmoothEmbedding period hPeriod metric state) =
    abelianTwoSidedSmoothEmbedding period hPeriod metric
      (abelianGhostSignedReconstruct period hPeriod state) :=
  Subtype.ext (abelianTwoSidedAmbient_inverse_smooth period hPeriod metric state)

private theorem forget_preserves_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∀ x ∈ abelianTwoSidedGraphSubmodule period hPeriod metric,
      (WithLp.fstL 2 Real (GlobalPairedAbelianOffShellAmbient period hPeriod)
        (GlobalPairedGaugeLieL2 period hPeriod)) x ∈
        globalPairedAbelianOffShellGraphSubmodule period hPeriod metric := by
  have h : abelianTwoSidedGraphSubmodule period hPeriod metric ≤
      (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric).comap
        (WithLp.fstL 2 Real (GlobalPairedAbelianOffShellAmbient period hPeriod)
          (GlobalPairedGaugeLieL2 period hPeriod)).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro x ⟨state, rfl⟩
      exact (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric).range.le_topologicalClosure
        ⟨state, rfl⟩
    · exact (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric).range.isClosed_topologicalClosure.preimage
        (WithLp.fstL 2 Real (GlobalPairedAbelianOffShellAmbient period hPeriod)
          (GlobalPairedGaugeLieL2 period hPeriod)).continuous
  exact h

/-- Forget only FP(antighost). Injectivity of this map is not asserted. -/
def abelianTwoSidedForget (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AbelianTwoSidedGraph period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (WithLp.fstL 2 Real (GlobalPairedAbelianOffShellAmbient period hPeriod)
    (GlobalPairedGaugeLieL2 period hPeriod)).restrict (forget_preserves_graph period hPeriod metric)

@[simp] theorem abelianTwoSidedForget_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianTwoSidedForget period hPeriod metric (abelianTwoSidedSmoothEmbedding period hPeriod metric state) =
    globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric state := rfl

theorem abelianTwoSidedForget_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange (abelianTwoSidedForget period hPeriod metric) := by
  apply (globalPairedAbelianOffShellSmoothEmbedding_denseRange period hPeriod metric).mono
  rintro x ⟨state, rfl⟩
  exact ⟨abelianTwoSidedSmoothEmbedding period hPeriod metric state, rfl⟩

theorem abelianTwoSidedSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective (abelianTwoSidedSmoothEmbedding period hPeriod metric) := by
  intro first second h
  apply globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod metric
  exact congrArg (abelianTwoSidedForget period hPeriod metric) h

end
end P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
end JanusFormal
