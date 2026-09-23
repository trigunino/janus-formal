import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Transport4D

/-! Equivalent finite-frame L² completions of actual covectors. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D

variable (source target : SmoothD8Frame period hPeriod)
variable (reference : SmoothGeneralLorentzMetric period hPeriod)

def frameCovectorL2Space (frame : SmoothD8Frame period hPeriod) :
    Submodule Real (FrameCovectorL2 period hPeriod frame) :=
  (frameCovectorL2 period hPeriod frame).range.topologicalClosure

abbrev FrameCovectorL2Completion (frame : SmoothD8Frame period hPeriod) :=
  frameCovectorL2Space period hPeriod frame

instance (frame : SmoothD8Frame period hPeriod) : CompleteSpace (FrameCovectorL2Completion period hPeriod frame) :=
  Submodule.topologicalClosure.completeSpace _

def frameCovectorL2Smooth (frame : SmoothD8Frame period hPeriod) :
    ActualSmoothCovector period hPeriod →ₗ[Real] FrameCovectorL2Completion period hPeriod frame :=
  (frameCovectorL2 period hPeriod frame).codRestrict (frameCovectorL2Space period hPeriod frame)
    (fun covector => Submodule.le_topologicalClosure _ ⟨covector, rfl⟩)

theorem frameCovectorL2Smooth_denseRange (frame : SmoothD8Frame period hPeriod) :
    DenseRange (frameCovectorL2Smooth period hPeriod frame) := by
  rw [DenseRange, Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (frameCovectorL2Smooth period hPeriod frame) =
      ((frameCovectorL2 period hPeriod frame).range : Set _) := by
    ext value
    constructor
    · rintro ⟨_, ⟨covector, rfl⟩, rfl⟩; exact ⟨covector, rfl⟩
    · rintro ⟨covector, rfl⟩
      exact ⟨frameCovectorL2Smooth period hPeriod frame covector, ⟨covector, rfl⟩, rfl⟩
  change closure ((frameCovectorL2 period hPeriod frame).range : Set (FrameCovectorL2 period hPeriod frame)) ⊆
    closure (Subtype.val '' Set.range (frameCovectorL2Smooth period hPeriod frame))
  exact (congrArg closure hRange).symm.subset

theorem frameCovectorL2Transport_mem (field : FrameCovectorL2Completion period hPeriod source) :
    frameCovectorL2Transport period hPeriod source target reference field.val ∈
      frameCovectorL2Space period hPeriod target := by
  have h : Set.MapsTo (frameCovectorL2Transport period hPeriod source target reference)
      (frameCovectorL2 period hPeriod source).range (frameCovectorL2 period hPeriod target).range := by
    rintro _ ⟨covector, rfl⟩
    exact ⟨covector, (frameCovectorL2Transport_smooth period hPeriod source target reference covector).symm⟩
  exact h.closure (frameCovectorL2Transport period hPeriod source target reference).continuous field.property

def frameCovectorL2CompletionTransport :
    FrameCovectorL2Completion period hPeriod source →L[Real] FrameCovectorL2Completion period hPeriod target :=
  ((frameCovectorL2Transport period hPeriod source target reference).comp
    (frameCovectorL2Space period hPeriod source).subtypeL).codRestrict
      (frameCovectorL2Space period hPeriod target)
      (frameCovectorL2Transport_mem period hPeriod source target reference)

theorem frameCovectorL2Transport_inverse (field : FrameCovectorL2Completion period hPeriod source) :
    frameCovectorL2Transport period hPeriod target source reference
      (frameCovectorL2Transport period hPeriod source target reference field.val) = field.val := by
  have hClosed : IsClosed {value : FrameCovectorL2 period hPeriod source |
      frameCovectorL2Transport period hPeriod target source reference
        (frameCovectorL2Transport period hPeriod source target reference value) = value} :=
    isClosed_eq ((frameCovectorL2Transport period hPeriod target source reference).continuous.comp
      (frameCovectorL2Transport period hPeriod source target reference).continuous) continuous_id
  apply (closure_minimal _ hClosed) field.property
  rintro _ ⟨covector, rfl⟩
  change frameCovectorL2Transport period hPeriod target source reference
    (frameCovectorL2Transport period hPeriod source target reference (frameCovectorL2 period hPeriod source covector)) = _
  rw [frameCovectorL2Transport_smooth, frameCovectorL2Transport_smooth]

def frameCovectorL2Equiv :
    FrameCovectorL2Completion period hPeriod source ≃L[Real] FrameCovectorL2Completion period hPeriod target where
  toLinearMap := (frameCovectorL2CompletionTransport period hPeriod source target reference).toLinearMap
  invFun := frameCovectorL2CompletionTransport period hPeriod target source reference
  left_inv field := Subtype.ext (frameCovectorL2Transport_inverse period hPeriod source target reference field)
  right_inv field := Subtype.ext (frameCovectorL2Transport_inverse period hPeriod target source reference field)
  continuous_toFun := (frameCovectorL2CompletionTransport period hPeriod source target reference).continuous
  continuous_invFun := (frameCovectorL2CompletionTransport period hPeriod target source reference).continuous

theorem frameCovectorL2Equiv_smooth (covector : ActualSmoothCovector period hPeriod) :
    frameCovectorL2Equiv period hPeriod source target reference (frameCovectorL2Smooth period hPeriod source covector) =
      frameCovectorL2Smooth period hPeriod target covector :=
  Subtype.ext (frameCovectorL2Transport_smooth period hPeriod source target reference covector)

end
end JanusFormal.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
