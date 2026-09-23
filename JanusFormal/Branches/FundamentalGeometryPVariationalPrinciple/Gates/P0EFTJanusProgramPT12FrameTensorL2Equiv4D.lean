import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Equivalent finite-frame L² completions of actual symmetric tensors. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameTensorL2Equiv4D
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

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

variable (source target : SmoothD8Frame period hPeriod)
variable (reference : SmoothGeneralLorentzMetric period hPeriod)

def frameTensorL2Space (frame : SmoothD8Frame period hPeriod) :
    Submodule Real (FrameTensorL2 period hPeriod frame) :=
  (frameTensorL2 period hPeriod frame).range.topologicalClosure

abbrev FrameTensorL2Completion (frame : SmoothD8Frame period hPeriod) :=
  frameTensorL2Space period hPeriod frame

instance (frame : SmoothD8Frame period hPeriod) : CompleteSpace (FrameTensorL2Completion period hPeriod frame) :=
  Submodule.topologicalClosure.completeSpace _

def frameTensorL2Smooth (frame : SmoothD8Frame period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] FrameTensorL2Completion period hPeriod frame :=
  (frameTensorL2 period hPeriod frame).codRestrict (frameTensorL2Space period hPeriod frame)
    (fun tensor => Submodule.le_topologicalClosure _ ⟨tensor, rfl⟩)

theorem frameTensorL2Smooth_denseRange (frame : SmoothD8Frame period hPeriod) :
    DenseRange (frameTensorL2Smooth period hPeriod frame) := by
  rw [DenseRange, Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (frameTensorL2Smooth period hPeriod frame) =
      ((frameTensorL2 period hPeriod frame).range : Set _) := by
    ext value
    constructor
    · rintro ⟨_, ⟨tensor, rfl⟩, rfl⟩; exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact ⟨frameTensorL2Smooth period hPeriod frame tensor, ⟨tensor, rfl⟩, rfl⟩
  change closure ((frameTensorL2 period hPeriod frame).range : Set (FrameTensorL2 period hPeriod frame)) ⊆
    closure (Subtype.val '' Set.range (frameTensorL2Smooth period hPeriod frame))
  exact (congrArg closure hRange).symm.subset

theorem frameTensorL2Transport_mem (field : FrameTensorL2Completion period hPeriod source) :
    frameTensorL2Transport period hPeriod source target reference field.val ∈
      frameTensorL2Space period hPeriod target := by
  have h : Set.MapsTo (frameTensorL2Transport period hPeriod source target reference)
      (frameTensorL2 period hPeriod source).range (frameTensorL2 period hPeriod target).range := by
    rintro _ ⟨tensor, rfl⟩
    exact ⟨tensor, (frameTensorL2Transport_smooth period hPeriod source target reference tensor).symm⟩
  exact h.closure (frameTensorL2Transport period hPeriod source target reference).continuous field.property

def frameTensorL2CompletionTransport :
    FrameTensorL2Completion period hPeriod source →L[Real] FrameTensorL2Completion period hPeriod target :=
  ((frameTensorL2Transport period hPeriod source target reference).comp
    (frameTensorL2Space period hPeriod source).subtypeL).codRestrict
      (frameTensorL2Space period hPeriod target)
      (frameTensorL2Transport_mem period hPeriod source target reference)

theorem frameTensorL2Transport_inverse (field : FrameTensorL2Completion period hPeriod source) :
    frameTensorL2Transport period hPeriod target source reference
      (frameTensorL2Transport period hPeriod source target reference field.val) = field.val := by
  have hClosed : IsClosed {value : FrameTensorL2 period hPeriod source |
      frameTensorL2Transport period hPeriod target source reference
        (frameTensorL2Transport period hPeriod source target reference value) = value} :=
    isClosed_eq ((frameTensorL2Transport period hPeriod target source reference).continuous.comp
      (frameTensorL2Transport period hPeriod source target reference).continuous) continuous_id
  apply (closure_minimal _ hClosed) field.property
  rintro _ ⟨tensor, rfl⟩
  change frameTensorL2Transport period hPeriod target source reference
    (frameTensorL2Transport period hPeriod source target reference (frameTensorL2 period hPeriod source tensor)) = _
  rw [frameTensorL2Transport_smooth, frameTensorL2Transport_smooth]

def frameTensorL2Equiv :
    FrameTensorL2Completion period hPeriod source ≃L[Real] FrameTensorL2Completion period hPeriod target where
  toLinearMap := (frameTensorL2CompletionTransport period hPeriod source target reference).toLinearMap
  invFun := frameTensorL2CompletionTransport period hPeriod target source reference
  left_inv field := Subtype.ext (frameTensorL2Transport_inverse period hPeriod source target reference field)
  right_inv field := Subtype.ext (frameTensorL2Transport_inverse period hPeriod target source reference field)
  continuous_toFun := (frameTensorL2CompletionTransport period hPeriod source target reference).continuous
  continuous_invFun := (frameTensorL2CompletionTransport period hPeriod target source reference).continuous

theorem frameTensorL2Equiv_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    frameTensorL2Equiv period hPeriod source target reference (frameTensorL2Smooth period hPeriod source tensor) =
      frameTensorL2Smooth period hPeriod target tensor :=
  Subtype.ext (frameTensorL2Transport_smooth period hPeriod source target reference tensor)

theorem frameTensorL2Completion_symmetric (frame : SmoothD8Frame period hPeriod)
    (field : FrameTensorL2Completion period hPeriod frame) (first second : Fin frame.count) :
    field.val (first, second) = field.val (second, first) := by
  have hClosed : IsClosed {value : FrameTensorL2 period hPeriod frame |
      value (first, second) = value (second, first)} :=
    isClosed_eq (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin frame.count × Fin frame.count =>
      CanonicalPhysicalBulkL2 period hPeriod) (first, second)).continuous
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin frame.count × Fin frame.count =>
        CanonicalPhysicalBulkL2 period hPeriod) (second, first)).continuous
  apply (closure_minimal _ hClosed) field.property
  rintro _ ⟨tensor, rfl⟩
  apply congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact tensor.symmetric point (frame.vectorAt point first) (frame.vectorAt point second)

end
end JanusFormal.P0EFTJanusProgramPT12FrameTensorL2Equiv4D
