import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D

/-! The actual completed metric-value raw second jet and its C² moving-graph evaluation. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryRawSecondJet4D
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusBoundedFiberJet2SubstitutionC2
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod
local instance : TopologicalSpace.MetrizableSpace Boundary :=
  Manifold.metrizableSpace throatCoverModelWithCorners _
local instance : MetricSpace Boundary := TopologicalSpace.metrizableSpaceMetric _
local instance : NormedAddCommGroup (Jet2 Boundary) := (jet2Submodule Boundary).normedAddCommGroup
local instance : NormedSpace Real (Jet2 Boundary) := Submodule.normedSpace (jet2Submodule Boundary)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric
local notation "Raw" => BoundedFiberField Boundary
local notation "Graph" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryRawValueCLM (row column : Index) : Core →L[Real] Raw :=
  (boundedArctanCompactPullbackCLM Boundary).comp
    (frameFreeBoundaryLatitudeValueCLM period hPeriod metric row column)

private def latitudeFirstRaw (row column : Index) : Core →L[Real] Raw :=
  (boundedArctanCompactPullbackCLM Boundary).comp
    (frameFreeBoundaryLatitudeFirstCLM period hPeriod metric row column)
private def latitudeSecondRaw (row column : Index) : Core →L[Real] Raw :=
  (boundedArctanCompactPullbackCLM Boundary).comp
    (frameFreeBoundaryLatitudeSecondCLM period hPeriod metric row column)

def frameFreeBoundaryRawFirstCLM (row column : Index) : Core →L[Real] Raw :=
  (ContinuousLinearMap.mul Real Raw ((boundedFiberArctanJet3 Boundary).1 1)).comp
    (latitudeFirstRaw period hPeriod metric row column)
def frameFreeBoundaryRawSecondCLM (row column : Index) : Core →L[Real] Raw :=
  (ContinuousLinearMap.mul Real Raw (((boundedFiberArctanJet3 Boundary).1 1) ^ 2)).comp
      (latitudeSecondRaw period hPeriod metric row column) +
    (ContinuousLinearMap.mul Real Raw ((boundedFiberArctanJet3 Boundary).1 2)).comp
      (latitudeFirstRaw period hPeriod metric row column)

def frameFreeBoundaryRawJetAmbientCLM (row column : Index) : Core →L[Real] Ambient Boundary :=
  ContinuousLinearMap.pi ![frameFreeBoundaryRawValueCLM period hPeriod metric row column,
    frameFreeBoundaryRawFirstCLM period hPeriod metric row column,
    frameFreeBoundaryRawSecondCLM period hPeriod metric row column]

private theorem rawValue_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : Boundary) (fiber : Real) :
    frameFreeBoundaryRawValueCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, fiber) =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary (Real.arctan fiber)) := rfl

private theorem rawFirst_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : Boundary) (fiber : Real) :
    frameFreeBoundaryRawFirstCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, fiber) =
      (boundedFiberArctanJet3 Boundary).1 1 (boundary, fiber) *
        frameFreeSmoothLatitudeFirst period hPeriod metric
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
          boundary (Real.arctan fiber) := by
  simp [frameFreeBoundaryRawFirstCLM, latitudeFirstRaw, arctanCompactFiberMap]

private theorem rawSecond_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : Boundary) (fiber : Real) :
    frameFreeBoundaryRawSecondCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, fiber) =
      ((boundedFiberArctanJet3 Boundary).1 1 (boundary, fiber)) ^ 2 *
        frameFreeSmoothLatitudeSecond period hPeriod metric
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
          boundary (Real.arctan fiber) +
      (boundedFiberArctanJet3 Boundary).1 2 (boundary, fiber) *
        frameFreeSmoothLatitudeFirst period hPeriod metric
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
          boundary (Real.arctan fiber) := by
  simp [frameFreeBoundaryRawSecondCLM, latitudeFirstRaw, latitudeSecondRaw, arctanCompactFiberMap]

private theorem frameFreeBoundaryRawJet_smooth_derivative_mem
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column : Index) :
    frameFreeBoundaryRawJetAmbientCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) ∈
      jet2DerivativeSubmodule Boundary := by
  let field := smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column
  refine ⟨?_, ?_⟩
  · intro boundary fiber
    change HasDerivAt (fun varied => frameFreeBoundaryRawValueCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, varied))
      (frameFreeBoundaryRawFirstCLM period hPeriod metric row column
        (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, fiber)) fiber
    have hComposed := (frameFreeSmoothLatitudeValue_hasDerivAt period hPeriod metric field boundary
      (Real.arctan fiber)).comp fiber ((boundedFiberArctanJet3 Boundary).2.1 boundary fiber)
    apply (hComposed.congr_of_eventuallyEq ?_).congr_deriv
    · rw [rawFirst_smooth]
      ring
    · filter_upwards [] with varied
      rw [rawValue_smooth]
      rfl
  · intro boundary fiber
    change HasDerivAt (fun varied => frameFreeBoundaryRawFirstCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, varied))
      (frameFreeBoundaryRawSecondCLM period hPeriod metric row column
        (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, fiber)) fiber
    have hComposed := (frameFreeSmoothLatitudeFirst_hasDerivAt period hPeriod metric field boundary
      (Real.arctan fiber)).comp fiber ((boundedFiberArctanJet3 Boundary).2.1 boundary fiber)
    have hProduct := ((boundedFiberArctanJet3 Boundary).2.2.1 boundary fiber).mul hComposed
    apply (hProduct.congr_of_eventuallyEq ?_).congr_deriv
    · rw [rawSecond_smooth]
      simp only [Function.comp_apply]
      ring
    · filter_upwards [] with varied
      rw [rawFirst_smooth]
      rfl

theorem frameFreeBoundaryRawJet_derivative_mem (row column : Index) (x : Core) :
    frameFreeBoundaryRawJetAmbientCLM period hPeriod metric row column x ∈
      jet2DerivativeSubmodule Boundary := by
  let jet := frameFreeBoundaryRawJetAmbientCLM period hPeriod metric row column
  have hClosed : IsClosed (jet ⁻¹' (jet2DerivativeSubmodule Boundary : Set (Ambient Boundary))) :=
    (jet2DerivativeSubmodule_isClosed Boundary).preimage jet.continuous
  have hSmooth : Set.range (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric) ⊆
      jet ⁻¹' (jet2DerivativeSubmodule Boundary : Set (Ambient Boundary)) := by
    rintro _ ⟨tensor, rfl⟩
    exact frameFreeBoundaryRawJet_smooth_derivative_mem period hPeriod metric tensor row column
  exact closure_minimal hSmooth hClosed
    (smoothToFrameFreeBoundaryC3Core_denseRange period hPeriod frame metric x)

private theorem frameFreeBoundaryRawSecond_uniformContinuous (row column : Index) (x : Core) :
    UniformContinuous (frameFreeBoundaryRawSecondCLM period hPeriod metric row column x) := by
  have hFirst : UniformContinuous ((boundedFiberArctanJet3 Boundary).1 1) := by
    simpa using boundedFiberArctanJet3_component_uniformContinuous Boundary (1 : Fin 3)
  have hSecond : UniformContinuous ((boundedFiberArctanJet3 Boundary).1 2) := by
    simpa using boundedFiberArctanJet3_component_uniformContinuous Boundary (2 : Fin 3)
  have hLatitudeFirst : UniformContinuous (latitudeFirstRaw period hPeriod metric row column x) :=
    boundedArctanCompactPullback_uniformContinuous Boundary
      (frameFreeBoundaryLatitudeFirstCLM period hPeriod metric row column x)
  have hLatitudeSecond : UniformContinuous (latitudeSecondRaw period hPeriod metric row column x) :=
    boundedArctanCompactPullback_uniformContinuous Boundary
      (frameFreeBoundaryLatitudeSecondCLM period hPeriod metric row column x)
  have hSquare := field_mul_uniformContinuous Boundary
    ((boundedFiberArctanJet3 Boundary).1 1) ((boundedFiberArctanJet3 Boundary).1 1) hFirst hFirst
  have hTerm1 := field_mul_uniformContinuous Boundary
    (((boundedFiberArctanJet3 Boundary).1 1) * ((boundedFiberArctanJet3 Boundary).1 1))
    (latitudeSecondRaw period hPeriod metric row column x) hSquare hLatitudeSecond
  have hTerm2 := field_mul_uniformContinuous Boundary
    ((boundedFiberArctanJet3 Boundary).1 2)
    (latitudeFirstRaw period hPeriod metric row column x) hSecond hLatitudeFirst
  change UniformContinuous (fun point =>
    ((boundedFiberArctanJet3 Boundary).1 1 point) ^ 2 *
      latitudeSecondRaw period hPeriod metric row column x point +
    (boundedFiberArctanJet3 Boundary).1 2 point *
      latitudeFirstRaw period hPeriod metric row column x point)
  simpa [pow_two] using hTerm1.add hTerm2

theorem frameFreeBoundaryRawJet_mem (row column : Index) (x : Core) :
    frameFreeBoundaryRawJetAmbientCLM period hPeriod metric row column x ∈ jet2Submodule Boundary := by
  have hDerivative := frameFreeBoundaryRawJet_derivative_mem period hPeriod metric row column x
  exact ⟨hDerivative.1, hDerivative.2,
    frameFreeBoundaryRawSecond_uniformContinuous period hPeriod metric row column x⟩

def frameFreeBoundaryRawJet2CLM (row column : Index) : Core →L[Real] Jet2 Boundary :=
  (frameFreeBoundaryRawJetAmbientCLM period hPeriod metric row column).codRestrict
    (jet2Submodule Boundary) (frameFreeBoundaryRawJet_mem period hPeriod metric row column)

def frameFreeBoundaryValueEvaluation (row column : Index) (current : Core × Graph) : Graph :=
  evaluation Boundary (frameFreeBoundaryRawJet2CLM period hPeriod metric row column current.1, current.2)

theorem frameFreeBoundaryValueEvaluation_contDiff_two (row column : Index) :
    ContDiff Real 2 (frameFreeBoundaryValueEvaluation period hPeriod metric row column) :=
  (evaluation_contDiff_two Boundary).comp
    (((frameFreeBoundaryRawJet2CLM period hPeriod metric row column).contDiff.comp contDiff_fst).prodMk
      contDiff_snd)

@[simp] theorem frameFreeBoundaryValueEvaluation_apply (row column : Index)
    (x : Core) (graph : Graph) (boundary : Boundary) :
    frameFreeBoundaryValueEvaluation period hPeriod metric row column (x, graph) boundary =
      frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column x
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary (Real.arctan (graph boundary))) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryRawSecondJet4D
