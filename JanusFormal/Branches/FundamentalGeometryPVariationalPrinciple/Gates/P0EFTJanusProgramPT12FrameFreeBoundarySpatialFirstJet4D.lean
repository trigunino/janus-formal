import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedLatitudeJetBuilder4D

/-! Actual C² moving-boundary evaluation of a first spatial metric derivative.
Its top latitude derivative uses the stored third metric jet and no fourth derivative. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundarySpatialFirstJet4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
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
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
open P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D
open P0EFTJanusProgramPT12BoundedLatitudeJetBuilder4D

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
local notation "Scalar" => FrameFreeLatitudeCompactScalar period hPeriod
local notation "Graph" => BoundedContinuousFunction Boundary Real

def frameFreeBoundarySpatialLatitudeValue (row column spatial : Index) : Core →L[Real] Scalar :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column spatial)

private def secondCompact (row column outer inner : Index) : Core →L[Real] Scalar :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner)

private def thirdCompact (row column outer middle inner : Index) : Core →L[Real] Scalar :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner)

def frameFreeBoundarySpatialLatitudeFirst (row column spatial : Index) : Core →L[Real] Scalar :=
  ∑ outer : Index,
    (ContinuousLinearMap.mul Real Scalar
      (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric outer)).comp
      (secondCompact period hPeriod metric row column outer spatial)

def frameFreeBoundarySpatialLatitudeSecond (row column spatial : Index) : Core →L[Real] Scalar :=
  (∑ outer : Index,
    (ContinuousLinearMap.mul Real Scalar
      (normalBoundaryLatitudeFrameCoefficientDerivativeCompact period hPeriod metric outer)).comp
      (secondCompact period hPeriod metric row column outer spatial)) +
  ∑ inner : Index, ∑ outer : Index,
    (ContinuousLinearMap.mul Real Scalar
      (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric inner *
        normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric outer)).comp
      (thirdCompact period hPeriod metric row column outer inner spatial)

def frameFreeBoundarySpatialLatitudeTriple (row column spatial : Index) :
    Core →L[Real] LatitudeTriple Boundary :=
  ContinuousLinearMap.pi ![frameFreeBoundarySpatialLatitudeValue period hPeriod metric row column spatial,
    frameFreeBoundarySpatialLatitudeFirst period hPeriod metric row column spatial,
    frameFreeBoundarySpatialLatitudeSecond period hPeriod metric row column spatial]

@[simp] theorem frameFreeBoundarySpatialLatitudeValue_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column spatial : Index)
    (boundary : Boundary) (latitude : ArctanCompactFiber) :
    frameFreeBoundarySpatialLatitudeValue period hPeriod metric row column spatial
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      frameDerivativeComponentField period hPeriod frame
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column) spatial
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) := rfl

@[simp] theorem frameFreeBoundarySpatialLatitudeFirst_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column spatial : Index)
    (boundary : Boundary) (latitude : ArctanCompactFiber) :
    frameFreeBoundarySpatialLatitudeFirst period hPeriod metric row column spatial
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      frameFreeSmoothLatitudeFirst period hPeriod metric
        (frameDerivativeComponentField period hPeriod frame
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column) spatial)
        boundary latitude := by
  simp [frameFreeBoundarySpatialLatitudeFirst, secondCompact, frameFreeSmoothLatitudeFirst,
    normalBoundaryLatitudeFrameCoefficientCompact, normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput, frameSecondDerivative]

@[simp] theorem frameFreeBoundarySpatialLatitudeSecond_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column spatial : Index)
    (boundary : Boundary) (latitude : ArctanCompactFiber) :
    frameFreeBoundarySpatialLatitudeSecond period hPeriod metric row column spatial
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      frameFreeSmoothLatitudeSecond period hPeriod metric
        (frameDerivativeComponentField period hPeriod frame
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column) spatial)
        boundary latitude := by
  simp [frameFreeBoundarySpatialLatitudeSecond, secondCompact, thirdCompact, frameFreeSmoothLatitudeSecond,
    normalBoundaryLatitudeFrameCoefficientCompact, normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM, normalBoundaryLatitudeCompactInput, frameSecondDerivative]

private theorem spatialRaw_smooth_mem (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column spatial : Index) :
    boundedLatitudeRawAmbient Boundary (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial)
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) ∈ jet2DerivativeSubmodule Boundary := by
  let field := frameDerivativeComponentField period hPeriod frame
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column) spatial
  refine boundedLatitudeRawAmbient_of_derivatives Boundary _ _
    (fun boundary latitude => field (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude))
    (frameFreeSmoothLatitudeFirst period hPeriod metric field)
    (frameFreeSmoothLatitudeSecond period hPeriod metric field) ?_ ?_ ?_ ?_ ?_
  · exact fun boundary latitude => frameFreeBoundarySpatialLatitudeValue_smooth period hPeriod metric
      tensor row column spatial boundary latitude
  · exact fun boundary latitude => frameFreeBoundarySpatialLatitudeFirst_smooth period hPeriod metric
      tensor row column spatial boundary latitude
  · exact fun boundary latitude => frameFreeBoundarySpatialLatitudeSecond_smooth period hPeriod metric
      tensor row column spatial boundary latitude
  · exact frameFreeSmoothLatitudeValue_hasDerivAt period hPeriod metric field
  · exact frameFreeSmoothLatitudeFirst_hasDerivAt period hPeriod metric field

theorem frameFreeBoundarySpatialRaw_derivative_mem (row column spatial : Index) (x : Core) :
    boundedLatitudeRawAmbient Boundary (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial) x ∈
      jet2DerivativeSubmodule Boundary :=
  boundedLatitudeRawAmbient_mem_of_dense Boundary
    (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial)
    (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric)
    (smoothToFrameFreeBoundaryC3Core_denseRange period hPeriod frame metric)
    (fun tensor => spatialRaw_smooth_mem period hPeriod metric tensor row column spatial) x

def frameFreeBoundarySpatialRawJet2CLM (row column spatial : Index) : Core →L[Real] Jet2 Boundary :=
  boundedLatitudeRawJet2 Boundary (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial)
    (frameFreeBoundarySpatialRaw_derivative_mem period hPeriod metric row column spatial)

def frameFreeBoundarySpatialFirstEvaluation (row column spatial : Index) (current : Core × Graph) : Graph :=
  boundedLatitudeEvaluation Boundary (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial)
    (frameFreeBoundarySpatialRaw_derivative_mem period hPeriod metric row column spatial) current

theorem frameFreeBoundarySpatialFirstEvaluation_contDiff_two (row column spatial : Index) :
    ContDiff Real 2 (frameFreeBoundarySpatialFirstEvaluation period hPeriod metric row column spatial) :=
  boundedLatitudeEvaluation_contDiff_two Boundary
    (frameFreeBoundarySpatialLatitudeTriple period hPeriod metric row column spatial)
    (frameFreeBoundarySpatialRaw_derivative_mem period hPeriod metric row column spatial)

@[simp] theorem frameFreeBoundarySpatialFirstEvaluation_apply (row column spatial : Index)
    (x : Core) (graph : Graph) (boundary : Boundary) :
    frameFreeBoundarySpatialFirstEvaluation period hPeriod metric row column spatial (x, graph) boundary =
      frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column spatial x
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary (Real.arctan (graph boundary))) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundarySpatialFirstJet4D
