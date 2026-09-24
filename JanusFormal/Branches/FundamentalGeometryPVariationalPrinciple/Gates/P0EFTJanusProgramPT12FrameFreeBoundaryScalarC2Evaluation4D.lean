import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedLatitudeJetBuilder4D

/-! Moving evaluation of the existing scalar C² completion. The closed latitude
builder supplies the derivative identities; no third scalar jet is required. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryScalarC2Evaluation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusBoundedFiberJet2SubstitutionC2
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
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : TopologicalSpace.MetrizableSpace Boundary := Manifold.metrizableSpace throatCoverModelWithCorners _
local instance : MetricSpace Boundary := TopologicalSpace.metrizableSpaceMetric _
local notation "Scalar" => CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : NormedAddCommGroup Scalar := (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real Scalar := inferInstance
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "CompactScalar" => FrameFreeLatitudeCompactScalar period hPeriod
local notation "Graph" => BoundedContinuousFunction Boundary Real

private def scalarCompactProjection (projection : ScalarFrameJet2 Index →L[Real] Real) : Scalar →L[Real] CompactScalar :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    ((projection.compLeftContinuous Real (EffectiveQuotient period hPeriod)).comp
      (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod))

private def firstCoordinate (index : Index) : ScalarFrameJet2 Index →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _))

private def secondCoordinate (outer inner : Index) : ScalarFrameJet2 Index →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp ((ContinuousLinearMap.proj outer).comp
    ((ContinuousLinearMap.snd Real (Index → Real) (Index → Index → Real)).comp
      (ContinuousLinearMap.snd Real Real ((Index → Real) × (Index → Index → Real)))))

@[simp] private theorem scalarFirstCompact_smooth
    (field : SmoothQuotientField period hPeriod Real) (index : Index)
    (boundary : Boundary) (latitude : ArctanCompactFiber) :
    scalarCompactProjection period hPeriod (firstCoordinate period hPeriod index)
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) (boundary, latitude) =
      frameDerivative period hPeriod Real (finiteSmoothTangentFrame period hPeriod) field
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) index := rfl

@[simp] private theorem scalarSecondCompact_smooth
    (field : SmoothQuotientField period hPeriod Real) (outer inner : Index)
    (boundary : Boundary) (latitude : ArctanCompactFiber) :
    scalarCompactProjection period hPeriod (secondCoordinate period hPeriod outer inner)
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) (boundary, latitude) =
      frameSecondDerivative period hPeriod (finiteSmoothTangentFrame period hPeriod) field
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) outer inner := rfl

variable (metric : SmoothGeneralLorentzMetric period hPeriod)

private def scalarLatitudeFirst : Scalar →L[Real] CompactScalar :=
  ∑ index : Index, (ContinuousLinearMap.mul Real CompactScalar
    (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric index)).comp
      (scalarCompactProjection period hPeriod (firstCoordinate period hPeriod index))

private def scalarLatitudeSecond : Scalar →L[Real] CompactScalar :=
  (∑ index : Index, (ContinuousLinearMap.mul Real CompactScalar
    (normalBoundaryLatitudeFrameCoefficientDerivativeCompact period hPeriod metric index)).comp
      (scalarCompactProjection period hPeriod (firstCoordinate period hPeriod index))) +
  ∑ inner : Index, ∑ outer : Index, (ContinuousLinearMap.mul Real CompactScalar
    (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric inner *
      normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric outer)).comp
      (scalarCompactProjection period hPeriod (secondCoordinate period hPeriod outer inner))

private def scalarLatitudeTriple : Scalar →L[Real] LatitudeTriple Boundary :=
  ContinuousLinearMap.pi ![
    scalarCompactProjection period hPeriod (ContinuousLinearMap.fst Real _ _),
    scalarLatitudeFirst period hPeriod metric, scalarLatitudeSecond period hPeriod metric]

private theorem scalarRaw_smooth_mem (field : SmoothQuotientField period hPeriod Real) :
    boundedLatitudeRawAmbient Boundary (scalarLatitudeTriple period hPeriod metric)
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) ∈ jet2DerivativeSubmodule Boundary := by
  refine boundedLatitudeRawAmbient_of_derivatives Boundary _ _
    (fun boundary latitude => field (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude))
    (frameFreeSmoothLatitudeFirst period hPeriod metric field)
    (frameFreeSmoothLatitudeSecond period hPeriod metric field) ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ => rfl
  · intro boundary latitude
    simp [scalarLatitudeTriple, scalarLatitudeFirst,
      frameFreeSmoothLatitudeFirst, normalBoundaryLatitudeFrameCoefficientCompact]
  · intro boundary latitude
    simp [scalarLatitudeTriple, scalarLatitudeSecond,
      frameFreeSmoothLatitudeSecond, normalBoundaryLatitudeFrameCoefficientCompact,
      normalBoundaryLatitudeFrameCoefficientDerivativeCompact]
  · exact frameFreeSmoothLatitudeValue_hasDerivAt period hPeriod metric field
  · exact frameFreeSmoothLatitudeFirst_hasDerivAt period hPeriod metric field

private theorem scalarRaw_derivative_mem (scalar : Scalar) :
    boundedLatitudeRawAmbient Boundary (scalarLatitudeTriple period hPeriod metric) scalar ∈
      jet2DerivativeSubmodule Boundary :=
  boundedLatitudeRawAmbient_mem_of_dense Boundary (scalarLatitudeTriple period hPeriod metric)
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod)
    (scalarRaw_smooth_mem period hPeriod metric) scalar

def frameFreeBoundaryScalarC2Evaluation (current : Scalar × Graph) : Graph :=
  boundedLatitudeEvaluation Boundary (scalarLatitudeTriple period hPeriod metric)
    (scalarRaw_derivative_mem period hPeriod metric) current

theorem frameFreeBoundaryScalarC2Evaluation_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryScalarC2Evaluation period hPeriod metric) :=
  boundedLatitudeEvaluation_contDiff_two Boundary (scalarLatitudeTriple period hPeriod metric)
    (scalarRaw_derivative_mem period hPeriod metric)

@[simp] theorem frameFreeBoundaryScalarC2Evaluation_apply
    (scalar : Scalar) (graph : Graph) (boundary : Boundary) :
    frameFreeBoundaryScalarC2Evaluation period hPeriod metric (scalar, graph) boundary =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod scalar
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary (Real.arctan (graph boundary))) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryScalarC2Evaluation4D
