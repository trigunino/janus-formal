import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

/-! Bounded latitude contractions of the genuine canonical finite-frame metric jets.
Their first two latitude derivatives are proved on smooth tensors by the actual collar chain rule. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : CompactSpace (OrientationBoundary period hPeriod) :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric

abbrev FrameFreeLatitudeCompactScalar :=
  C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real)

def frameFreeSmoothLatitudeFirst (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  ∑ index : Index, normalBoundaryLatitudeFrameCoefficient period hPeriod metric index boundary latitude *
    frameDerivative period hPeriod Real frame field
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) index

def frameFreeSmoothLatitudeSecond (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  (∑ index : Index, normalBoundaryLatitudeFrameCoefficientDerivative period hPeriod metric index boundary latitude *
    frameDerivative period hPeriod Real frame field
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) index) +
  ∑ inner : Index, ∑ outer : Index,
    normalBoundaryLatitudeFrameCoefficient period hPeriod metric inner boundary latitude *
      normalBoundaryLatitudeFrameCoefficient period hPeriod metric outer boundary latitude *
      frameSecondDerivative period hPeriod frame field
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) outer inner

theorem frameFreeSmoothLatitudeValue_hasDerivAt
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    HasDerivAt (fun varied => field (normalBoundaryLatitudeFiberPoint period hPeriod boundary varied))
      (frameFreeSmoothLatitudeFirst period hPeriod metric field boundary latitude) latitude :=
  normalBoundaryLatitudeSmoothField_hasDerivAt period hPeriod metric field boundary latitude

theorem frameFreeSmoothLatitudeFirst_hasDerivAt
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    HasDerivAt (frameFreeSmoothLatitudeFirst period hPeriod metric field boundary)
      (frameFreeSmoothLatitudeSecond period hPeriod metric field boundary latitude) latitude := by
  have hTerm (index : Index) :=
    (normalBoundaryLatitudeFrameCoefficient_hasDerivAt period hPeriod metric index boundary latitude).mul
      (normalBoundaryLatitudeSmoothField_hasDerivAt period hPeriod metric
        (frameDerivativeComponentField period hPeriod frame field index) boundary latitude)
  have hSum := HasDerivAt.fun_sum (u := Finset.univ) (fun index _ => hTerm index)
  unfold frameFreeSmoothLatitudeFirst frameFreeSmoothLatitudeSecond
  simpa only [frameDerivativeComponentField, frameSecondDerivative, Pi.mul_apply,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using hSum

def frameFreeBoundaryLatitudeValueCLM (row column : Index) :
    Core →L[Real] FrameFreeLatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column)

private def spatialFirstCompact (row column index : Index) :
    Core →L[Real] FrameFreeLatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index)

private def spatialSecondCompact (row column outer inner : Index) :
    Core →L[Real] FrameFreeLatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner)

def frameFreeBoundaryLatitudeFirstCLM (row column : Index) :
    Core →L[Real] FrameFreeLatitudeCompactScalar period hPeriod :=
  ∑ index : Index,
    (ContinuousLinearMap.mul Real (FrameFreeLatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric index)).comp
      (spatialFirstCompact period hPeriod metric row column index)

def frameFreeBoundaryLatitudeSecondCLM (row column : Index) :
    Core →L[Real] FrameFreeLatitudeCompactScalar period hPeriod :=
  (∑ index : Index,
    (ContinuousLinearMap.mul Real (FrameFreeLatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientDerivativeCompact period hPeriod metric index)).comp
      (spatialFirstCompact period hPeriod metric row column index)) +
  ∑ inner : Index, ∑ outer : Index,
    (ContinuousLinearMap.mul Real (FrameFreeLatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric inner *
        normalBoundaryLatitudeFrameCoefficientCompact period hPeriod metric outer)).comp
      (spatialSecondCompact period hPeriod metric row column outer inner)

@[simp] theorem frameFreeBoundaryLatitudeValueCLM_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : OrientationBoundary period hPeriod) (latitude : ArctanCompactFiber) :
    frameFreeBoundaryLatitudeValueCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) := rfl

@[simp] theorem frameFreeBoundaryLatitudeFirstCLM_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : OrientationBoundary period hPeriod) (latitude : ArctanCompactFiber) :
    frameFreeBoundaryLatitudeFirstCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      frameFreeSmoothLatitudeFirst period hPeriod metric
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
        boundary latitude := by
  simp [frameFreeBoundaryLatitudeFirstCLM, spatialFirstCompact, frameFreeSmoothLatitudeFirst,
    normalBoundaryLatitudeFrameCoefficientCompact, normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput]

@[simp] theorem frameFreeBoundaryLatitudeSecondCLM_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index) (boundary : OrientationBoundary period hPeriod) (latitude : ArctanCompactFiber) :
    frameFreeBoundaryLatitudeSecondCLM period hPeriod metric row column
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) (boundary, latitude) =
      frameFreeSmoothLatitudeSecond period hPeriod metric
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
        boundary latitude := by
  simp [frameFreeBoundaryLatitudeSecondCLM, spatialFirstCompact, spatialSecondCompact,
    frameFreeSmoothLatitudeSecond, normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact, normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput]

def frameFreeBoundaryLatitudeTripleCLM (row column : Index) :
    Core →L[Real] (Fin 3 → FrameFreeLatitudeCompactScalar period hPeriod) :=
  ContinuousLinearMap.pi ![frameFreeBoundaryLatitudeValueCLM period hPeriod metric row column,
    frameFreeBoundaryLatitudeFirstCLM period hPeriod metric row column,
    frameFreeBoundaryLatitudeSecondCLM period hPeriod metric row column]

theorem frameFreeBoundaryLatitudeTripleCLM_norm_apply_le (row column : Index) (x : Core) :
    ‖frameFreeBoundaryLatitudeTripleCLM period hPeriod metric row column x‖ ≤
      ‖frameFreeBoundaryLatitudeTripleCLM period hPeriod metric row column‖ * ‖x‖ :=
  (frameFreeBoundaryLatitudeTripleCLM period hPeriod metric row column).le_opNorm x

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeJets4D
