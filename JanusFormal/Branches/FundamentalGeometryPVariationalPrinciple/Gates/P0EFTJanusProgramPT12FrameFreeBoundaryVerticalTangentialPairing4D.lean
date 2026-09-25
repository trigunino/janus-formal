import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D

/-! C² readings of the genuine covector g(V, T·), with exact smooth agreement.
The ambient generating family remains redundant. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryVerticalTangentialPairing4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D

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
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryVerticalEvaluation (row : Index) (current : Input) : Field :=
  frameFreeBoundaryVerticalCoefficientEvaluation period hPeriod frame metric row
    (frameFreeBoundaryNormalInput period hPeriod metric current)

theorem frameFreeBoundaryVerticalEvaluation_contDiff_two (row : Index) :
    ContDiff Real 2 (frameFreeBoundaryVerticalEvaluation period hPeriod metric row) :=
  (frameFreeBoundaryVerticalCoefficientEvaluation_contDiff_two period hPeriod frame metric row).comp
    (frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric)

theorem frameFreeBoundaryVerticalEvaluation_smooth_reconstructs
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    (∑ row : Index, frameFreeBoundaryVerticalEvaluation period hPeriod metric row (variation, parameter) boundary •
      (finiteSmoothTangentFrame period hPeriod).vectorAt point row) =
      normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary := by
  dsimp only
  let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
  let normal := smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement
  let latitude := Real.arctan (parameter *
    normalDisplacementOrientationScalar period hPeriod displacement boundary)
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  have hCoefficient (row : Index) :
      frameFreeBoundaryVerticalEvaluation period hPeriod metric row (variation, parameter) boundary =
      frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude) := by
    unfold frameFreeBoundaryVerticalEvaluation
    rw [frameFreeBoundaryVerticalCoefficientEvaluation_apply]
    change frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row
      (boundary, Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) = _
    dsimp only [latitude, normal]
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hPoint : normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude = point := by
    change normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (Real.arctan (parameter * normalDisplacementOrientationScalar period hPeriod displacement boundary)) = _
    rw [← normalBoundaryC2JetCoreValueAt_smooth period hPeriod displacement boundary]
    rw [← normalBoundaryRawFiberPoint_eq_latitude, normalBoundaryRawFiberPoint_graph,
      normalBoundaryC2Graph_smooth]
  have hVertical := frameFreeBoundaryLiftCoefficient_reconstructs period hPeriod frame metric
    (fun current => normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2) (boundary, latitude)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  change (normalBoundaryLatitudeFiberLift period hPeriod boundary latitude).2 =
    ∑ row : Index, frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude) •
      (finiteSmoothTangentFrame period hPeriod).vectorAt
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) row at hVertical
  rw [hPoint] at hVertical
  have hCanonical := normalGraphCanonicalLatitudeVector_smooth_heq_normalBoundaryLatitudeFiberLift
    period hPeriod displacement parameter boundary
  change (∑ row : Index, frameFreeBoundaryVerticalEvaluation period hPeriod metric row (variation, parameter) boundary •
    (finiteSmoothTangentFrame period hPeriod).vectorAt point row) = _
  simp_rw [hCoefficient]
  exact eq_of_heq ((heq_of_eq hVertical.symm).trans hCanonical.symm)

def frameFreeBoundaryVerticalTangentialPairingEvaluation (index : TangentIndex) (current : Input) : Field :=
  ∑ first : Index, ∑ second : Index,
    frameFreeBoundaryVerticalEvaluation period hPeriod metric first current *
      frameFreeBoundaryActualMetricEvaluation period hPeriod metric first second current *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index second current

theorem frameFreeBoundaryVerticalTangentialPairingEvaluation_contDiff_two (index : TangentIndex) :
    ContDiff Real 2 (frameFreeBoundaryVerticalTangentialPairingEvaluation period hPeriod metric index) := by
  unfold frameFreeBoundaryVerticalTangentialPairingEvaluation
  exact ContDiff.sum fun first _ => ContDiff.sum fun second _ =>
    ((frameFreeBoundaryVerticalEvaluation_contDiff_two period hPeriod metric first).mul
      (frameFreeBoundaryActualMetricEvaluation_contDiff_two period hPeriod metric first second)).mul
        (frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric index second)

theorem frameFreeBoundaryVerticalTangentialPairingEvaluation_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (boundary : Boundary) (index : TangentIndex) :
    frameFreeBoundaryVerticalTangentialPairingEvaluation period hPeriod metric index
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod variedMetric displacement parameter boundary
        ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index) := by
  let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  have hMetric (first second : Index) :
      frameFreeBoundaryActualMetricEvaluation period hPeriod metric first second (variation, parameter) boundary =
      variedMetric.tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point first)
        ((finiteSmoothTangentFrame period hPeriod).vectorAt point second) := by
    simpa only [hVaried] using frameFreeBoundaryActualMetricEvaluation_smooth
      period hPeriod metric tensor displacement parameter boundary first second
  have hVertical := frameFreeBoundaryVerticalEvaluation_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary
  have hTangent := frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary index
  unfold frameFreeBoundaryVerticalTangentialPairingEvaluation normalBoundarySmoothGraphVerticalTangentialCovector
  simp only [BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
    ContinuousLinearMap.comp_apply]
  change (∑ first : Index, ∑ second : Index,
      frameFreeBoundaryVerticalEvaluation period hPeriod metric first (variation, parameter) boundary *
        frameFreeBoundaryActualMetricEvaluation period hPeriod metric first second (variation, parameter) boundary *
          frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index second (variation, parameter) boundary) =
    variedMetric.tensor.tensor point
    (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary)
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : Boundary => normalGraphOrientationDouble period hPeriod displacement (current, parameter))
      boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index))
  simp_rw [hMetric]
  rw [← hVertical, ← hTangent]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryVerticalTangentialPairing4D
