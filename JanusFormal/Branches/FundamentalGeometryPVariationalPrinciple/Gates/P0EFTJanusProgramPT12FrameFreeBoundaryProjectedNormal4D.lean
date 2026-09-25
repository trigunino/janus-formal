import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryVerticalTangentialPairing4D

/-! The actual metric-normal projection V − T(L⁻¹Db), before normalization. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
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
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
open P0EFTJanusProgramPT12FrameFreeBoundaryVerticalTangentialPairing4D

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
local instance : ChartedSpace ThroatCoverModel (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryTangentialCoefficientEvaluation (current : Input) : TangentIndex → Field :=
  frameFreeBoundaryTangentialProjectionEvaluation period hPeriod metric
    (current, fun index => frameFreeBoundaryVerticalTangentialPairingEvaluation period hPeriod metric index current)

theorem frameFreeBoundaryTangentialCoefficientEvaluation_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric)
      (frameFreeBoundaryInducedDomain period hPeriod metric) := by
  have hReadings : ContDiff Real 2 (fun current : Input => fun index : TangentIndex =>
      frameFreeBoundaryVerticalTangentialPairingEvaluation period hPeriod metric index current) :=
    contDiff_pi.mpr (frameFreeBoundaryVerticalTangentialPairingEvaluation_contDiff_two period hPeriod metric)
  exact (frameFreeBoundaryTangentialProjectionEvaluation_contDiffOn_two period hPeriod metric).comp
    (contDiff_id.prodMk hReadings).contDiffOn (fun _ h => ⟨h, Set.mem_univ _⟩)

def frameFreeBoundaryProjectedNormalEvaluation (upper : Index) (current : Input) : Field :=
  frameFreeBoundaryVerticalEvaluation period hPeriod metric upper current -
    ∑ index : TangentIndex, frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric current index *
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index upper current

theorem frameFreeBoundaryProjectedNormalEvaluation_contDiffOn_two (upper : Index) :
    ContDiffOn Real 2 (frameFreeBoundaryProjectedNormalEvaluation period hPeriod metric upper)
      (frameFreeBoundaryInducedDomain period hPeriod metric) := by
  unfold frameFreeBoundaryProjectedNormalEvaluation
  exact (frameFreeBoundaryVerticalEvaluation_contDiff_two period hPeriod metric upper).contDiffOn.sub
    (ContDiffOn.sum fun index _ =>
      (contDiffOn_pi.mp (frameFreeBoundaryTangentialCoefficientEvaluation_contDiffOn_two period hPeriod metric) index).mul
        (frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric index upper).contDiffOn)

def frameFreeBoundaryTangentialProjectionVector (current : Input) (boundary : Boundary) :
    TangentSpace throatCoverModelWithCorners boundary :=
  intrinsicThroatFiniteFrameSynthesisAt
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
    (fun index => frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric current index boundary)

def frameFreeBoundaryProjectedNormalVector
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    TangentSpace coverModelWithCorners (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :=
  ∑ upper : Index, frameFreeBoundaryProjectedNormalEvaluation period hPeriod metric upper
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary •
      (finiteSmoothTangentFrame period hPeriod).vectorAt
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) upper

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
local notation "current" => (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)

private theorem finiteProjectedSum {I J E : Type*} [Fintype I] [Fintype J]
    [AddCommGroup E] [Module Real E] (vectors : I → E)
    (vertical : I → Real) (tangents : J → I → Real) (coefficients : J → Real) :
    (∑ upper : I, (vertical upper - ∑ index : J, coefficients index * tangents index upper) • vectors upper) =
      (∑ upper : I, vertical upper • vectors upper) -
        ∑ index : J, coefficients index • ∑ upper : I, tangents index upper • vectors upper := by
  simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
  congr 1
  rw [Finset.sum_comm]

private theorem projectionDerivative_eq_sum (boundary : Boundary) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun point : Boundary => normalGraphOrientationDouble period hPeriod displacement (point, parameter)) boundary
      (frameFreeBoundaryTangentialProjectionVector period hPeriod metric current boundary) =
      ∑ index : TangentIndex, frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric current index boundary •
        ∑ upper : Index, frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index upper current boundary •
          (finiteSmoothTangentFrame period hPeriod).vectorAt
            (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) upper := by
  unfold frameFreeBoundaryTangentialProjectionVector
  rw [intrinsicThroatFiniteFrameSynthesisAt_apply, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul]
  exact congrArg (fun vector =>
    frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric current index boundary • vector)
      (frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs
        period hPeriod metric tensor displacement parameter boundary index).symm

private theorem projectedNormalVector_eq_sub (boundary : Boundary) :
    frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary =
      normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary -
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : Boundary => normalGraphOrientationDouble period hPeriod displacement (point, parameter)) boundary
          (frameFreeBoundaryTangentialProjectionVector period hPeriod metric current boundary) := by
  have hAlgebra := finiteProjectedSum
    (fun upper : Index => (finiteSmoothTangentFrame period hPeriod).vectorAt
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) upper)
    (fun upper => frameFreeBoundaryVerticalEvaluation period hPeriod metric upper current boundary)
    (fun index upper => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index upper current boundary)
    (fun index => frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod metric current index boundary)
  rw [frameFreeBoundaryVerticalEvaluation_smooth_reconstructs
      period hPeriod metric tensor displacement parameter boundary,
    ← projectionDerivative_eq_sum period hPeriod metric tensor displacement parameter boundary] at hAlgebra
  unfold frameFreeBoundaryProjectedNormalVector frameFreeBoundaryProjectedNormalEvaluation
  simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply] using hAlgebra

variable (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (hCurrent :
    ((smoothToFrameFreeBoundaryJointCore period hPeriod (finiteSmoothTangentFrame period hPeriod) metric
      (tensor, displacement), parameter) :
      FrameFreeBoundaryJointCore period hPeriod (finiteSmoothTangentFrame period hPeriod) metric × Real) ∈
        frameFreeBoundaryInducedDomain period hPeriod metric)

include hVaried hCurrent in
private theorem projectionVector_smooth_musical (boundary : Boundary) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric displacement parameter boundary
      (frameFreeBoundaryTangentialProjectionVector period hPeriod metric current boundary) =
      normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod variedMetric displacement parameter boundary := by
  have hVector : frameFreeBoundaryTangentialProjectionVector period hPeriod metric current boundary =
      frameFreeBoundaryInducedInverseMusicalAt period hPeriod metric current boundary
        (normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod variedMetric displacement parameter boundary) := by
    unfold frameFreeBoundaryTangentialProjectionVector frameFreeBoundaryTangentialCoefficientEvaluation
      frameFreeBoundaryTangentialProjectionEvaluation frameFreeBoundaryInducedInverseMusicalAt
    congr 1
    funext row
    simp only [BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp_rw [frameFreeBoundaryVerticalTangentialPairingEvaluation_smooth
      period hPeriod metric tensor variedMetric hVaried displacement parameter boundary]
  rw [hVector]
  exact frameFreeBoundaryInducedInverseMusicalAt_smooth period hPeriod metric tensor variedMetric hVaried
    displacement parameter hCurrent boundary _

include hVaried hCurrent in
private theorem projectionVector_smooth_eq_historical (boundary : Boundary) :
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
      (frameFreeBoundaryTangentialProjectionVector period hPeriod metric current boundary) =
      normalGraphInducedMetricInverse period hPeriod variedMetric displacement parameter
        (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
          period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphTangentialPairing period hPeriod variedMetric displacement parameter
          (orientationDoubleToThroat period hPeriod boundary)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary)) := by
  let tangentEquiv := normalBoundaryOrientationTangentEquiv period hPeriod boundary
  apply (normalGraphInducedMetricEquiv period hPeriod variedMetric displacement parameter
    (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
      period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent)
    (orientationDoubleToThroat period hPeriod boundary)).injective
  rw [normalGraphInducedMetricEquiv_apply, normalGraphInducedMetricEquiv_apply,
    normalGraphInducedMetric_metricInverse]
  apply ContinuousLinearMap.ext
  intro targetSecond
  have hMusical := congrArg (fun covector : TangentSpace throatCoverModelWithCorners boundary →L[Real] Real =>
      covector (tangentEquiv.symm targetSecond))
    (projectionVector_smooth_musical period hPeriod metric tensor displacement parameter variedMetric hVaried hCurrent boundary)
  rw [normalBoundarySmoothGraphInducedMetricMusical_apply] at hMusical
  unfold normalBoundarySmoothGraphVerticalTangentialCovector at hMusical
  simp only [ContinuousLinearMap.comp_apply] at hMusical
  rw [normalGraphOrientationDouble_mfderiv_eq_comp, ← normalBoundaryOrientationTangentEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hMusical
  exact hMusical

include hVaried hCurrent in
theorem frameFreeBoundaryProjectedNormalVector_smooth (boundary : Boundary) :
    frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary =
      normalGraphMetricNormal period hPeriod variedMetric displacement parameter
        (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
          period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary) := by
  rw [projectedNormalVector_eq_sub period hPeriod metric tensor displacement parameter boundary]
  unfold normalGraphMetricNormal normalGraphTangentialProjection
  congr 1
  rw [normalGraphOrientationDouble_mfderiv_eq_comp, ← normalBoundaryOrientationTangentEquiv_apply,
    projectionVector_smooth_eq_historical period hPeriod metric tensor displacement parameter variedMetric hVaried hCurrent]

include hVaried hCurrent in
theorem frameFreeBoundaryProjectedNormalVector_smooth_orthogonal (boundary : Boundary)
    (tangent : TangentSpace throatCoverModelWithCorners boundary) :
    variedMetric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
      (frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : Boundary => normalGraphOrientationDouble period hPeriod displacement (point, parameter)) boundary tangent) = 0 := by
  rw [frameFreeBoundaryProjectedNormalVector_smooth period hPeriod metric tensor displacement parameter variedMetric hVaried hCurrent]
  rw [normalGraphOrientationDouble_mfderiv_eq_comp, ← normalBoundaryOrientationTangentEquiv_apply]
  exact normalGraphMetricNormal_orthogonal period hPeriod variedMetric displacement parameter
    (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
      period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent)
    (orientationDoubleToThroat period hPeriod boundary)
    (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary)
    (normalBoundaryOrientationTangentEquiv period hPeriod boundary tangent)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
