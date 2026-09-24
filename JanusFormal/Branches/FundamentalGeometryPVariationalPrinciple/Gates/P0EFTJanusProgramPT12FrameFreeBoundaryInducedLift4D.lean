import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D

/-! Faithful identity extension of the redundant induced Gram matrix, with
exact agreement to the existing intrinsic relative endomorphism on smooth data. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedLift4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
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
local instance : ChartedSpace ThroatCoverModel (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "Index" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "MatrixField" => CandidateANormalBoundaryInducedMetricMatrixField period hPeriod
@[reducible] local instance : NormedAddCommGroup MatrixField := Pi.normedAddCommGroup
@[reducible] local instance : NormedSpace Real MatrixField := Pi.normedSpace

def frameFreeBoundaryInducedLift (current : Input) : MatrixField := fun row column =>
  (1 : MatrixField) row column - normalBoundaryReferenceProjectorMatrix period hPeriod row column +
    ∑ middle : Index, normalBoundaryReferenceDualCoefficientMatrix period hPeriod row middle *
      frameFreeBoundaryInducedMetricEvaluation period hPeriod metric current middle column

theorem frameFreeBoundaryInducedLift_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryInducedLift period hPeriod metric) := by
  have hInduced := frameFreeBoundaryInducedMetricEvaluation_contDiff_two period hPeriod metric
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  unfold frameFreeBoundaryInducedLift
  exact (contDiff_const.sub contDiff_const).add (ContDiff.sum fun middle _ =>
    contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp hInduced middle) column))

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried

theorem frameFreeBoundaryInducedMetricEvaluation_smooth_eq_musical
    (boundary : Boundary) (row column : Index) :
    frameFreeBoundaryInducedMetricEvaluation period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
      row column boundary =
      normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric displacement parameter boundary
        ((throatFrame).vectorAt boundary row) ((throatFrame).vectorAt boundary column) := by
  have hCompleted := frameFreeBoundaryInducedMetricEvaluation_smooth
    period hPeriod metric tensor displacement parameter boundary row column
  dsimp only at hCompleted
  rw [← hVaried] at hCompleted
  rw [normalBoundarySmoothGraphInducedMetricMusical_apply,
    normalBoundaryOrientationTangentEquiv_apply, normalBoundaryOrientationTangentEquiv_apply,
    normalGraphInducedMetricValue_apply]
  rw [← normalGraphOrientationDouble_mfderiv_eq_comp period hPeriod displacement parameter boundary,
    ← normalGraphOrientationDouble_mfderiv_eq_comp period hPeriod displacement parameter boundary]
  simpa only [normalGraphOrientationDouble] using hCompleted

theorem frameFreeBoundaryInducedMetricEvaluation_smooth_eq_encoding
    (boundary : Boundary) (row column : Index) :
    frameFreeBoundaryInducedMetricEvaluation period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
      row column boundary =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        ((intrinsicThroatFiniteFrameOperator (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          throatFrame boundary).toLinearMap.comp
          (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
            variedMetric displacement parameter boundary).toLinearMap) row column := by
  rw [frameFreeBoundaryInducedMetricEvaluation_smooth_eq_musical
    period hPeriod metric tensor variedMetric hVaried displacement parameter boundary row column]
  unfold normalBoundarySmoothGraphRelativeEndomorphism
  calc
    _ = normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric displacement parameter boundary
        ((throatFrame).vectorAt boundary column) ((throatFrame).vectorAt boundary row) := by
      rw [normalBoundarySmoothGraphInducedMetricMusical_apply, normalBoundarySmoothGraphInducedMetricMusical_apply]
      exact normalGraphInducedMetricValue_symmetric period hPeriod variedMetric displacement parameter _ _ _
    _ = _ := (intrinsicThroatFiniteFrameEndomorphismMatrixAt_relativeMusical_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
      (normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric displacement parameter boundary)
      row column).symm

theorem frameFreeBoundaryInducedLift_smooth_apply
    (boundary : Boundary) (row column : Index) :
    frameFreeBoundaryInducedLift period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
      row column boundary =
      intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap row column := by
  classical
  let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter boundary
  have hDual : (fun first second => normalBoundaryReferenceDualCoefficientMatrix
      period hPeriod first second boundary) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        (intrinsicThroatFiniteFrameOperator (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          throatFrame boundary).inverse.toLinearMap := by
    ext first second
    exact normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse period hPeriod first second boundary
  have hMetric : (fun first second => frameFreeBoundaryInducedMetricEvaluation period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
      first second boundary) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        ((intrinsicThroatFiniteFrameOperator (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          throatFrame boundary).toLinearMap.comp relative.toLinearMap) := by
    ext first second
    exact frameFreeBoundaryInducedMetricEvaluation_smooth_eq_encoding
      period hPeriod metric tensor variedMetric hVaried displacement parameter boundary first second
  have hProduct := intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary relative.toLinearMap
  rw [← hDual, ← hMetric] at hProduct
  have hEntry := congrArg (fun matrix : Matrix Index Index Real => matrix row column) hProduct
  change (∑ middle : Index, normalBoundaryReferenceDualCoefficientMatrix period hPeriod row middle boundary *
    frameFreeBoundaryInducedMetricEvaluation period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
      middle column boundary) = _ at hEntry
  unfold frameFreeBoundaryInducedLift intrinsicThroatFiniteFrameLiftAt redundantFiniteFrameLift
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sum_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  rw [normalBoundaryReferenceProjectorMatrix_apply_eq_finiteFrameProjector, hEntry]
  unfold intrinsicThroatFiniteFrameProjectorMatrixAt intrinsicThroatFiniteFrameEndomorphismMatrixAt
  dsimp only [relative]
  split_ifs <;> simp

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedLift4D
