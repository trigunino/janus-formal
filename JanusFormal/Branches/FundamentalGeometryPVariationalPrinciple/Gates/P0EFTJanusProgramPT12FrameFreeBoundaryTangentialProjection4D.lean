import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D

/-! The faithful induced inverse raises genuine tangent covectors. Its finite
coefficient operation is C² jointly in the geometry and covector readings. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
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
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D

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
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "Readings" => Index → Field
local notation "MatrixField" => CandidateANormalBoundaryInducedMetricMatrixField period hPeriod
@[reducible] local instance : NormedAddCommGroup MatrixField := Pi.normedAddCommGroup
@[reducible] local instance : NormedSpace Real MatrixField := Pi.normedSpace

def frameFreeBoundaryTangentialProjectionEvaluation (state : Input × Readings) : Readings :=
  fun row => ∑ middle : Index,
    frameFreeBoundaryInducedLiftInverse period hPeriod metric state.1 row middle *
      ∑ column : Index, normalBoundaryReferenceDualCoefficientMatrix period hPeriod middle column *
        state.2 column

theorem frameFreeBoundaryTangentialProjectionEvaluation_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryTangentialProjectionEvaluation period hPeriod metric)
      (frameFreeBoundaryInducedDomain period hPeriod metric ×ˢ (Set.univ : Set Readings)) := by
  have hInverse : ContDiffOn Real 2
      (fun state : Input × Readings => frameFreeBoundaryInducedLiftInverse period hPeriod metric state.1)
      (frameFreeBoundaryInducedDomain period hPeriod metric ×ˢ (Set.univ : Set Readings)) :=
    (frameFreeBoundaryInducedLiftInverse_contDiffOn_two period hPeriod metric).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  rw [contDiffOn_pi]
  intro row
  unfold frameFreeBoundaryTangentialProjectionEvaluation
  exact ContDiffOn.sum fun middle _ =>
    (contDiffOn_pi.mp (contDiffOn_pi.mp hInverse row) middle).mul
      (ContDiffOn.sum fun column _ => contDiffOn_const.mul
        (contDiff_pi.mp contDiff_snd column).contDiffOn)

/-- Pointwise synthesis of the same finite operation on an actual covector. -/
def frameFreeBoundaryInducedInverseMusicalAt (current : Input) (boundary : Boundary)
    (covector : TangentSpace throatCoverModelWithCorners boundary →L[Real] Real) :
    TangentSpace throatCoverModelWithCorners boundary :=
  intrinsicThroatFiniteFrameSynthesisAt
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
    (Matrix.mulVec (Matrix.of fun row column => frameFreeBoundaryInducedLiftInverse period hPeriod metric current row column boundary)
      (Matrix.mulVec (Matrix.of fun row column => normalBoundaryReferenceDualCoefficientMatrix period hPeriod row column boundary)
        (fun index => covector ((throatFrame).vectorAt boundary index))))

theorem frameFreeBoundaryInducedInverseMusicalAt_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedDomain period hPeriod metric)
    (boundary : Boundary)
    (covector : TangentSpace throatCoverModelWithCorners boundary →L[Real] Real) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric displacement parameter boundary
      (frameFreeBoundaryInducedInverseMusicalAt period hPeriod metric
        (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
        boundary covector) = covector := by
  apply (intrinsicThroatInverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) boundary).injective
  change normalBoundarySmoothGraphRelativeEndomorphism period hPeriod variedMetric displacement parameter boundary
    (frameFreeBoundaryInducedInverseMusicalAt period hPeriod metric _ boundary covector) = _
  unfold frameFreeBoundaryInducedInverseMusicalAt
  rw [frameFreeBoundaryInducedLiftInverse_smooth_synthesis
    period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent]
  have hDual : (Matrix.of fun row column => normalBoundaryReferenceDualCoefficientMatrix period hPeriod row column boundary) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        (intrinsicThroatFiniteFrameOperator
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary).inverse.toLinearMap := by
    ext row column
    exact normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse
      period hPeriod row column boundary
  rw [hDual, intrinsicThroatFiniteFrameEndomorphismMatrixAt_inverseOperator_mulVec]
  exact congrArg (fun linear => linear
    (intrinsicThroatInverseMusical (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) boundary covector))
      (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
