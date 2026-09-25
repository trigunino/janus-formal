import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D

/-! The actual squared projected normal, obtained by the same C² metric contraction. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquare4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
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
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

private theorem finiteBilinearSquare {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module Real E] [TopologicalSpace E]
    (pairing : E →L[Real] E →L[Real] Real) (vectors : I → E) (coefficients : I → Real) :
    (∑ first : I, ∑ second : I,
      coefficients first * pairing (vectors first) (vectors second) * coefficients second) =
        pairing (∑ index : I, coefficients index • vectors index)
          (∑ index : I, coefficients index • vectors index) := by
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

def frameFreeBoundaryNormalSquare (current : Input) : Field :=
  ∑ first : Index, ∑ second : Index,
    frameFreeBoundaryProjectedNormalEvaluation period hPeriod metric first current *
      frameFreeBoundaryActualMetricEvaluation period hPeriod metric first second current *
        frameFreeBoundaryProjectedNormalEvaluation period hPeriod metric second current

theorem frameFreeBoundaryNormalSquare_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryNormalSquare period hPeriod metric)
      (frameFreeBoundaryInducedDomain period hPeriod metric) := by
  unfold frameFreeBoundaryNormalSquare
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ =>
    ((frameFreeBoundaryProjectedNormalEvaluation_contDiffOn_two period hPeriod metric first).mul
      (frameFreeBoundaryActualMetricEvaluation_contDiff_two period hPeriod metric first second).contDiffOn).mul
        (frameFreeBoundaryProjectedNormalEvaluation_contDiffOn_two period hPeriod metric second)

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
local notation "current" => (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)

include hVaried in
theorem frameFreeBoundaryNormalSquare_smooth (boundary : Boundary) :
    frameFreeBoundaryNormalSquare period hPeriod metric current boundary =
      variedMetric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
        (frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary)
        (frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary) := by
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  have hSquare := finiteBilinearSquare (I := Index)
    (E := TangentSpace coverModelWithCorners point)
    (variedMetric.tensor.tensor point)
    (fun index : Index => (finiteSmoothTangentFrame period hPeriod).vectorAt point index)
    (fun index => frameFreeBoundaryProjectedNormalEvaluation period hPeriod metric index current boundary)
  unfold frameFreeBoundaryNormalSquare frameFreeBoundaryProjectedNormalVector
  simp only [BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  simp_rw [frameFreeBoundaryActualMetricEvaluation_smooth period hPeriod metric tensor displacement parameter boundary,
    ← hVaried]
  exact hSquare

theorem frameFreeBoundaryNormalSquare_smooth_eq_historical
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) (boundary : Boundary) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
      period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent
    let normal := normalGraphMetricNormal period hPeriod variedMetric displacement parameter hNonNull
      (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter boundary)
    frameFreeBoundaryNormalSquare period hPeriod metric current boundary =
      variedMetric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) normal normal := by
  dsimp only
  rw [frameFreeBoundaryNormalSquare_smooth period hPeriod metric tensor variedMetric hVaried displacement parameter boundary,
    frameFreeBoundaryProjectedNormalVector_smooth period hPeriod metric tensor displacement parameter variedMetric hVaried hCurrent]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquare4D
