import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBoundaryBase4D

/-! The faithful lift defines an actual open non-null domain containing the
intrinsic bulk base. On smooth fields its condition implies the existing GHY non-null condition. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BoundedContinuousFunction
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
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedLift4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicBulkBoundaryBase4D

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
local notation "Field" => BoundedContinuousFunction Boundary Real
@[reducible] local instance : NormedAddCommGroup
    (CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) := Pi.normedAddCommGroup
@[reducible] local instance : NormedSpace Real
    (CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) := Pi.normedSpace
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

private def boundaryEvaluationRingHom (boundary : Boundary) : Field →+* Real where
  toFun field := field boundary
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem field_isUnit_of_nonzero (field : Field) (hNonzero : ∀ boundary, field boundary ≠ 0) :
    IsUnit field := by
  let inverse : Field := BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary => (field boundary)⁻¹
      continuous_toFun := field.continuous.inv₀ hNonzero }
  refine ⟨{ val := field, inv := inverse, val_inv := ?_, inv_val := ?_ }, rfl⟩
  · ext boundary
    simp [inverse, hNonzero boundary]
  · ext boundary
    simp [inverse, hNonzero boundary]

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real

def frameFreeBoundaryInducedDeterminant (current : Input) : Field :=
  candidateANormalBoundaryInducedRelativeLiftDeterminant period hPeriod
    (frameFreeBoundaryInducedLift period hPeriod metric current)

theorem frameFreeBoundaryInducedDeterminant_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryInducedDeterminant period hPeriod metric) :=
  ((candidateANormalBoundaryInducedRelativeLiftDeterminant_contDiff period hPeriod).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
      (frameFreeBoundaryInducedLift_contDiff_two period hPeriod metric)

def frameFreeBoundaryInducedDomain : Set Input :=
  {current | IsUnit (frameFreeBoundaryInducedDeterminant period hPeriod metric current)}

theorem frameFreeBoundaryInducedDomain_isOpen :
    IsOpen (frameFreeBoundaryInducedDomain period hPeriod metric) :=
  Units.isOpen.preimage (frameFreeBoundaryInducedDeterminant_contDiff_two period hPeriod metric).continuous

theorem frameFreeBoundaryInducedDeterminant_ne_zero_of_mem (current : Input)
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) (boundary : Boundary) :
    frameFreeBoundaryInducedDeterminant period hPeriod metric current boundary ≠ 0 :=
  (hCurrent.map (boundaryEvaluationRingHom period hPeriod boundary)).ne_zero

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried in
theorem frameFreeBoundaryInducedDeterminant_smooth_eq_historical (boundary : Boundary) :
    frameFreeBoundaryInducedDeterminant period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      normalGraphRelativeDeterminant period hPeriod variedMetric displacement parameter
        (orientationDoubleToThroat period hPeriod boundary) := by
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
  have hMap := (boundaryEvaluationRingHom period hPeriod boundary).map_det
    (frameFreeBoundaryInducedLift period hPeriod metric current)
  change (Matrix.det (frameFreeBoundaryInducedLift period hPeriod metric current)) boundary = _
  calc
    _ = Matrix.det (fun row column =>
        frameFreeBoundaryInducedLift period hPeriod metric current row column boundary) := hMap
    _ = Matrix.det (intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap) := by
      congr 1
      funext row column
      exact frameFreeBoundaryInducedLift_smooth_apply period hPeriod metric tensor variedMetric hVaried
        displacement parameter boundary row column
    _ = _ := (intrinsicThroatFiniteFrameLiftAt_det
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary _).trans
        (normalBoundarySmoothGraphRelativeEndomorphism_det_eq_historical
          period hPeriod variedMetric displacement parameter boundary)

include hVaried in
theorem normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedDomain period hPeriod metric) :
    NormalGraphNonNullAt period hPeriod variedMetric displacement parameter := by
  intro point
  rcases orientationDoubleToThroat_surjective period hPeriod point with ⟨boundary, hBoundary⟩
  have hDet := frameFreeBoundaryInducedDeterminant_ne_zero_of_mem period hPeriod metric _ hCurrent boundary
  rw [frameFreeBoundaryInducedDeterminant_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter boundary, hBoundary] at hDet
  exact normalGraphInducedMetricValue_injective_of_relativeDet_ne_zero
    period hPeriod variedMetric displacement parameter point hDet

/-- The already inhabited intrinsic bulk geometry supplies a non-null base for this completed domain. -/
theorem zero_mem_intrinsicFrameFreeBoundaryInducedDomain :
    (0 : FrameFreeBoundaryJointCore period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric × Real) ∈
      frameFreeBoundaryInducedDomain period hPeriod (intrinsicBulkGeometry period hPeriod).plusMetric := by
  let baseMetric := (intrinsicBulkGeometry period hPeriod).plusMetric
  change IsUnit (frameFreeBoundaryInducedDeterminant period hPeriod baseMetric 0)
  apply field_isUnit_of_nonzero period hPeriod
  intro boundary
  have hSmoothZero : smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric
      ((0 : SmoothSymmetricCovariantTwoTensor period hPeriod), (0 : SmoothNormalDisplacement period hPeriod)) = 0 :=
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric).map_zero
  have hEqual := frameFreeBoundaryInducedDeterminant_smooth_eq_historical
    period hPeriod baseMetric 0 baseMetric (by simp) 0 0 boundary
  rw [hSmoothZero] at hEqual
  change frameFreeBoundaryInducedDeterminant period hPeriod baseMetric 0 boundary = _ at hEqual
  rw [hEqual]
  exact normalGraphRelativeDeterminant_ne_zero period hPeriod baseMetric 0 0
    (intrinsicBulkNonNullDomain_zero_mem period hPeriod 0) (orientationDoubleToThroat period hPeriod boundary)

theorem intrinsicFrameFreeBoundaryInducedDomain_mem_nhds_zero :
    frameFreeBoundaryInducedDomain period hPeriod (intrinsicBulkGeometry period hPeriod).plusMetric ∈
      𝓝 (0 : FrameFreeBoundaryJointCore period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric × Real) :=
  (frameFreeBoundaryInducedDomain_isOpen period hPeriod _).mem_nhds
    (zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
