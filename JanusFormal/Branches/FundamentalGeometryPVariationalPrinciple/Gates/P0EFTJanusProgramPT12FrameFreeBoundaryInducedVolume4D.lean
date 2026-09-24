import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D

/-! Actual induced volume density near the inhabited intrinsic base. The existing
scalar root engine is restricted to its positive branch, with exact sqrt/physical agreement. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D
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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D

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
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "baseMetric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real
local notation "determinant" => frameFreeBoundaryInducedDeterminant period hPeriod baseMetric
local notation "rootBranch" => candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod

def frameFreeBoundaryPositiveRootTarget : Set Field :=
  candidateANormalBoundaryScalarFieldLocalRootTarget period hPeriod ∩
    rootBranch ⁻¹' Metric.ball 1 1

theorem frameFreeBoundaryPositiveRootTarget_isOpen :
    IsOpen (frameFreeBoundaryPositiveRootTarget period hPeriod) :=
  (candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn period hPeriod).continuousOn.isOpen_inter_preimage
    (candidateANormalBoundaryScalarFieldLocalRootTarget_isOpen period hPeriod) Metric.isOpen_ball

theorem one_mem_frameFreeBoundaryPositiveRootTarget :
    (1 : Field) ∈ frameFreeBoundaryPositiveRootTarget period hPeriod :=
  ⟨candidateANormalBoundaryScalarFieldOne_mem_localRootTarget period hPeriod, by simp⟩

theorem frameFreeBoundaryRootBranch_pos {field : Field}
    (hField : field ∈ frameFreeBoundaryPositiveRootTarget period hPeriod) (boundary : Boundary) :
    0 < rootBranch field boundary := by
  have hBall : rootBranch field ∈ Metric.ball 1 1 := hField.2
  have hNorm : ‖rootBranch field - 1‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hBall
  have hPoint := lt_of_le_of_lt ((rootBranch field - 1).norm_coe_le_norm boundary) hNorm
  change |rootBranch field boundary - 1| < 1 at hPoint
  linarith [(abs_lt.mp hPoint).1]

def frameFreeBoundaryInducedDeterminantRatio (current : Input) : Field :=
  determinant current * Ring.inverse (determinant 0)

theorem frameFreeBoundaryInducedDeterminantRatio_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryInducedDeterminantRatio period hPeriod) :=
  (frameFreeBoundaryInducedDeterminant_contDiff_two period hPeriod baseMetric).mul contDiff_const

@[simp] theorem frameFreeBoundaryInducedDeterminantRatio_zero :
    frameFreeBoundaryInducedDeterminantRatio period hPeriod 0 = 1 :=
  Ring.mul_inverse_cancel _ (zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod)

def frameFreeBoundaryInducedVolumeDomain : Set Input :=
  frameFreeBoundaryInducedDomain period hPeriod baseMetric ∩
    frameFreeBoundaryInducedDeterminantRatio period hPeriod ⁻¹'
      frameFreeBoundaryPositiveRootTarget period hPeriod

theorem frameFreeBoundaryInducedVolumeDomain_isOpen :
    IsOpen (frameFreeBoundaryInducedVolumeDomain period hPeriod) :=
  (frameFreeBoundaryInducedDomain_isOpen period hPeriod baseMetric).inter
    ((frameFreeBoundaryPositiveRootTarget_isOpen period hPeriod).preimage
      (frameFreeBoundaryInducedDeterminantRatio_contDiff_two period hPeriod).continuous)

theorem zero_mem_frameFreeBoundaryInducedVolumeDomain :
    (0 : Input) ∈ frameFreeBoundaryInducedVolumeDomain period hPeriod := by
  refine ⟨zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod, ?_⟩
  change frameFreeBoundaryInducedDeterminantRatio period hPeriod 0 ∈
    frameFreeBoundaryPositiveRootTarget period hPeriod
  rw [frameFreeBoundaryInducedDeterminantRatio_zero]
  exact one_mem_frameFreeBoundaryPositiveRootTarget period hPeriod

def frameFreeBoundaryInducedBaseVolume : Field :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary => Real.sqrt |determinant 0 boundary|
      continuous_toFun := (determinant 0).continuous.abs.sqrt }

def frameFreeBoundaryInducedVolume (current : Input) : Field :=
  frameFreeBoundaryInducedBaseVolume period hPeriod *
    rootBranch (frameFreeBoundaryInducedDeterminantRatio period hPeriod current)

theorem frameFreeBoundaryInducedVolume_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryInducedVolume period hPeriod)
      (frameFreeBoundaryInducedVolumeDomain period hPeriod) :=
  contDiffOn_const.mul ((candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn period hPeriod).comp
    (frameFreeBoundaryInducedDeterminantRatio_contDiff_two period hPeriod).contDiffOn (fun _ hCurrent => hCurrent.2.1))

@[simp] theorem frameFreeBoundaryInducedVolume_zero :
    frameFreeBoundaryInducedVolume period hPeriod 0 = frameFreeBoundaryInducedBaseVolume period hPeriod := by
  unfold frameFreeBoundaryInducedVolume
  rw [frameFreeBoundaryInducedDeterminantRatio_zero, candidateANormalBoundaryScalarFieldLocalRootBranch_at_one, mul_one]

theorem frameFreeBoundaryInducedVolume_pos {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryInducedVolumeDomain period hPeriod) (boundary : Boundary) :
    0 < frameFreeBoundaryInducedVolume period hPeriod current boundary := by
  apply mul_pos
  · exact Real.sqrt_pos.2 (abs_pos.mpr (frameFreeBoundaryInducedDeterminant_ne_zero_of_mem
      period hPeriod baseMetric 0 (zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod) boundary))
  · exact frameFreeBoundaryRootBranch_pos period hPeriod hCurrent.2 boundary

theorem frameFreeBoundaryInducedVolume_sq {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryInducedVolumeDomain period hPeriod) (boundary : Boundary) :
    (frameFreeBoundaryInducedVolume period hPeriod current boundary) ^ 2 = |determinant current boundary| := by
  let root := rootBranch (frameFreeBoundaryInducedDeterminantRatio period hPeriod current) boundary
  have hSquare := congrArg (fun field : Field => field boundary)
    (candidateANormalBoundaryScalarFieldLocalRootBranch_square period hPeriod hCurrent.2.1)
  change root * root = frameFreeBoundaryInducedDeterminantRatio period hPeriod current boundary at hSquare
  have hCancel : frameFreeBoundaryInducedDeterminantRatio period hPeriod current * determinant 0 =
      determinant current :=
    Ring.inverse_mul_cancel_right _ _ (zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod)
  have hDet := congrArg (fun field : Field => field boundary) hCancel
  change frameFreeBoundaryInducedDeterminantRatio period hPeriod current boundary * determinant 0 boundary =
    determinant current boundary at hDet
  have hValue : root ^ 2 * determinant 0 boundary = determinant current boundary := by
    simpa only [pow_two, hSquare] using hDet
  change (Real.sqrt |determinant 0 boundary| * root) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _), ← hValue, abs_mul, abs_of_nonneg (sq_nonneg root)]
  ring

theorem frameFreeBoundaryInducedVolume_apply {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryInducedVolumeDomain period hPeriod) (boundary : Boundary) :
    frameFreeBoundaryInducedVolume period hPeriod current boundary = Real.sqrt |determinant current boundary| := by
  rw [← frameFreeBoundaryInducedVolume_sq period hPeriod hCurrent boundary,
    Real.sqrt_sq_eq_abs, abs_of_pos (frameFreeBoundaryInducedVolume_pos period hPeriod hCurrent boundary)]

theorem frameFreeBoundaryInducedVolume_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = (baseMetric).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedVolumeDomain period hPeriod) (boundary : Boundary) :
    frameFreeBoundaryInducedVolume period hPeriod
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
      normalGraphRelativeVolumeDensity period hPeriod variedMetric displacement parameter
        (orientationDoubleToThroat period hPeriod boundary) := by
  rw [frameFreeBoundaryInducedVolume_apply period hPeriod hCurrent boundary,
    frameFreeBoundaryInducedDeterminant_smooth_eq_historical period hPeriod baseMetric tensor variedMetric hVaried
      displacement parameter boundary]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D
