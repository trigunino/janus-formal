import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquareBase4D

/-! Positive normalization of the actual projected normal near the inhabited
intrinsic base. The scalar root and inverse are the existing Banach-algebra engines. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryUnitNormal4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D
open P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
open P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
open P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquare4D
open P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquareBase4D

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
local notation "baseMetric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "square" => frameFreeBoundaryNormalSquare period hPeriod baseMetric
local notation "rootBranch" => candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod

def frameFreeBoundaryUnitNormalDomain : Set Input :=
  frameFreeBoundaryInducedDomain period hPeriod baseMetric ∩
    square ⁻¹' frameFreeBoundaryPositiveRootTarget period hPeriod

theorem frameFreeBoundaryUnitNormalDomain_isOpen :
    IsOpen (frameFreeBoundaryUnitNormalDomain period hPeriod) :=
  (frameFreeBoundaryNormalSquare_contDiffOn_two period hPeriod baseMetric).continuousOn.isOpen_inter_preimage
    (frameFreeBoundaryInducedDomain_isOpen period hPeriod baseMetric)
    (frameFreeBoundaryPositiveRootTarget_isOpen period hPeriod)

theorem zero_joint_mem_frameFreeBoundaryUnitNormalDomain (parameter : Real) :
    ((0, parameter) : Input) ∈ frameFreeBoundaryUnitNormalDomain period hPeriod := by
  refine ⟨zero_joint_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod parameter, ?_⟩
  change square (0, parameter) ∈ frameFreeBoundaryPositiveRootTarget period hPeriod
  rw [frameFreeBoundaryNormalSquare_zero_joint]
  exact one_mem_frameFreeBoundaryPositiveRootTarget period hPeriod

theorem frameFreeBoundaryUnitNormalDomain_mem_nhds_zero_one :
    frameFreeBoundaryUnitNormalDomain period hPeriod ∈ 𝓝 ((0, 1) : Input) :=
  (frameFreeBoundaryUnitNormalDomain_isOpen period hPeriod).mem_nhds
    (zero_joint_mem_frameFreeBoundaryUnitNormalDomain period hPeriod 1)

def frameFreeBoundaryNormalMagnitude (current : Input) : Field := rootBranch (square current)

theorem frameFreeBoundaryNormalMagnitude_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryNormalMagnitude period hPeriod)
      (frameFreeBoundaryUnitNormalDomain period hPeriod) :=
  (candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn period hPeriod).comp
    ((frameFreeBoundaryNormalSquare_contDiffOn_two period hPeriod baseMetric).mono Set.inter_subset_left)
    (fun _ h => h.2.1)

theorem frameFreeBoundaryNormalMagnitude_pos {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    0 < frameFreeBoundaryNormalMagnitude period hPeriod current boundary :=
  frameFreeBoundaryRootBranch_pos period hPeriod hCurrent.2 boundary

theorem frameFreeBoundaryNormalMagnitude_sq {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    (frameFreeBoundaryNormalMagnitude period hPeriod current boundary) ^ 2 = square current boundary := by
  have h := congrArg (fun field : Field => field boundary)
    (candidateANormalBoundaryScalarFieldLocalRootBranch_square period hPeriod hCurrent.2.1)
  simpa only [frameFreeBoundaryNormalMagnitude, candidateANormalBoundaryScalarFieldSquare,
    BoundedContinuousFunction.mul_apply, pow_two] using h

theorem frameFreeBoundaryNormalMagnitude_apply {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    frameFreeBoundaryNormalMagnitude period hPeriod current boundary = Real.sqrt |square current boundary| := by
  rw [← frameFreeBoundaryNormalMagnitude_sq period hPeriod hCurrent boundary,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (frameFreeBoundaryNormalMagnitude_pos period hPeriod hCurrent boundary)]

theorem frameFreeBoundaryNormalMagnitude_isUnit {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryUnitNormalDomain period hPeriod) :
    IsUnit (frameFreeBoundaryNormalMagnitude period hPeriod current) := by
  have hBall : rootBranch (square current) ∈ Metric.ball 1 1 := hCurrent.2.2
  have hNorm : ‖1 - frameFreeBoundaryNormalMagnitude period hPeriod current‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, frameFreeBoundaryNormalMagnitude] using hBall
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hNorm

def frameFreeBoundaryNormalMagnitudeInverse (current : Input) : Field :=
  Ring.inverse (frameFreeBoundaryNormalMagnitude period hPeriod current)

theorem frameFreeBoundaryNormalMagnitudeInverse_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryNormalMagnitudeInverse period hPeriod)
      (frameFreeBoundaryUnitNormalDomain period hPeriod) := by
  intro current hCurrent
  have hUnit := frameFreeBoundaryNormalMagnitude_isUnit period hPeriod hCurrent
  have hInverse : ContDiffAt Real 2 Ring.inverse (frameFreeBoundaryNormalMagnitude period hPeriod current) := by
    simpa using (contDiffAt_ringInverse Real hUnit.unit : ContDiffAt Real 2 Ring.inverse (hUnit.unit : Field))
  exact hInverse.comp_contDiffWithinAt current
    (frameFreeBoundaryNormalMagnitude_contDiffOn_two period hPeriod current hCurrent)

theorem frameFreeBoundaryNormalMagnitudeInverse_apply {current : Input}
    (hCurrent : current ∈ frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    frameFreeBoundaryNormalMagnitudeInverse period hPeriod current boundary =
      (Real.sqrt |square current boundary|)⁻¹ := by
  have hCancel := congrArg (fun field : Field => field boundary)
    (Ring.inverse_mul_cancel _ (frameFreeBoundaryNormalMagnitude_isUnit period hPeriod hCurrent))
  change frameFreeBoundaryNormalMagnitudeInverse period hPeriod current boundary *
    frameFreeBoundaryNormalMagnitude period hPeriod current boundary = 1 at hCancel
  rw [← frameFreeBoundaryNormalMagnitude_apply period hPeriod hCurrent boundary]
  apply mul_right_cancel₀ (ne_of_gt (frameFreeBoundaryNormalMagnitude_pos period hPeriod hCurrent boundary))
  rw [hCancel, inv_mul_cancel₀ (ne_of_gt (frameFreeBoundaryNormalMagnitude_pos period hPeriod hCurrent boundary))]

def frameFreeBoundaryUnitNormalEvaluation (upper : Index) (current : Input) : Field :=
  frameFreeBoundaryNormalMagnitudeInverse period hPeriod current *
    frameFreeBoundaryProjectedNormalEvaluation period hPeriod baseMetric upper current

theorem frameFreeBoundaryUnitNormalEvaluation_contDiffOn_two (upper : Index) :
    ContDiffOn Real 2 (frameFreeBoundaryUnitNormalEvaluation period hPeriod upper)
      (frameFreeBoundaryUnitNormalDomain period hPeriod) :=
  (frameFreeBoundaryNormalMagnitudeInverse_contDiffOn_two period hPeriod).mul
    ((frameFreeBoundaryProjectedNormalEvaluation_contDiffOn_two period hPeriod baseMetric upper).mono Set.inter_subset_left)

def frameFreeBoundaryUnitNormalVector (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    TangentSpace coverModelWithCorners (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :=
  ∑ upper : Index, frameFreeBoundaryUnitNormalEvaluation period hPeriod upper
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary •
      (finiteSmoothTangentFrame period hPeriod).vectorAt
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) upper

private theorem unitNormalVector_eq_scaled
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryUnitNormalVector period hPeriod tensor displacement parameter boundary =
      frameFreeBoundaryNormalMagnitudeInverse period hPeriod
          (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary •
        frameFreeBoundaryProjectedNormalVector period hPeriod baseMetric tensor displacement parameter boundary := by
  unfold frameFreeBoundaryUnitNormalVector frameFreeBoundaryUnitNormalEvaluation frameFreeBoundaryProjectedNormalVector
  simp only [BoundedContinuousFunction.mul_apply, Finset.smul_sum, smul_smul]

private theorem normalSquare_smooth_eq_class
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = (baseMetric).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    square (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
      normalGraphMetricNormalSquare period hPeriod variedMetric displacement parameter
        (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor variedMetric hVaried
          displacement parameter hCurrent.1) (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter boundary) := by
  simpa only [normalGraphMetricNormalSquare, normalGraphCanonicalNormalClass,
    normalGraphMetricNormalFromClass_mk, normalGraphOrientationDouble] using
    frameFreeBoundaryNormalSquare_smooth_eq_historical period hPeriod baseMetric tensor variedMetric hVaried
      displacement parameter hCurrent.1 boundary

theorem frameFreeBoundaryUnitNormalVector_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = (baseMetric).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryUnitNormalDomain period hPeriod) (boundary : Boundary) :
    frameFreeBoundaryUnitNormalVector period hPeriod tensor displacement parameter boundary =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric displacement parameter
        (normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor variedMetric hVaried
          displacement parameter hCurrent.1) boundary := by
  have hScalar := (frameFreeBoundaryNormalMagnitudeInverse_apply period hPeriod hCurrent boundary).trans
    (congrArg (fun value : Real => (Real.sqrt |value|)⁻¹)
      (normalSquare_smooth_eq_class period hPeriod tensor variedMetric hVaried displacement parameter hCurrent boundary))
  have hNormal := frameFreeBoundaryProjectedNormalVector_smooth period hPeriod baseMetric
    tensor displacement parameter variedMetric hVaried hCurrent.1 boundary
  have hProduct := congrArg₂
    (fun scalar : Real => fun vector : TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) => scalar • vector)
    hScalar hNormal
  have hResult := (unitNormalVector_eq_scaled period hPeriod tensor displacement parameter boundary).trans hProduct
  simpa only [normalGraphCanonicalMetricUnitNormal, normalGraphMetricUnitNormal,
    normalGraphCanonicalNormalClass, normalGraphMetricNormalFromClass_mk] using hResult

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryUnitNormal4D
