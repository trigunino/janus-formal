import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquare4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D

/-! At the intrinsic zero-displacement background the projected latitude normal
has square one, at every fixed parameter, including the physical parameter one. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquareBase4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
private theorem transport_mpr_heq {α β : Sort u} (h : α = β) (value : β) :
    HEq (h.mpr value) value := by
  cases h
  rfl
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkBoundaryBase4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
open P0EFTJanusProgramPT12FrameFreeBoundaryVerticalTangentialPairing4D
open P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
open P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquare4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace CoverModel (MappingTorusCover (reflectedSphereData period hPeriod)) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (MappingTorusCover (reflectedSphereData period hPeriod)) :=
  reflectedSphereCover_isManifold period hPeriod
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
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real

private theorem latitudeLift_zero (base : CanonicalLatitudeBase) :
    canonicalLatitudeNormalLift period hPeriod (base, 0) =
      (⟨fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (fixedEquatorData period hPeriod) (canonicalLatitudeAnchor period hPeriod base)),
        canonicalQuotientLatitudeNormal period hPeriod (canonicalLatitudeAnchor period hPeriod base)⟩ :
        TangentBundle coverModelWithCorners (Q period hPeriod)) := by
  let anchor := canonicalLatitudeAnchor period hPeriod base
  have hCover : (⟨normalLatitudeCover period hPeriod anchor 0,
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (normalLatitudeCover period hPeriod anchor) 0 1⟩ :
      TangentBundle coverModelWithCorners (MappingTorusCover (reflectedSphereData period hPeriod))) =
      ⟨fixedThroatCoverInclusion period hPeriod anchor, coverLatitudeNormalVector period hPeriod anchor⟩ := by
    apply Bundle.TotalSpace.ext
    · exact normalLatitudeCover_zero period hPeriod anchor
    · exact (coverLatitudeNormalVector_heq_rawDerivative period hPeriod anchor).symm
  have hProjected := congrArg (tangentMap coverModelWithCorners coverModelWithCorners
    (mappingTorusMk (reflectedSphereData period hPeriod))) hCover
  have hCanonical : (tangentMap coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (reflectedSphereData period hPeriod))
        ⟨fixedThroatCoverInclusion period hPeriod anchor, coverLatitudeNormalVector period hPeriod anchor⟩) =
      (⟨fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor),
        canonicalQuotientLatitudeNormal period hPeriod anchor⟩ :
          TangentBundle coverModelWithCorners (Q period hPeriod)) := by
    apply Bundle.TotalSpace.ext
    · exact (fixedThroatQuotientInclusion_mk period hPeriod anchor).symm
    · symm
      unfold canonicalQuotientLatitudeNormal
      dsimp only [id]
      exact transport_mpr_heq _ _
  unfold canonicalLatitudeNormalLift quotientNormalLatitude
  rw [canonicalLatitudeNormalVector_eq_projectionDerivative]
  simpa only [tangentMap, anchor] using hProjected.trans hCanonical

private theorem graphLatitude_zero_total (parameter : Real)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    (⟨normalGraphOrientationDouble period hPeriod 0
        (mappingTorusMk (orientationDoubleData period hPeriod) point, parameter),
      normalGraphCanonicalLatitudeVector period hPeriod 0 parameter
        (mappingTorusMk (orientationDoubleData period hPeriod) point)⟩ :
        TangentBundle coverModelWithCorners (Q period hPeriod)) =
      ⟨fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (fixedEquatorData period hPeriod) (orientationDoubleCoverHomeomorph period hPeriod point)),
        canonicalQuotientLatitudeNormal period hPeriod (orientationDoubleCoverHomeomorph period hPeriod point)⟩ := by
  rw [normalGraphCanonicalLatitudeVector_total, normalGraphCanonicalLatitudeLift_mk,
    normalGraphCanonicalLatitudeLiftCover_eq_canonical]
  simp only [normalGraphCanonicalLatitudeParameterCover, normalGraphCoordinate,
    normalCoordinateLift_zero_displacement, mul_zero, Real.arctan_zero]
  have h := latitudeLift_zero period hPeriod (normalGraphCanonicalLatitudeBaseCover period hPeriod point)
  rw [canonicalLatitudeAnchor_baseCover] at h
  exact h

theorem intrinsicGraphLatitude_zero_square (parameter : Real) (boundary : Boundary) :
    (baseMetric).tensor.tensor (normalGraphOrientationDouble period hPeriod 0 (boundary, parameter))
      (normalGraphCanonicalLatitudeVector period hPeriod 0 parameter boundary)
      (normalGraphCanonicalLatitudeVector period hPeriod 0 parameter boundary) = 1 := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have h := congrArg (fun lifted : TangentBundle coverModelWithCorners (Q period hPeriod) =>
      (baseMetric).tensor.tensor lifted.1 lifted.2 lifted.2)
    (graphLatitude_zero_total period hPeriod parameter point)
  rw [h, intrinsicBulkGeometry_plusMetric_tensor]
  exact canonicalQuotientLatitudeNormal_square period hPeriod _

theorem intrinsicGraphLatitude_zero_covector (parameter : Real) (boundary : Boundary) :
    normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod baseMetric 0 parameter boundary = 0 := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hVector := eq_of_heq (Bundle.TotalSpace.ext_iff.mp
    (graphLatitude_zero_total period hPeriod parameter point)).2
  dsimp only at hVector
  have hGraph : normalGraph period hPeriod 0 parameter = fixedThroatQuotientInclusion period hPeriod := by
    rw [normalGraph_zero_displacement_eq_zero]
    funext source
    exact normalGraph_zero period hPeriod 0 source
  apply ContinuousLinearMap.ext
  intro tangent
  unfold normalBoundarySmoothGraphVerticalTangentialCovector
  simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply]
  erw [normalGraphOrientationDouble_mfderiv_eq_comp, hVector]
  simp only [normalGraphOrientationDouble, orientationDoubleToThroat_mk]
  rw [hGraph, intrinsicBulkGeometry_plusMetric_tensor]
  exact canonicalQuotientLatitudeNormal_orthogonal period hPeriod _ _

private theorem basePairing_zero (parameter : Real) (index : NormalBoundaryTangentIndex period hPeriod) :
    frameFreeBoundaryVerticalTangentialPairingEvaluation period hPeriod baseMetric index (0, parameter) = 0 := by
  ext boundary
  have h := frameFreeBoundaryVerticalTangentialPairingEvaluation_smooth period hPeriod baseMetric
    0 baseMetric (by simp) 0 parameter boundary index
  have hZero : smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric
      ((0 : SmoothSymmetricCovariantTwoTensor period hPeriod), (0 : SmoothNormalDisplacement period hPeriod)) = 0 :=
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric).map_zero
  rw [hZero, intrinsicGraphLatitude_zero_covector, _root_.zero_apply] at h
  exact h

theorem frameFreeBoundaryNormalSquare_zero_joint (parameter : Real) :
    frameFreeBoundaryNormalSquare period hPeriod baseMetric (0, parameter) = 1 := by
  have hZero : smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric
      ((0 : SmoothSymmetricCovariantTwoTensor period hPeriod), (0 : SmoothNormalDisplacement period hPeriod)) = 0 :=
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric).map_zero
  have hProjection : frameFreeBoundaryTangentialCoefficientEvaluation period hPeriod baseMetric (0, parameter) = 0 := by
    funext index
    simp [frameFreeBoundaryTangentialCoefficientEvaluation, frameFreeBoundaryTangentialProjectionEvaluation,
      basePairing_zero]
  have hNormal (boundary : Boundary) : frameFreeBoundaryProjectedNormalVector period hPeriod baseMetric
      0 0 parameter boundary = normalGraphCanonicalLatitudeVector period hPeriod 0 parameter boundary := by
    unfold frameFreeBoundaryProjectedNormalVector frameFreeBoundaryProjectedNormalEvaluation
    rw [hZero]
    simp only [hProjection, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    have h := frameFreeBoundaryVerticalEvaluation_smooth_reconstructs period hPeriod baseMetric 0 0 parameter boundary
    dsimp only at h
    rw [hZero] at h
    exact h
  ext boundary
  have h := frameFreeBoundaryNormalSquare_smooth period hPeriod baseMetric 0 baseMetric (by simp) 0 parameter boundary
  rw [hZero, hNormal, intrinsicGraphLatitude_zero_square] at h
  exact h

theorem frameFreeBoundaryNormalSquare_zero_one_pos (boundary : Boundary) :
    0 < frameFreeBoundaryNormalSquare period hPeriod baseMetric ((0, 1) : Input) boundary := by
  rw [frameFreeBoundaryNormalSquare_zero_joint]
  exact zero_lt_one

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryNormalSquareBase4D
