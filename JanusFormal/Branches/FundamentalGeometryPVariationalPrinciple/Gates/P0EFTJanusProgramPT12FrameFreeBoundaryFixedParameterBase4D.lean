import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D

/-! At zero displacement the actual normal graph is independent of its parameter.
Consequently every fixed parameter, including one, has the same inhabited volume base. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod

theorem normalCoordinateLift_zero_displacement
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    normalCoordinateLift period hPeriod 0 anchor = 0 := by
  let point := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  have hPoint : point ∈ normalBundleBaseSet period hPeriod anchor :=
    mappingTorusMk_mem_normalBundleBaseSet period hPeriod anchor
  change (((fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor) ⟨point, 0⟩).2 = 0
  exact (((fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor).linearEquivAt
    Real point hPoint).map_zero

theorem normalGraph_zero_displacement_eq_zero (parameter : Real) :
    normalGraph period hPeriod 0 parameter = normalGraph period hPeriod 0 0 := by
  funext point
  refine Quotient.inductionOn point ?_
  intro anchor
  change mappingTorusMk (reflectedSphereData period hPeriod)
      (normalGraphCoverMap period hPeriod 0 parameter anchor) =
    mappingTorusMk (reflectedSphereData period hPeriod) (normalGraphCoverMap period hPeriod 0 0 anchor)
  congr 1
  simp only [normalGraphCoverMap, normalGraphCoordinate,
    normalCoordinateLift_zero_displacement, mul_zero, Real.arctan_zero]

theorem normalGraphRelativeDeterminant_zero_displacement
    (metric : SmoothGeneralLorentzMetric period hPeriod) (parameter : Real)
    (point : Throat period hPeriod) :
    normalGraphRelativeDeterminant period hPeriod metric 0 parameter point =
      normalGraphRelativeDeterminant period hPeriod metric 0 0 point := by
  unfold normalGraphRelativeDeterminant normalGraphRelativeEndomorphism normalGraphInducedMetricValue
  rw [normalGraph_zero_displacement_eq_zero period hPeriod parameter]

local notation "frame" => finiteSmoothTangentFrame period hPeriod

theorem frameFreeBoundaryInducedDeterminant_zero_joint
    (metric : SmoothGeneralLorentzMetric period hPeriod) (parameter : Real) :
    frameFreeBoundaryInducedDeterminant period hPeriod metric (0, parameter) =
      frameFreeBoundaryInducedDeterminant period hPeriod metric 0 := by
  ext boundary
  have hSmoothZero : smoothToFrameFreeBoundaryJointCore period hPeriod frame metric
      ((0 : SmoothSymmetricCovariantTwoTensor period hPeriod), (0 : SmoothNormalDisplacement period hPeriod)) = 0 :=
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric).map_zero
  have hParameter := frameFreeBoundaryInducedDeterminant_smooth_eq_historical
    period hPeriod metric 0 metric (by simp) 0 parameter boundary
  have hZero := frameFreeBoundaryInducedDeterminant_smooth_eq_historical
    period hPeriod metric 0 metric (by simp) 0 0 boundary
  rw [hSmoothZero] at hParameter hZero
  exact hParameter.trans ((normalGraphRelativeDeterminant_zero_displacement period hPeriod metric
    parameter (orientationDoubleToThroat period hPeriod boundary)).trans hZero.symm)

local notation "baseMetric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real

theorem zero_joint_mem_intrinsicFrameFreeBoundaryInducedDomain (parameter : Real) :
    ((0, parameter) : Input) ∈ frameFreeBoundaryInducedDomain period hPeriod baseMetric := by
  change IsUnit (frameFreeBoundaryInducedDeterminant period hPeriod baseMetric (0, parameter))
  rw [frameFreeBoundaryInducedDeterminant_zero_joint]
  exact zero_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod

theorem frameFreeBoundaryInducedDeterminantRatio_zero_joint (parameter : Real) :
    frameFreeBoundaryInducedDeterminantRatio period hPeriod (0, parameter) = 1 := by
  unfold frameFreeBoundaryInducedDeterminantRatio
  rw [frameFreeBoundaryInducedDeterminant_zero_joint]
  exact frameFreeBoundaryInducedDeterminantRatio_zero period hPeriod

theorem zero_joint_mem_frameFreeBoundaryInducedVolumeDomain (parameter : Real) :
    ((0, parameter) : Input) ∈ frameFreeBoundaryInducedVolumeDomain period hPeriod := by
  refine ⟨zero_joint_mem_intrinsicFrameFreeBoundaryInducedDomain period hPeriod parameter, ?_⟩
  change frameFreeBoundaryInducedDeterminantRatio period hPeriod (0, parameter) ∈
    frameFreeBoundaryPositiveRootTarget period hPeriod
  rw [frameFreeBoundaryInducedDeterminantRatio_zero_joint]
  exact one_mem_frameFreeBoundaryPositiveRootTarget period hPeriod

theorem frameFreeBoundaryInducedVolumeDomain_mem_nhds_zero_joint (parameter : Real) :
    frameFreeBoundaryInducedVolumeDomain period hPeriod ∈ 𝓝 ((0, parameter) : Input) :=
  (frameFreeBoundaryInducedVolumeDomain_isOpen period hPeriod).mem_nhds
    (zero_joint_mem_frameFreeBoundaryInducedVolumeDomain period hPeriod parameter)

theorem frameFreeBoundaryInducedVolume_zero_joint (parameter : Real) :
    frameFreeBoundaryInducedVolume period hPeriod (0, parameter) =
      frameFreeBoundaryInducedBaseVolume period hPeriod := by
  unfold frameFreeBoundaryInducedVolume
  rw [frameFreeBoundaryInducedDeterminantRatio_zero_joint,
    candidateANormalBoundaryScalarFieldLocalRootBranch_at_one, mul_one]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
