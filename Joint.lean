import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D

namespace JanusFormal
namespace Joint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev OrientationBoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev HolonomicVector4 :=
  P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4

attribute [local instance 30000]
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.throatCoverChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.throatCoverIsManifold
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveThroatChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveThroatIsManifold
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveQuotientChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveQuotientIsManifold

local instance (priority := 30000) orientationBoundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000) orientationBoundaryCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundaryCover period hPeriod) :=
  fixedThroatCover_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000) orientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance (priority := 30000) orientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

theorem test_joint
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
          current.1) := by
  let coverField := fun current :
      OrientationBoundaryCover period hPeriod × Real =>
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement current.2
      current.1
  have hInvariant : ∀ (winding : Int)
      (current : OrientationBoundaryCover period hPeriod × Real),
      coverField (winding +ᵥ current.1, current.2) = coverField current := by
    intro winding current
    exact normalGraphCanonicalLatitudeLiftCover_invariant period hPeriod
      displacement current.2 winding current.1
  have hDescended := mappingTorusInvariantMapProd_contMDiff
    (orientationDoubleData period hPeriod) throatCoverModelWithCorners ∞
    (modelWithCornersSelf Real Real) coverModelWithCorners.tangent coverField
      hInvariant
      (fixedThroat_projection_isLocalDiffeomorph_smooth
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      (normalGraphCanonicalLatitudeLiftCover_joint_contMDiff period hPeriod
        displacement)
  exact hDescended.congr fun current => by
    obtain ⟨coverPoint, hPoint⟩ :=
      mappingTorusMk_surjective (orientationDoubleData period hPeriod) current.1
    rcases current with ⟨boundary, parameter⟩
    dsimp only at hPoint ⊢
    subst boundary
    rfl

private def testBoundaryParameter
    (current : OrientationBoundary period hPeriod × Real) :
    EffectiveThroat period hPeriod × Real :=
  (orientationDoubleToThroat period hPeriod current.1, current.2)

private theorem testBoundaryParameter_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (testBoundaryParameter period hPeriod) :=
  ((orientationDoubleToThroat_contMDiff period hPeriod).comp contMDiff_fst).prodMk
    contMDiff_snd

private def testLatitudeCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) :
    CoverCoordinates :=
  ((trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base))
    (normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
      current.1)).2

private theorem testLatitudeCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (testLatitudeCoordinates period hPeriod displacement base) base := by
  let trivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base)
  have hLift : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
          current.1) base :=
    (test_joint period hPeriod displacement).contMDiffAt
  have hMem : normalGraphCanonicalLatitudeLift period hPeriod displacement
      base.2 base.1 ∈ trivialization.source := by
    rw [trivialization.mem_source]
    change (normalGraphCanonicalLatitudeLift period hPeriod displacement
      base.2 base.1).1 ∈ trivialization.baseSet
    rw [normalGraphCanonicalLatitudeLift_base period hPeriod displacement
      base.2 base.1]
    exact mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base)
  exact ((trivialization.contMDiffAt_iff
    (f := fun current : OrientationBoundary period hPeriod × Real =>
      normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
        current.1) hMem).mp hLift).2

private def testMetricNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) :
    CoverCoordinates :=
  normalGraphMetricNormalProjectorCoordinates period hPeriod metric displacement
    (testBoundaryParameter period hPeriod base)
    (testBoundaryParameter period hPeriod current)
    (testLatitudeCoordinates period hPeriod displacement base current)

private theorem testMetricNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (testMetricNormalCoordinates period hPeriod metric displacement base)
      base := by
  have hParameter : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (testBoundaryParameter period hPeriod) base :=
    (testBoundaryParameter_contMDiff period hPeriod).contMDiffAt
  have hProjector :=
    (normalGraphMetricNormalProjectorCoordinates_contMDiffAt period hPeriod
      metric displacement (testBoundaryParameter period hPeriod base) hNonNull)
      |>.comp base hParameter
  exact hProjector.clm_apply
    (testLatitudeCoordinates_contMDiffAt period hPeriod displacement base)

private def testLocalLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (coordinates : OrientationBoundary period hPeriod × Real → CoverCoordinates)
    (current : OrientationBoundary period hPeriod × Real) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  (trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base))
      |>.toOpenPartialHomeomorph.symm
        (normalGraphOrientationDouble period hPeriod displacement current,
          coordinates current)

private theorem testLocalLift_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (coordinates : OrientationBoundary period hPeriod × Real → CoverCoordinates)
    (hCoordinates : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞ coordinates base) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (testLocalLift period hPeriod displacement base coordinates) base := by
  let trivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base)
  have hPair : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (coverModelWithCorners.prod
        (modelWithCornersSelf Real CoverCoordinates)) ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        (normalGraphOrientationDouble period hPeriod displacement current,
          coordinates current)) base :=
    (normalGraphOrientationDouble_contMDiff period hPeriod displacement)
      |>.contMDiffAt.prodMk hCoordinates
  have hInput :
      (normalGraphOrientationDouble period hPeriod displacement base,
        coordinates base) ∈ trivialization.target := by
    rw [trivialization.mem_target]
    exact mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base)
  have hSymm : ContMDiffAt
      (coverModelWithCorners.prod
        (modelWithCornersSelf Real CoverCoordinates))
      coverModelWithCorners.tangent ∞
      trivialization.toOpenPartialHomeomorph.symm
      (normalGraphOrientationDouble period hPeriod displacement base,
        coordinates base) :=
    trivialization.contMDiffOn_symm.contMDiffAt
      (trivialization.open_target.mem_nhds hInput)
  apply (hSymm.comp base hPair).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun current => by
    unfold testLocalLift
    rfl

private def testHolonomicJointCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (coordinates : OrientationBoundary period hPeriod × Real → CoverCoordinates)
    (current : OrientationBoundary period hPeriod × Real) : HolonomicVector4 :=
  let graph := fun point : OrientationBoundary period hPeriod × Real =>
    normalGraphOrientationDouble period hPeriod displacement point
  let localInverse :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
  inTangentCoordinates coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) graph
      (fun point => localInverse (graph point))
      (fun point => mfderiv coverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) localInverse (graph point))
      base current (coordinates current)

private theorem testHolonomicJointCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (coordinates : OrientationBoundary period hPeriod × Real → CoverCoordinates)
    (hCoordinates : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞ coordinates base)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement base) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (testHolonomicJointCoordinates period hPeriod displacement base patch
        coordinate coordinates) base := by
  let graph := fun point : OrientationBoundary period hPeriod × Real =>
    normalGraphOrientationDouble period hPeriod displacement point
  let localInverse :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
  have hInverse : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ localInverse (graph base) := by
    change ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ localInverse
      (normalGraphOrientationDouble period hPeriod displacement base)
    rw [← hAt]
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.localInverse_contMDiffAt
  have hUncurry : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        coverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (Function.uncurry (fun _ : OrientationBoundary period hPeriod × Real =>
        localInverse)) (base, graph base) := by
    change ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        coverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun current => localInverse current.2) (base, graph base)
    exact hInverse.comp (base, graph base) contMDiffAt_snd
  have hGraph : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞ graph base :=
    (normalGraphOrientationDouble_contMDiff period hPeriod displacement)
      |>.contMDiffAt
  have hApplied := ContMDiffAt.mfderiv_apply
    (I := coverModelWithCorners)
    (I' := modelWithCornersSelf Real HolonomicVector4)
    (f := fun _ : OrientationBoundary period hPeriod × Real => localInverse)
    (g := graph) (g₁ := id)
    (g₂ := coordinates)
    hUncurry hGraph contMDiffAt_id hCoordinates (by simp)
  exact hApplied

private theorem testHolonomicJointCoordinates_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (coordinates : OrientationBoundary period hPeriod × Real → CoverCoordinates) :
    testHolonomicJointCoordinates period hPeriod displacement base patch
        coordinate coordinates base =
      mfderiv coverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
        (normalGraphOrientationDouble period hPeriod displacement base)
        ((trivializationAt CoverCoordinates
          (fun point : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners point)
          (normalGraphOrientationDouble period hPeriod displacement base)).symm
            (normalGraphOrientationDouble period hPeriod displacement base)
            (coordinates base)) := by
  simp [testHolonomicJointCoordinates, inTangentCoordinates,
    ContinuousLinearMap.inCoordinates, Trivialization.symmL_apply]
  rfl

end
end Joint
end JanusFormal
