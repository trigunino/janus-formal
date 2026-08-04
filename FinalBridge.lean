import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

open scoped Manifold ContDiff Topology
open Filter Set Module

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev TestEffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TestOrientationBoundary :=
  CutThroatBoundary period hPeriod

local instance testEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance testEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance testOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance testOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

theorem test_localSectionMeanCurvature_eventually_eq_reanchored_public
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    ∀ᶠ current in nhds base,
      NormalGraphNonNullAt period hPeriod metric displacement current.2 ∧
        (let currentBoundary :=
          normalGraphOrientationLocalSection period hPeriod boundary current.1
        let currentCoordinate :=
          normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current
        normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
            hPeriod metric displacement boundary parameter patch coordinate
              current =
          normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
            hPeriod metric displacement currentBoundary current.2 patch
              currentCoordinate current) := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let tangentTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  let cotangentTrivialization :=
    trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hNonNullCurrent : ∀ᶠ current in nhds base,
      NormalGraphNonNullAt period hPeriod metric displacement current.2 :=
    continuous_snd.continuousAt.eventually
      ((normalGraphNonNullDomain_isOpen period hPeriod metric displacement)
        |>.mem_nhds hNonNull)
  have hFstTendsto : Tendsto Prod.fst (nhds base) (nhds base.1) :=
    continuous_fst.continuousAt
  have hSectionReconstruct :
      (fun current : TestEffectiveThroat period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1))
        =ᶠ[nhds base] Prod.fst := by
    change ((fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) ∘
        Prod.fst) =ᶠ[nhds base] Prod.fst
    exact (normalGraphOrientationLocalSection_eventually_reconstructs period
      hPeriod boundary).comp_tendsto hFstTendsto
  have hGraphReanchor :=
    normalGraphHolonomicCoordinateGerm_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hGraph
  have hNormalReanchor :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventuallyEq_reanchored
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hFirstTangent : ∀ᶠ current in nhds base,
      current.1 ∈ tangentTrivialization.baseSet :=
    continuous_fst.continuousAt.eventually
      (tangentTrivialization.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1))
  have hFirstCotangent : ∀ᶠ current in nhds base,
      current.1 ∈ cotangentTrivialization.baseSet :=
    continuous_fst.continuousAt.eventually
      (cotangentTrivialization.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1))
  filter_upwards [hNonNullCurrent, hSectionReconstruct,
    hGraphReanchor, hNormalReanchor, hFirstTangent,
      hFirstCotangent] with current hCurrentNonNull hProjection hGraphGerm
        hNormalGerm hFirstTangentAt hFirstCotangentAt
  constructor
  · exact hCurrentNonNull
  · let currentBoundary :=
      normalGraphOrientationLocalSection period hPeriod boundary current.1
    let currentCoordinate :=
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current
    let currentBase : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod currentBoundary, current.2)
    have hCurrentProjection :
        orientationDoubleToThroat period hPeriod currentBoundary = current.1 := by
      simpa [currentBoundary] using hProjection
    have hCurrentBase : currentBase = current := by
      exact Prod.ext hCurrentProjection rfl
    have hSecondTangent : current.1 ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod currentBoundary)).baseSet := by
      rw [hCurrentProjection]
      exact mem_baseSet_trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) current.1
    have hSecondCotangent : current.1 ∈
        (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod currentBoundary)).baseSet := by
      rw [hCurrentProjection]
      exact mem_baseSet_trivializationAt
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) current.1
    have hGraphGermDynamic :
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
            coordinate =ᶠ[nhds current]
          normalGraphHolonomicCoordinateGerm period hPeriod displacement
            currentBase patch currentCoordinate := by
      rw [hCurrentBase]
      simpa [currentCoordinate] using hGraphGerm
    have hNaturality :=
      normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_natural_of_eventuallyEq
        period hPeriod metric displacement boundary currentBoundary parameter
          current.2 current hCurrentNonNull patch coordinate
            currentCoordinate hFirstTangentAt hSecondTangent hFirstCotangentAt
              hSecondCotangent hGraphGermDynamic hNormalGerm
    exact hNaturality.symm

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
end JanusFormal
