import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

open scoped Manifold ContDiff Topology
open Filter Set Module

variable
    {𝕜 E F H₁ H₂ M N : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H₁] [TopologicalSpace H₂]
    (I : ModelWithCorners 𝕜 E H₁)
    (J : ModelWithCorners 𝕜 F H₂)
    [TopologicalSpace M] [ChartedSpace H₁ M]
    [TopologicalSpace N] [ChartedSpace H₂ N]

theorem test_localInverse_eventuallyEq
    {n : ℕ∞ω} {f : M → N} {x x' : M}
    (hf : IsLocalDiffeomorphAt I J n f x)
    (hg : IsLocalDiffeomorphAt I J n f x')
    (hx' : x' ∈ hf.localInverse.target) :
    hf.localInverse =ᶠ[nhds (f x')] hg.localInverse := by
  have hxChoose : x' ∈ hf.choose.source := hx'
  have hForward : f x' = hf.choose x' := hf.choose_spec.2 hxChoose
  have hSource : f x' ∈ hf.localInverse.source := by
    rw [hForward]
    exact hf.localInverse.map_target hx'
  have hBase : hf.localInverse (f x') = x' :=
    hf.localInverse_left_inv hx'
  have hContinuous : ContinuousAt hf.localInverse (f x') :=
    hf.localInverse_contMDiffOn.contMDiffAt
      (hf.localInverse.open_source.mem_nhds hSource) |>.continuousAt
  rw [ContinuousAt, hBase] at hContinuous
  have hTarget : ∀ᶠ point in nhds (f x'),
      hf.localInverse point ∈ hg.localInverse.target :=
    hContinuous.eventually
      (hg.localInverse.open_target.mem_nhds hg.localInverse_mem_target)
  have hRight : (f ∘ hf.localInverse) =ᶠ[nhds (f x')] id :=
    Filter.eventuallyEq_of_mem
      (hf.localInverse.open_source.mem_nhds hSource)
      hf.localInverse_eqOn_right
  filter_upwards [hTarget, hRight] with point hPoint hPointRight
  calc
    hf.localInverse point =
        hg.localInverse (f (hf.localInverse point)) :=
      (hg.localInverse_left_inv hPoint).symm
    _ = hg.localInverse point := congrArg hg.localInverse hPointRight

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
open P0EFTJanusExplicitBoundaryDensityLedger

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev TestEffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TestEffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TestOrientationBoundary :=
  CutThroatBoundary period hPeriod

local instance testEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance testEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance testEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel (TestEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance testEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (TestEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance testOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance testOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

theorem test_orientationLocalSection_eventuallyEq_reanchored
    (boundary : TestOrientationBoundary period hPeriod) :
    let base := orientationDoubleToThroat period hPeriod boundary
    ∀ᶠ point in nhds base,
      normalGraphOrientationLocalSection period hPeriod boundary =ᶠ[nhds point]
        normalGraphOrientationLocalSection period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary point) := by
  dsimp only
  let hFixed :=
    orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary
  let localSection := normalGraphOrientationLocalSection period hPeriod boundary
  have hContinuous : ContinuousAt localSection
      (orientationDoubleToThroat period hPeriod boundary) :=
    (normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary)
      |>.continuousAt
  change Tendsto localSection
    (nhds (orientationDoubleToThroat period hPeriod boundary))
    (nhds (localSection
      (orientationDoubleToThroat period hPeriod boundary))) at hContinuous
  have hLocalSectionBase : localSection
      (orientationDoubleToThroat period hPeriod boundary) = boundary := by
    exact normalGraphOrientationLocalSection_base period hPeriod boundary
  rw [hLocalSectionBase] at hContinuous
  have hTarget : ∀ᶠ point in
      nhds (orientationDoubleToThroat period hPeriod boundary),
      localSection point ∈ hFixed.localInverse.target :=
    hContinuous.eventually
      (hFixed.localInverse.open_target.mem_nhds
        hFixed.localInverse_mem_target)
  have hReconstruct :=
    normalGraphOrientationLocalSection_eventually_reconstructs period hPeriod
      boundary
  filter_upwards [hTarget, hReconstruct] with point hPoint hPointReconstruct
  let currentBoundary := localSection point
  let hCurrent :=
    orientationDoubleToThroat_isLocalDiffeomorph period hPeriod currentBoundary
  have hUnique := test_localInverse_eventuallyEq
    throatCoverModelWithCorners throatCoverModelWithCorners hFixed hCurrent hPoint
  change hFixed.localInverse =ᶠ[nhds point] hCurrent.localInverse
  have hCurrentPoint :
      orientationDoubleToThroat period hPeriod currentBoundary = point := by
    simpa [currentBoundary, localSection] using hPointReconstruct
  rw [hCurrentPoint] at hUnique
  exact hUnique

theorem test_holonomicLocalInverse_eventuallyEq_reanchored
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in nhds base,
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse =ᶠ[
        nhds (normalGraph period hPeriod displacement current.2 current.1)]
        (patch.coordinateMap_isLocalDiffeomorph currentCoordinate).localInverse := by
  dsimp only
  let hFixed := patch.coordinateMap_isLocalDiffeomorph coordinate
  let coordinateGerm :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate
  have hContinuous : ContinuousAt coordinateGerm base :=
    (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt).continuousAt
  change Tendsto coordinateGerm (nhds base)
    (nhds (coordinateGerm base)) at hContinuous
  have hCoordinateBase : coordinateGerm base = coordinate := by
    exact normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hAt
  rw [hCoordinateBase] at hContinuous
  have hTarget : ∀ᶠ current in nhds base,
      coordinateGerm current ∈ hFixed.localInverse.target :=
    hContinuous.eventually
      (hFixed.localInverse.open_target.mem_nhds hFixed.localInverse_mem_target)
  have hReconstruct :=
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt
  filter_upwards [hTarget, hReconstruct] with current hCurrentTarget hReconstructAt
  let currentCoordinate := coordinateGerm current
  let hCurrent := patch.coordinateMap_isLocalDiffeomorph currentCoordinate
  have hUnique := test_localInverse_eventuallyEq
    (modelWithCornersSelf Real Vector4) coverModelWithCorners hFixed hCurrent
      hCurrentTarget
  change hFixed.localInverse =ᶠ[
      nhds (normalGraph period hPeriod displacement current.2 current.1)]
    hCurrent.localInverse
  have hCurrentPoint : patch.coordinateMap currentCoordinate =
      normalGraph period hPeriod displacement current.2 current.1 := by
    simpa [currentCoordinate, coordinateGerm, Function.comp_def] using
      hReconstructAt
  rw [hCurrentPoint] at hUnique
  exact hUnique

def testTangentCoordinateTransition
    (firstBase secondBase current : TestEffectiveThroat period hPeriod)
    (hFirst : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecond : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet) :
    ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates :=
  ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
    |>.continuousLinearEquivAt Real current hFirst).symm.trans
  ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
    |>.continuousLinearEquivAt Real current hSecond)

def testCotangentCoordinateTransition
    (firstBase secondBase current : TestEffectiveThroat period hPeriod)
    (hFirst : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecond : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet) :
    (ThroatCoverCoordinates →L[Real] Real) ≃L[Real]
      (ThroatCoverCoordinates →L[Real] Real) :=
  ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
    |>.continuousLinearEquivAt Real current hFirst).symm.trans
  ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
    |>.continuousLinearEquivAt Real current hSecond)

theorem test_inducedInverseCoordinates_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBase secondBase current : TestEffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase.1).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase.1).baseSet) :
    (normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement secondBase current).comp
        (testCotangentCoordinateTransition period hPeriod firstBase.1
          secondBase.1 current.1 hFirstCotangent hSecondCotangent :
            (ThroatCoverCoordinates →L[Real] Real) →L[Real]
              (ThroatCoverCoordinates →L[Real] Real)) =
      (testTangentCoordinateTransition period hPeriod firstBase.1 secondBase.1
        current.1 hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates).comp
        (normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement firstBase current) := by
  rw [normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
      metric displacement firstBase current hNonNull hFirstTangent
        hFirstCotangent,
    normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
      metric displacement secondBase current hNonNull hSecondTangent
        hSecondCotangent]
  rw [ContinuousLinearMap.inCoordinates_eq hFirstCotangent hFirstTangent,
    ContinuousLinearMap.inCoordinates_eq hSecondCotangent hSecondTangent]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecondCotangent
  apply ContinuousLinearMap.ext
  intro covector
  change tangentSecond
      (normalGraphInducedMetricInverse period hPeriod metric displacement
        current.2 hNonNull current.1
          (cotangentSecond.symm (cotangentSecond (cotangentFirst.symm covector)))) =
    tangentSecond (tangentFirst.symm
      (tangentFirst
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          current.2 hNonNull current.1 (cotangentFirst.symm covector))))
  rw [cotangentSecond.symm_apply_apply, tangentFirst.symm_apply_apply]

theorem test_fiberLinearMapCoordinates_natural
    (firstBase secondBase current : TestEffectiveThroat period hPeriod)
    (hFirstTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecondTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet)
    (hFirstCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecondCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet)
    (fiberMap : ThroatTangentFiber period hPeriod current →L[Real]
      ThroatCotangentFiber period hPeriod current) :
    (ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        secondBase current secondBase current fiberMap).comp
      (testTangentCoordinateTransition period hPeriod firstBase secondBase
        current hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
    (testCotangentCoordinateTransition period hPeriod firstBase secondBase
        current hFirstCotangent hSecondCotangent :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)).comp
      (ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        firstBase current firstBase current fiberMap) := by
  rw [ContinuousLinearMap.inCoordinates_eq hFirstTangent hFirstCotangent,
    ContinuousLinearMap.inCoordinates_eq hSecondTangent hSecondCotangent]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondCotangent
  apply ContinuousLinearMap.ext
  intro vector
  change cotangentSecond
      (fiberMap (tangentSecond.symm (tangentSecond (tangentFirst.symm vector)))) =
    cotangentSecond (cotangentFirst.symm
      (cotangentFirst (fiberMap (tangentFirst.symm vector))))
  rw [tangentSecond.symm_apply_apply, cotangentFirst.symm_apply_apply]

#check LinearMap.trace_conj'

theorem test_trace_eq_of_intertwining
    (first second : ThroatCoverCoordinates →ₗ[Real] ThroatCoverCoordinates)
    (transition : ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates)
    (hIntertwine : second.comp transition.toLinearMap =
      transition.toLinearMap.comp first) :
    LinearMap.trace Real ThroatCoverCoordinates second =
      LinearMap.trace Real ThroatCoverCoordinates first := by
  have hConj : second = transition.conj first := by
    apply LinearMap.ext
    intro vector
    have hApply := LinearMap.congr_fun hIntertwine (transition.symm vector)
    simpa [LinearEquiv.conj_apply] using hApply
  rw [hConj]
  exact LinearMap.trace_conj' first transition

theorem test_contractedTrace_natural
    (firstInverse secondInverse :
      (ThroatCoverCoordinates →L[Real] Real) →L[Real]
        ThroatCoverCoordinates)
    (firstForm secondForm : ThroatCoverCoordinates →L[Real]
      (ThroatCoverCoordinates →L[Real] Real))
    (tangentTransition :
      ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates)
    (cotangentTransition :
      (ThroatCoverCoordinates →L[Real] Real) ≃L[Real]
        (ThroatCoverCoordinates →L[Real] Real))
    (hInverse : secondInverse.comp
        (cotangentTransition :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)) =
      (tangentTransition : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates).comp firstInverse)
    (hForm : secondForm.comp
        (tangentTransition : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates) =
      (cotangentTransition :
        (ThroatCoverCoordinates →L[Real] Real) →L[Real]
          (ThroatCoverCoordinates →L[Real] Real)).comp firstForm) :
    LinearMap.trace Real ThroatCoverCoordinates
        (secondInverse.toLinearMap.comp secondForm.toLinearMap) =
      LinearMap.trace Real ThroatCoverCoordinates
        (firstInverse.toLinearMap.comp firstForm.toLinearMap) := by
  apply test_trace_eq_of_intertwining
    (transition := tangentTransition.toLinearEquiv)
  apply LinearMap.ext
  intro vector
  change secondInverse (secondForm (tangentTransition vector)) =
    tangentTransition (firstInverse (firstForm vector))
  have hFormApply := congrArg (fun map => map vector) hForm
  simp only [ContinuousLinearMap.comp_apply] at hFormApply
  erw [hFormApply]
  have hInverseApply := congrArg (fun map => map (firstForm vector)) hInverse
  simp only [ContinuousLinearMap.comp_apply] at hInverseApply
  exact hInverseApply

private def testThroatCoordinateBasis :
    Basis (Fin 3) Real ThroatCoverCoordinates := by
  let basis := Module.finBasis Real ThroatCoverCoordinates
  have hDimension : Module.finrank Real ThroatCoverCoordinates = 3 := by
    simp [ThroatCoverCoordinates]
  simpa [hDimension] using basis

private def testThroatContinuousDualBasis :
    Basis (Fin 3) Real (ThroatCoverCoordinates →L[Real] Real) :=
  (testThroatCoordinateBasis).dualBasis.map
    (LinearMap.toContinuousLinearMap :
      Module.Dual Real ThroatCoverCoordinates ≃ₗ[Real]
        (ThroatCoverCoordinates →L[Real] Real))

def testLocalSectionExtrinsicCurvatureLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real]
      (ThroatCoverCoordinates →L[Real] Real) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin testThroatCoordinateBasis testThroatContinuousDualBasis
      (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
        period hPeriod metric displacement boundary parameter patch coordinate
          current))

theorem testLocalSectionExtrinsicCurvatureLinearMap_toMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    LinearMap.toMatrix testThroatCoordinateBasis testThroatContinuousDualBasis
        (testLocalSectionExtrinsicCurvatureLinearMap period hPeriod metric
          displacement boundary parameter patch coordinate current).toLinearMap =
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
        period hPeriod metric displacement boundary parameter patch coordinate
          current := by
  apply (Matrix.toLin testThroatCoordinateBasis
    testThroatContinuousDualBasis).injective
  simp [testLocalSectionExtrinsicCurvatureLinearMap]

theorem testLocalSectionMeanCurvatureFamily_eq_trace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement boundary parameter patch coordinate current =
      LinearMap.trace Real ThroatCoverCoordinates
        ((normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement
            (orientationDoubleToThroat period hPeriod boundary, parameter)
            current).toLinearMap.comp
          (testLocalSectionExtrinsicCurvatureLinearMap period hPeriod metric
            displacement boundary parameter patch coordinate current).toLinearMap) := by
  rw [LinearMap.trace_eq_matrix_trace Real testThroatCoordinateBasis]
  rw [LinearMap.toMatrix_comp testThroatCoordinateBasis
    testThroatContinuousDualBasis testThroatCoordinateBasis]
  rw [testLocalSectionExtrinsicCurvatureLinearMap_toMatrix]
  rfl

private theorem test_eventually_local
    {α : Type*} [TopologicalSpace α] {predicate : α → Prop} {base : α}
    (hPredicate : ∀ᶠ point in nhds base, predicate point) :
    ∀ᶠ current in nhds base, ∀ᶠ point in nhds current, predicate point := by
  have hSet : {point | predicate point} ∈ nhds base := hPredicate
  obtain ⟨neighborhood, hSubset, hOpen, hBase⟩ := mem_nhds_iff.mp hSet
  filter_upwards [hOpen.mem_nhds hBase] with current hCurrent
  exact Filter.mem_of_superset (hOpen.mem_nhds hCurrent) hSubset

private theorem test_eventually_local_eq
    {α β : Type*} [TopologicalSpace α]
    {first second : α → β} {base : α}
    (hEq : first =ᶠ[nhds base] second) :
    ∀ᶠ current in nhds base, first =ᶠ[nhds current] second :=
  test_eventually_local hEq

theorem test_localSectionNormal_eventuallyEq_reanchored
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
      let currentBoundary :=
        normalGraphOrientationLocalSection period hPeriod boundary current.1
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement boundary parameter patch coordinate =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement currentBoundary current.2 patch currentCoordinate := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let orientationBase : TestOrientationBoundary period hPeriod × Real :=
    (boundary, parameter)
  let fixedLift :=
    normalGraphOrientationLocalSectionJoint period hPeriod boundary
  have hLiftTendsto : Tendsto fixedLift (nhds base) (nhds orientationBase) := by
    have hLift :=
      (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
        boundary parameter).continuousAt
    change Tendsto fixedLift (nhds base) (nhds (fixedLift base)) at hLift
    have hLiftBase : fixedLift base = orientationBase := by
      simpa [fixedLift, base, orientationBase] using
        (normalGraphOrientationLocalSectionJoint_base period hPeriod boundary
          parameter)
    rw [hLiftBase] at hLift
    exact hLift
  have hFixedAdmissible : ∀ᶠ current in nhds base,
      NormalGraphCanonicalJointCoordinateAdmissible period hPeriod metric
        displacement orientationBase (fixedLift current) :=
    hLiftTendsto.eventually
      (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
        metric displacement orientationBase hNonNull)
  have hFixedAdmissibleLocal := test_eventually_local hFixedAdmissible
  have hNonNullCurrent : ∀ᶠ current in nhds base,
      current.2 ∈ normalGraphNonNullDomain period hPeriod metric displacement :=
    continuous_snd.continuousAt.eventually
      ((normalGraphNonNullDomain_isOpen period hPeriod metric displacement)
        |>.mem_nhds hNonNull)
  have hFstTendsto : Tendsto Prod.fst (nhds base) (nhds base.1) :=
    continuous_fst.continuousAt
  have hSectionReanchor :=
    hFstTendsto.eventually
      (normalGraphOrientationLocalSection_eventuallyEq_reanchored period hPeriod
        boundary)
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
  have hSectionReconstructLocal :=
    test_eventually_local_eq hSectionReconstruct
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseReanchor :=
    normalGraphHolonomicLocalInverse_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hGraph
  filter_upwards [hFixedAdmissibleLocal, hNonNullCurrent, hSectionReanchor,
    hSectionReconstruct, hSectionReconstructLocal, hInverseReanchor] with
    current hFixedAdmissibleAt hCurrentNonNull hSectionReanchorAt
      hSectionReconstructAt hSectionReconstructAtLocal hInverseReanchorAt
  let currentBoundary :=
    normalGraphOrientationLocalSection period hPeriod boundary current.1
  let currentCoordinate :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current
  let currentOrientationBase : TestOrientationBoundary period hPeriod × Real :=
    (currentBoundary, current.2)
  let currentLift :=
    normalGraphOrientationLocalSectionJoint period hPeriod currentBoundary
  have hCurrentProjection :
      orientationDoubleToThroat period hPeriod currentBoundary = current.1 := by
    simpa [currentBoundary] using hSectionReconstructAt
  have hCurrentLiftTendsto : Tendsto currentLift (nhds current)
      (nhds currentOrientationBase) := by
    have hLift :=
      (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
        currentBoundary current.2).continuousAt
    change Tendsto currentLift
      (nhds (orientationDoubleToThroat period hPeriod currentBoundary,
        current.2)) (nhds (currentLift
          (orientationDoubleToThroat period hPeriod currentBoundary,
            current.2))) at hLift
    have hLiftBase : currentLift
        (orientationDoubleToThroat period hPeriod currentBoundary, current.2) =
      currentOrientationBase := by
      simpa [currentLift, currentOrientationBase] using
        (normalGraphOrientationLocalSectionJoint_base period hPeriod
          currentBoundary current.2)
    have hAnchor :
        (orientationDoubleToThroat period hPeriod currentBoundary, current.2) =
          current := by
      exact Prod.ext hCurrentProjection rfl
    rw [hAnchor] at hLift hLiftBase
    rw [hLiftBase] at hLift
    exact hLift
  have hCurrentAdmissible : ∀ᶠ point in nhds current,
      NormalGraphCanonicalJointCoordinateAdmissible period hPeriod metric
        displacement currentOrientationBase (currentLift point) :=
    hCurrentLiftTendsto.eventually
      (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
        metric displacement currentOrientationBase hCurrentNonNull)
  have hLiftEq : fixedLift =ᶠ[nhds current] currentLift := by
    have hSection := hSectionReanchorAt.comp_tendsto
      (show Tendsto Prod.fst (nhds current) (nhds current.1) from
        continuous_fst.continuousAt)
    filter_upwards [hSection] with point hPoint
    change
      (normalGraphOrientationLocalSection period hPeriod boundary point.1,
        point.2) =
      (normalGraphOrientationLocalSection period hPeriod currentBoundary point.1,
        point.2)
    simpa [currentBoundary, Function.comp_def] using
      congrArg (fun value => (value, point.2)) hPoint
  have hGraphTendsto : Tendsto
      (fun point : TestEffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
      (nhds current)
      (nhds (normalGraph period hPeriod displacement current.2 current.1)) :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  have hInverseLocal := test_eventually_local_eq hInverseReanchorAt
  have hInverseAlongGraph := hGraphTendsto.eventually hInverseLocal
  filter_upwards [hFixedAdmissibleAt, hCurrentAdmissible, hLiftEq,
    hSectionReconstructAtLocal, hInverseAlongGraph] with point hFixed hCurrent
      hLift hReconstruct hInverse
  rcases hFixed with ⟨hFixedNonNull, hFixedTangent, hFixedCotangent, hFixedImage⟩
  rw [← hLift] at hCurrent
  rcases hCurrent with
    ⟨hReanchoredNonNull, hReanchoredTangent, hReanchoredCotangent,
      hReanchoredImage⟩
  have hFixedIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement orientationBase (fixedLift point)
        hFixedNonNull hFixedTangent hFixedCotangent hFixedImage patch coordinate
  have hCurrentIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement currentOrientationBase
        (fixedLift point) hReanchoredNonNull hReanchoredTangent
          hReanchoredCotangent hReanchoredImage patch currentCoordinate
  change
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement orientationBase patch coordinate
          (fixedLift point) =
      normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement currentOrientationBase patch
          currentCoordinate (currentLift point)
  rw [← hLift]
  rw [hFixedIntrinsic, hCurrentIntrinsic]
  have hNonNullProof : hReanchoredNonNull = hFixedNonNull :=
    Subsingleton.elim _ _
  rw [hNonNullProof]
  have hGraphPoint :
      normalGraphOrientationDouble period hPeriod displacement (fixedLift point) =
        normalGraph period hPeriod displacement point.2 point.1 := by
    change normalGraph period hPeriod displacement point.2
        (orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary point.1)) =
      normalGraph period hPeriod displacement point.2 point.1
    exact congrArg (normalGraph period hPeriod displacement point.2) hReconstruct
  rw [hGraphPoint]
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners)
    (I' := modelWithCornersSelf Real Vector4) hInverse
  exact congrArg (fun derivative => derivative
    (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      point.2 hFixedNonNull (fixedLift point).1)) hDerivative

theorem test_throatCotangentCoordinates_apply
    (base current : TestEffectiveThroat period hPeriod)
    (hTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base).baseSet)
    (hCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base).baseSet)
    (covector : ThroatCotangentFiber period hPeriod current)
    (vector : ThroatTangentFiber period hPeriod current) :
    ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base)
      |>.continuousLinearEquivAt Real current hCotangent) covector
        (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base)
          |>.continuousLinearEquivAt Real current hTangent) vector) =
      covector vector := by
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base) hCotangent,
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base) hTangent]
  rw [(trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base)
      |>.continuousLinearMapAt_apply_of_mem (R := Real) hCotangent,
    (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base)
      |>.continuousLinearMapAt_apply_of_mem (R := Real) hTangent]
  rw [hom_trivializationAt_apply]
  unfold ContinuousLinearMap.inCoordinates
  simp
  rw [(trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) base).symm_apply_apply_mk hTangent]

theorem test_throatCoordinateTransition_pairing
    (firstBase secondBase current : TestEffectiveThroat period hPeriod)
    (hFirstTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecondTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet)
    (hFirstCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecondCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet)
    (covector : ThroatCoverCoordinates →L[Real] Real)
    (vector : ThroatCoverCoordinates) :
    normalGraphThroatCotangentCoordinateTransition period hPeriod firstBase
        secondBase current hFirstCotangent hSecondCotangent covector
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            firstBase secondBase current hFirstTangent hSecondTangent vector) =
      covector vector := by
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondCotangent
  change cotangentSecond (cotangentFirst.symm covector)
      (tangentSecond (tangentFirst.symm vector)) = covector vector
  rw [test_throatCotangentCoordinates_apply period hPeriod secondBase current
    hSecondTangent hSecondCotangent]
  have hFirst := test_throatCotangentCoordinates_apply period hPeriod firstBase
    current hFirstTangent hFirstCotangent (cotangentFirst.symm covector)
      (tangentFirst.symm vector)
  change cotangentFirst (cotangentFirst.symm covector)
      (tangentFirst (tangentFirst.symm vector)) = _ at hFirst
  rw [cotangentFirst.apply_symm_apply, tangentFirst.apply_symm_apply] at hFirst
  exact hFirst.symm

theorem test_localSectionNormalDerivativeCoordinates_apply_eq_mfderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod boundary)).baseSet)
    (vector : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate current
          vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real Vector4)
        (fun point =>
          normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
            hPeriod metric displacement boundary parameter patch coordinate
              (point, current.2)) current.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod boundary)).symm current.1
              vector) := by
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  have hTarget : representative current ∈
      (trivializationAt Vector4
        (fun point : Vector4 =>
          TangentSpace (modelWithCornersSelf Real Vector4) point)
        (representative base)).baseSet :=
    mem_baseSet_trivializationAt Vector4
      (fun point : Vector4 =>
        TangentSpace (modelWithCornersSelf Real Vector4) point)
      (representative current)
  rw [show normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        current =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) Vector4
      (fun point : Vector4 =>
        TangentSpace (modelWithCornersSelf Real Vector4) point)
      base.1 current.1 (representative base) (representative current)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real Vector4)
        (fun point => representative (point, current.2)) current.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hTarget]
  simp [base, representative]

theorem test_coordinateGerm_eventuallyEq_reanchored
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in nhds base,
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
          coordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement current
          patch currentCoordinate := by
  have hInverse :=
    normalGraphHolonomicLocalInverse_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hAt
  filter_upwards [hInverse] with current hInverseAt
  dsimp only
  have hGraphTendsto : Tendsto
      (fun point : TestEffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
      (nhds current)
      (nhds (normalGraph period hPeriod displacement current.2 current.1)) :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  change
    ((patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse ∘
      fun point : TestEffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1) =ᶠ[nhds current]
    (((patch.coordinateMap_isLocalDiffeomorph
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)).localInverse) ∘
      fun point : TestEffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
  exact hInverseAt.comp_tendsto hGraphTendsto

set_option backward.isDefEq.respectTransparency false in
theorem test_graphDerivativeCoordinates_natural_of_eventuallyEq
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBase secondBase current : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate currentCoordinate : Vector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase.1).baseSet)
    (hGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement firstBase patch
          coordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement secondBase
          patch currentCoordinate) :
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        secondBase patch currentCoordinate current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod firstBase.1
        secondBase.1 current.1 hFirst hSecond :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        firstBase patch coordinate current := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [ContinuousLinearMap.comp_apply]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod displacement secondBase current patch currentCoordinate hSecond,
    normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod displacement firstBase current patch coordinate hFirst]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirst
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecond
  have hInput :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondBase.1).symm current.1
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            firstBase.1 secondBase.1 current.1 hFirst hSecond vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstBase.1).symm current.1 vector := by
    change tangentSecond.symm (tangentSecond (tangentFirst.symm vector)) = _
    exact tangentSecond.symm_apply_apply _
  erw [hInput]
  have hSection : Tendsto
      (fun point : TestEffectiveThroat period hPeriod => (point, current.2))
      (nhds current.1) (nhds current) := by
    have h : Tendsto
        (fun point : TestEffectiveThroat period hPeriod => (point, current.2))
        (nhds current.1) (nhds (current.1, current.2)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Prod.eta current] using h
  have hSlice := hGerm.comp_tendsto hSection
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Vector4) hSlice
  exact congrArg (fun derivative => derivative
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1).symm current.1 vector))
    hDerivative.symm

set_option backward.isDefEq.respectTransparency false in
theorem test_normalDerivativeCoordinates_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : TestOrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement secondBoundary secondParameter patch
          secondCoordinate current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirst hSecond :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement firstBoundary firstParameter patch
          firstCoordinate current := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [ContinuousLinearMap.comp_apply]
  rw [test_localSectionNormalDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod metric displacement secondBoundary secondParameter patch
        secondCoordinate current hSecond,
    test_localSectionNormalDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod metric displacement firstBoundary firstParameter patch
        firstCoordinate current hFirst]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod firstBoundary))
      |>.continuousLinearEquivAt Real current.1 hFirst
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod secondBoundary))
      |>.continuousLinearEquivAt Real current.1 hSecond
  have hInput :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod secondBoundary)).symm
          current.1
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            (orientationDoubleToThroat period hPeriod firstBoundary)
            (orientationDoubleToThroat period hPeriod secondBoundary) current.1
              hFirst hSecond vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod firstBoundary)).symm
          current.1 vector := by
    change tangentSecond.symm (tangentSecond (tangentFirst.symm vector)) = _
    exact tangentSecond.symm_apply_apply _
  erw [hInput]
  have hSection : Tendsto
      (fun point : TestEffectiveThroat period hPeriod => (point, current.2))
      (nhds current.1) (nhds current) := by
    have h : Tendsto
        (fun point : TestEffectiveThroat period hPeriod => (point, current.2))
        (nhds current.1) (nhds (current.1, current.2)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Prod.eta current] using h
  have hSlice := hGerm.comp_tendsto hSection
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Vector4) hSlice
  exact congrArg (fun derivative => derivative
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod firstBoundary)).symm
      current.1 vector)) hDerivative.symm

def test_localSectionRawExtrinsicCurvatureLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →ₗ[Real]
      ThroatCoverCoordinates →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second =>
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate
          first second current)
    (by
      intro first second third
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp_rw [←
        P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.localLeviCivitaChristoffelBilinearMap_apply]
      simp only [map_add, LinearMap.add_apply]
      ring)
    (by
      intro scalar first second
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp_rw [←
        P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.localLeviCivitaChristoffelBilinearMap_apply]
      simp only [map_smul, LinearMap.smul_apply]
      rw [← smul_add, map_smul]
      rfl)
    (by
      intro first second third
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp only [map_add])
    (by
      intro scalar first second
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp only [map_smul])

private def testContinuousBilinearOfLinear
    (form : ThroatCoverCoordinates →ₗ[Real]
      ThroatCoverCoordinates →ₗ[Real] Real) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun first =>
        LinearMap.toContinuousLinearMap (form first)
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro third
        simp
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        simp }

def test_localSectionExtrinsicCurvatureContinuousLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] Real :=
  let raw := test_localSectionRawExtrinsicCurvatureLinearMap period hPeriod
    metric displacement boundary parameter patch coordinate current
  testContinuousBilinearOfLinear
    ((1 / 2 : Real) • (raw + LinearMap.flip raw))

@[simp]
theorem test_localSectionExtrinsicCurvatureContinuousLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real)
    (first second : ThroatCoverCoordinates) :
    test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod metric
        displacement boundary parameter patch coordinate current first second =
      (1 / 2 : Real) *
        (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            first second current +
        normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            second first current) := by
  rfl

theorem test_localSectionExtrinsicCurvatureContinuousLinearMap_toMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (current : TestEffectiveThroat period hPeriod × Real) :
    LinearMap.toMatrix testThroatCoordinateBasis testThroatContinuousDualBasis
        (test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod
          metric displacement boundary parameter patch coordinate current).toLinearMap =
      (fun row column => (1 / 2 : Real) *
        (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            (testThroatCoordinateBasis row) (testThroatCoordinateBasis column)
              current +
        normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            (testThroatCoordinateBasis column) (testThroatCoordinateBasis row)
              current)) := by
  ext row column
  simp only [LinearMap.toMatrix_apply, testThroatContinuousDualBasis,
    Basis.map_repr, LinearEquiv.trans_apply, Basis.dualBasis_repr]
  simp
  ring

theorem test_localSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : TestOrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate)
    (first second : ThroatCoverCoordinates) :
    let transition :=
      normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirst hSecond
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement secondBoundary secondParameter patch
          secondCoordinate (transition first) (transition second) current =
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement firstBoundary firstParameter patch
          firstCoordinate first second current := by
  dsimp only
  let firstBase : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod firstBoundary, firstParameter)
  let secondBase : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod secondBoundary, secondParameter)
  have hGraphDerivative :=
    test_graphDerivativeCoordinates_natural_of_eventuallyEq period hPeriod
      displacement firstBase secondBase current patch firstCoordinate
        secondCoordinate hFirst hSecond hGraphGerm
  have hNormalDerivative :=
    test_normalDerivativeCoordinates_natural_of_eventuallyEq period hPeriod
      metric displacement firstBoundary secondBoundary firstParameter
        secondParameter current patch firstCoordinate secondCoordinate hFirst
          hSecond hNormalGerm
  have hGraphFirst := congrArg (fun derivative => derivative first)
    hGraphDerivative
  have hGraphSecond := congrArg (fun derivative => derivative second)
    hGraphDerivative
  have hNormalFirst := congrArg (fun derivative => derivative first)
    hNormalDerivative
  simp only [ContinuousLinearMap.comp_apply] at hGraphFirst hGraphSecond hNormalFirst
  dsimp only [firstBase, secondBase] at hGraphFirst hGraphSecond
  have hCoordinate := hGraphGerm.eq_of_nhds
  have hNormal := hNormalGerm.eq_of_nhds
  unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
  dsimp only
  erw [hGraphFirst, hGraphSecond, hNormalFirst, ← hCoordinate, ← hNormal]

theorem test_localSectionExtrinsicCurvatureLinearMap_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : TestOrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : TestEffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    (test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod metric
        displacement secondBoundary secondParameter patch secondCoordinate
          current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      (normalGraphThroatCotangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirstCotangent hSecondCotangent :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)).comp
        (test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
            current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro secondCoordinateVector
  let transition :=
    normalGraphThroatTangentCoordinateTransition period hPeriod
      (orientationDoubleToThroat period hPeriod firstBoundary)
      (orientationDoubleToThroat period hPeriod secondBoundary) current.1
        hFirstTangent hSecondTangent
  let second := transition.symm secondCoordinateVector
  have hSecond : transition second = secondCoordinateVector :=
    transition.apply_symm_apply secondCoordinateVector
  rw [← hSecond]
  simp only [ContinuousLinearMap.comp_apply]
  dsimp only [transition]
  erw [test_throatCoordinateTransition_pairing period hPeriod
    (orientationDoubleToThroat period hPeriod firstBoundary)
    (orientationDoubleToThroat period hPeriod secondBoundary) current.1
      hFirstTangent hSecondTangent hFirstCotangent hSecondCotangent]
  rw [test_localSectionExtrinsicCurvatureContinuousLinearMap_apply,
    test_localSectionExtrinsicCurvatureContinuousLinearMap_apply]
  have hFirstSecond :=
    test_localSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirstTangent hSecondTangent hGraphGerm hNormalGerm
            first second
  have hSecondFirst :=
    test_localSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirstTangent hSecondTangent hGraphGerm hNormalGerm
            second first
  dsimp only at hFirstSecond hSecondFirst
  erw [hFirstSecond, hSecondFirst]

theorem test_localSectionContractedTrace_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : TestOrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : TestEffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    let firstBase : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod firstBoundary, firstParameter)
    let secondBase : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod secondBoundary, secondParameter)
    LinearMap.trace Real ThroatCoverCoordinates
        ((normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement secondBase current).toLinearMap.comp
        (test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate current).toLinearMap) =
      LinearMap.trace Real ThroatCoverCoordinates
        ((normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement firstBase current).toLinearMap.comp
        (test_localSectionExtrinsicCurvatureContinuousLinearMap period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
            current).toLinearMap) := by
  dsimp only
  let firstBase : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod firstBoundary, firstParameter)
  let secondBase : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod secondBoundary, secondParameter)
  let tangentTransition :=
    normalGraphThroatTangentCoordinateTransition period hPeriod firstBase.1
      secondBase.1 current.1 hFirstTangent hSecondTangent
  let cotangentTransition :=
    normalGraphThroatCotangentCoordinateTransition period hPeriod firstBase.1
      secondBase.1 current.1 hFirstCotangent hSecondCotangent
  apply test_contractedTrace_natural
    (tangentTransition := tangentTransition)
    (cotangentTransition := cotangentTransition)
  · exact normalGraphInducedMetricInverseCoordinates_natural period hPeriod
      metric displacement firstBase secondBase current hNonNull hFirstTangent
        hSecondTangent hFirstCotangent hSecondCotangent
  · exact test_localSectionExtrinsicCurvatureLinearMap_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirstTangent hSecondTangent hFirstCotangent
            hSecondCotangent hGraphGerm hNormalGerm

theorem test_localSectionMeanCurvature_eventually_eq_gauss
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
        ∀ hCurrentNonNull :
            NormalGraphNonNullAt period hPeriod metric displacement current.2,
          normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
              hPeriod metric displacement boundary parameter patch coordinate
                current =
            normalGraphCanonicalGaussMeanCurvature period hPeriod metric
              displacement current.2 hCurrentNonNull
                (normalGraphOrientationLocalSection period hPeriod boundary
                  current.1) := by
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
  have hCoordinateReconstruct :=
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hGraph
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
    hCoordinateReconstruct, hGraphReanchor, hNormalReanchor, hFirstTangent,
      hFirstCotangent] with current hCurrentNonNull hProjection hCoordinate
        hGraphGerm hNormalGerm hFirstTangentAt hFirstCotangentAt
  constructor
  · exact hCurrentNonNull
  · intro hCurrentNonNullProof
    let currentBoundary :=
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
          current.2 current hCurrentNonNullProof patch coordinate
            currentCoordinate hFirstTangentAt hSecondTangent hFirstCotangentAt
              hSecondCotangent hGraphGermDynamic hNormalGerm
    have hAtCurrent : patch.coordinateMap currentCoordinate =
        normalGraphOrientationDouble period hPeriod displacement
          (currentBoundary, current.2) := by
      simpa [currentCoordinate, currentBoundary, normalGraphOrientationDouble,
        hCurrentProjection] using hCoordinate
    have hGauss :=
      normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss
        period hPeriod metric displacement current.2 hCurrentNonNullProof
          currentBoundary patch currentCoordinate hAtCurrent
    dsimp only at hGauss
    rw [hCurrentBase] at hGauss
    exact hNaturality.symm.trans hGauss

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
end JanusFormal
