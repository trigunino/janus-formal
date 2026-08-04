import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 3000000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter Module TopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev TestEffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TestEffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TestOrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev TestVector4 :=
  P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4

local instance testEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel (TestEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance testEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (TestEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance testEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance testEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (TestEffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance testOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance testOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (TestOrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
private def testTangentSpaceModelCoordinates
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    (I : ModelWithCorners Real E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (point : M) : TangentSpace I point ≃L[Real] E where
  toFun vector := vector
  invFun vector := vector
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private theorem testDependentBilinApply_heq
    {α : Sort _} {β : α → Sort _}
    (f : (point : α) → β point → β point → Real)
    {source target : α} (hBase : source = target)
    {firstSource secondSource : β source}
    {firstTarget secondTarget : β target}
    (hFirst : HEq firstSource firstTarget)
    (hSecond : HEq secondSource secondTarget) :
    HEq (f source firstSource secondSource)
      (f target firstTarget secondTarget) := by
  cases hBase
  cases hFirst
  cases hSecond
  rfl

private theorem test_fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  exact congrArg (fun derivative : E →L[Real] G => derivative direction)
    hDerivative

set_option backward.isDefEq.respectTransparency false in
theorem test_localSectionNormal_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    (fun current => localMetricCoordinateForm period hPeriod metric patch
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
        metric displacement boundary parameter patch coordinate current)
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        base patch coordinate current tangent)) =ᶠ[nhds base] fun _ => 0 := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let lifted := normalGraphOrientationLocalSectionJoint period hPeriod boundary
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hLiftTendsto : Tendsto lifted (nhds base) (nhds (boundary, parameter)) :=
    by
      have hLift :=
        (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
          boundary parameter).continuousAt
      change Tendsto lifted (nhds base) (nhds (lifted base)) at hLift
      have hLiftBase : lifted base = (boundary, parameter) := by
        simpa [lifted, base] using
          (normalGraphOrientationLocalSectionJoint_base period hPeriod boundary
            parameter)
      rw [hLiftBase] at hLift
      exact hLift
  have hAdmissible := hLiftTendsto.eventually
    (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
      metric displacement (boundary, parameter) hNonNull)
  have hFstTendsto : Tendsto Prod.fst (nhds base) (nhds base.1) :=
    continuous_fst.continuousAt
  have hSection :
      (fun current : TestEffectiveThroat period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1))
        =ᶠ[nhds base] Prod.fst := by
    change ((fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) ∘
        Prod.fst) =ᶠ[nhds base] Prod.fst
    exact (normalGraphOrientationLocalSection_eventually_reconstructs period
      hPeriod boundary).comp_tendsto hFstTendsto
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hGraph
  have hDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_eventually_reconstructs
      period hPeriod displacement base patch coordinate hGraph
  have hRight :=
    normalGraphHolonomicLocalInverseDerivative_eventually_rightInverse period
      hPeriod displacement base patch coordinate hGraph
  filter_upwards [hAdmissible, hSection, hCoordinate, hDerivative, hRight] with
    current hCurrentAdmissible hSectionCurrent hCoordinateCurrent
      hDerivativeCurrent hRightCurrent
  rcases hCurrentAdmissible with
    ⟨hCurrent, hTangent, hCotangent, hImage⟩
  let liftedCurrent := lifted current
  have hGraphPoint :
      normalGraphOrientationDouble period hPeriod displacement liftedCurrent =
        normalGraph period hPeriod displacement current.2 current.1 := by
    change normalGraph period hPeriod displacement current.2
        (orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1)) =
      normalGraph period hPeriod displacement current.2 current.1
    exact congrArg (normalGraph period hPeriod displacement current.2)
      hSectionCurrent
  have hIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement (boundary, parameter) liftedCurrent
        hCurrent hTangent hCotangent hImage patch coordinate
  rw [hGraphPoint] at hIntrinsic
  let intrinsicNormal :=
    normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      liftedCurrent.2 hCurrent liftedCurrent.1
  have hIntrinsic' :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement boundary parameter patch coordinate current =
        mfderiv coverModelWithCorners
          (modelWithCornersSelf Real TestVector4)
          (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
          (normalGraph period hPeriod displacement current.2 current.1)
          intrinsicNormal := by
    simpa [intrinsicNormal, liftedCurrent, lifted,
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates] using hIntrinsic
  have hNormalModel := hRightCurrent intrinsicNormal
  have hNormal : HEq
      (mfderiv (modelWithCornersSelf Real TestVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod metric displacement boundary parameter patch coordinate current))
      intrinsicNormal := by
    rw [hIntrinsic']
    exact hNormalModel.heq
  let sourceTangent : ThroatTangentFiber period hPeriod current.1 :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symm current.1 tangent
  let intrinsicTangent :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement current.2) current.1 sourceTangent
  have hCoordinateTangent : HEq
      (mfderiv (modelWithCornersSelf Real TestVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent))
      intrinsicTangent := by
    exact (hDerivativeCurrent tangent).heq
  have hMetric := testDependentBilinApply_heq
    (fun point first second => metric.tensor.tensor point first second)
    hCoordinateCurrent hNormal hCoordinateTangent
  rw [localMetricCoordinateForm_apply]
  change metric.tensor.tensor
      (patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current))
      (mfderiv (modelWithCornersSelf Real TestVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod metric displacement boundary parameter patch coordinate current))
      (mfderiv (modelWithCornersSelf Real TestVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent)) = 0
  rw [eq_of_heq hMetric]
  let physicalTangent : ThroatTangentFiber period hPeriod
      (orientationDoubleToThroat period hPeriod liftedCurrent.1) :=
    hSectionCurrent.symm ▸ sourceTangent
  have hPhysical := normalGraphCanonicalMetricUnitNormal_orthogonal period hPeriod
    metric displacement current.2 hCurrent liftedCurrent.1 physicalTangent
  have hThroatPoint :
      orientationDoubleToThroat period hPeriod liftedCurrent.1 = current.1 := by
    simpa [liftedCurrent, lifted, normalGraphOrientationLocalSectionJoint] using
      hSectionCurrent
  unfold normalGraphOrientationDouble at hPhysical
  rw [hThroatPoint] at hPhysical
  simpa [intrinsicNormal, intrinsicTangent, sourceTangent, physicalTangent,
    liftedCurrent, lifted, normalGraphOrientationLocalSectionJoint] using
      hPhysical

theorem test_localSectionNormalDerivative_apply_base_eq_mfderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (vector : ThroatCoverCoordinates) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate base
          vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real TestVector4)
        (fun point =>
          normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
            hPeriod metric displacement boundary parameter patch coordinate
              (point, parameter)) base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector) := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  have hThroat : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hTarget : representative base ∈
      (trivializationAt TestVector4
        (fun point : TestVector4 =>
          TangentSpace (modelWithCornersSelf Real TestVector4) point)
        (representative base)).baseSet :=
    mem_baseSet_trivializationAt TestVector4
      (fun point : TestVector4 =>
        TangentSpace (modelWithCornersSelf Real TestVector4) point)
      (representative base)
  rw [show normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        base =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) TestVector4
      (fun point : TestVector4 =>
        TangentSpace (modelWithCornersSelf Real TestVector4) point)
      base.1 base.1 (representative base) (representative base)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real TestVector4)
        (fun point => representative (point, base.2)) base.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hThroat hTarget]
  simp [base, representative]

def testLocalSectionNormalSourceGerm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : TestOrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (sourceCoordinate : ThroatCoverCoordinates) : TestVector4 :=
  normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
    metric displacement boundary parameter patch coordinate
      ((extChartAt throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary)).symm sourceCoordinate,
        parameter)

theorem testLocalSectionNormalSourceGerm_contDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    ContDiffAt Real ∞
      (testLocalSectionNormalSourceGerm period hPeriod metric displacement
        boundary parameter patch coordinate)
      (extChartAt throatCoverModelWithCorners throatBase throatBase) := by
  dsimp only
  let throatBase := orientationDoubleToThroat period hPeriod boundary
  let base : TestEffectiveThroat period hPeriod × Real := (throatBase, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  let slice := fun point : TestEffectiveThroat period hPeriod =>
    representative (point, parameter)
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real TestVector4) ∞ representative base := by
    simpa [representative, base, throatBase] using
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : TestEffectiveThroat period hPeriod => (point, parameter))
      throatBase :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real TestVector4) ∞ slice throatBase :=
    ContMDiffAt.comp
      (f := fun point : TestEffectiveThroat period hPeriod => (point, parameter))
      (g := representative) throatBase hRepresentative hSection
  have hSource := (contMDiffAt_iff_source).mp hSlice
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  have hFunction :
      slice ∘ (extChartAt throatCoverModelWithCorners throatBase).symm =
        testLocalSectionNormalSourceGerm period hPeriod metric displacement
          boundary parameter patch coordinate := by
    rfl
  rw [hFunction] at hSource
  exact hSource.contDiffAt

@[simp]
theorem testLocalSectionNormalSourceGerm_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    testLocalSectionNormalSourceGerm period hPeriod metric displacement boundary
        parameter patch coordinate
          (extChartAt throatCoverModelWithCorners throatBase throatBase) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  dsimp only
  unfold testLocalSectionNormalSourceGerm
  rw [extChartAt_to_inv]
  exact normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq
    period hPeriod metric displacement parameter hNonNull boundary patch
      coordinate hAt

theorem testLocalSectionNormalSourceGerm_fderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    let base : TestEffectiveThroat period hPeriod × Real :=
      (throatBase, parameter)
    fderiv Real
        (testLocalSectionNormalSourceGerm period hPeriod metric displacement
          boundary parameter patch coordinate)
        (extChartAt throatCoverModelWithCorners throatBase throatBase) tangent =
      normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate base
          tangent := by
  dsimp only
  let throatBase := orientationDoubleToThroat period hPeriod boundary
  let base : TestEffectiveThroat period hPeriod × Real := (throatBase, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  let slice := fun point : TestEffectiveThroat period hPeriod =>
    representative (point, parameter)
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real TestVector4) ∞ representative base := by
    simpa [representative, base, throatBase] using
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : TestEffectiveThroat period hPeriod => (point, parameter))
      throatBase :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real TestVector4) ∞ slice throatBase :=
    ContMDiffAt.comp
      (f := fun point : TestEffectiveThroat period hPeriod => (point, parameter))
      (g := representative) throatBase hRepresentative hSection
  rw [test_localSectionNormalDerivative_apply_base_eq_mfderiv period hPeriod
    metric displacement boundary parameter patch coordinate tangent]
  have hChart : throatBase ∈ (chartAt ThroatCoverModel throatBase).source :=
    mem_chart_source ThroatCoverModel throatBase
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) throatBase).symm throatBase tangent =
        tangent := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) throatBase).symmL Real throatBase
            tangent = tangent
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  rw [hVector]
  rw [(hSlice.mdifferentiableAt (by simp)).mfderiv]
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, fderivWithin_univ]
  simp [testLocalSectionNormalSourceGerm, writtenInExtChartAt,
    Function.comp_def, slice, representative, throatBase, base]
  rfl

theorem testLocalSectionNormalSourceGerm_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    (fun sourceCoordinate =>
      localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate sourceCoordinate)
        (testLocalSectionNormalSourceGerm period hPeriod metric displacement
          boundary parameter patch coordinate sourceCoordinate)
        (fderiv Real
          (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
            patch coordinate) sourceCoordinate tangent)) =ᶠ[
          nhds (extChartAt throatCoverModelWithCorners base.1 base.1)]
      fun _ => 0 := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let inverse := (extChartAt throatCoverModelWithCorners base.1).symm
  let sourceMap := fun sourceCoordinate : ThroatCoverCoordinates =>
    (inverse sourceCoordinate, base.2)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseContinuous : ContinuousAt inverse
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_extChartAt_symm base.1
  have hInverseBase :
      inverse (extChartAt throatCoverModelWithCorners base.1 base.1) = base.1 := by
    dsimp only [inverse]
    rw [extChartAt_to_inv]
  have hInverseTendsto : Tendsto inverse
      (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
      (nhds base.1) := by
    have hTendsto : Tendsto inverse
        (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
        (nhds (inverse
          (extChartAt throatCoverModelWithCorners base.1 base.1))) :=
      hInverseContinuous
    rw [hInverseBase] at hTendsto
    exact hTendsto
  have hSourceMapTendsto : Tendsto sourceMap
      (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
      (nhds base) := by
    have hConst : Tendsto
        (fun _ : ThroatCoverCoordinates => base.2)
        (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
        (nhds base.2) := tendsto_const_nhds
    have hPair := hInverseTendsto.prodMk hConst
    have hBaseFilter : nhds base = nhds base.1 ×ˢ nhds base.2 := by
      rw [← Prod.eta base]
      exact nhds_prod_eq
    rw [hBaseFilter]
    simpa [sourceMap] using hPair
  have hOrthogonal :=
    (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventually_orthogonal
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt tangent).comp_tendsto hSourceMapTendsto
  have hTarget : ∀ᶠ sourceCoordinate in
      nhds (extChartAt throatCoverModelWithCorners base.1 base.1),
      sourceCoordinate ∈
        (extChartAt throatCoverModelWithCorners base.1).target :=
    extChartAt_target_mem_nhds base.1
  have hCurrentPoint : ∀ᶠ point in nhds base.1, point ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1)
  have hRepresentative :=
    normalGraphHolonomicSpatialRepresentative_eventually_contMDiffAt period
      hPeriod displacement base patch coordinate hGraph
  filter_upwards [hOrthogonal, hTarget,
    hInverseTendsto.eventually hCurrentPoint,
    hInverseTendsto.eventually hRepresentative] with sourceCoordinate
      hOrthogonalAt hSourceTarget hCurrent hRepresentativeAt
  have hDerivative :=
    normalGraphHolonomicSourceChartGerm_fderiv_eq_family_of_mem period hPeriod
      displacement base patch coordinate sourceCoordinate hSourceTarget hCurrent
        hRepresentativeAt tangent
  rw [hDerivative]
  simpa [testLocalSectionNormalSourceGerm,
    normalGraphHolonomicSourceChartGerm, sourceMap, inverse, base] using
      hOrthogonalAt

theorem test_localSectionRawExtrinsicCurvature_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate
          first second base =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second := by
  dsimp only
  let base : TestEffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let sourceGerm :=
    normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
      coordinate
  let normalGerm :=
    testLocalSectionNormalSourceGerm period hPeriod metric displacement boundary
      parameter patch coordinate
  let tangentGerm := fun sourceCoordinate =>
    fderiv Real sourceGerm sourceCoordinate second
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSource : ContDiffAt Real ∞ sourceGerm sourceBase := by
    exact normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hNormal : ContDiffAt Real ∞ normalGerm sourceBase := by
    exact testLocalSectionNormalSourceGerm_contDiffAt period hPeriod metric
      displacement parameter hNonNull boundary patch coordinate hAt
  have hSourceC2 : ContDiffAt Real 2 sourceGerm sourceBase :=
    hSource.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFDeriv : DifferentiableAt Real (fderiv Real sourceGerm) sourceBase :=
    (hSourceC2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hTangent : DifferentiableAt Real tangentGerm sourceBase :=
    hFDeriv.clm_apply (differentiableAt_const second)
  have hOrthogonal :=
    testLocalSectionNormalSourceGerm_eventually_orthogonal period hPeriod metric
      displacement parameter hNonNull boundary patch coordinate hAt second
  have hGaussWeingarten :=
    localMetric_gauss_weingarten_of_eventually_orthogonal period hPeriod metric
      patch sourceGerm normalGerm tangentGerm sourceBase first
        (hSource.differentiableAt (by simp))
        (hNormal.differentiableAt (by simp)) hTangent hOrthogonal
  have hTangentDerivative :
      fderiv Real tangentGerm sourceBase first =
        normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate first second := by
    unfold normalGraphHolonomicSourceSecondDerivativeCoordinatesAt
    exact test_fderiv_continuousLinearMap_apply_const
      (fderiv Real sourceGerm) sourceBase first second hFDeriv
  dsimp only [sourceGerm, sourceBase, normalGerm, tangentGerm]
    at hGaussWeingarten
  rw [normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base
    patch coordinate hGraph] at hGaussWeingarten
  rw [testLocalSectionNormalSourceGerm_base period hPeriod metric displacement
    parameter hNonNull boundary patch coordinate hAt] at hGaussWeingarten
  rw [testLocalSectionNormalSourceGerm_fderiv period hPeriod metric displacement
    parameter hNonNull boundary patch coordinate hAt first]
    at hGaussWeingarten
  rw [hTangentDerivative] at hGaussWeingarten
  change
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            base first +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
              hPeriod metric displacement parameter hNonNull boundary patch
                coordinate hAt))
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate second) =
      -localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary patch
            coordinate hAt)
        (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
            displacement base patch coordinate first second +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate second))
    at hGaussWeingarten
  unfold
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
  dsimp only
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hGraph]
  rw [normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt]
  rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  exact hGaussWeingarten

theorem test_localSectionExtrinsicCurvatureMatrix_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix period
        hPeriod metric displacement boundary parameter patch coordinate base =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  dsimp only
  ext row column
  unfold normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  rw [test_localSectionRawExtrinsicCurvature_base_eq_gauss period hPeriod metric
      displacement parameter hNonNull boundary patch coordinate hAt,
    test_localSectionRawExtrinsicCurvature_base_eq_gauss period hPeriod metric
      displacement parameter hNonNull boundary patch coordinate hAt]

theorem test_localSectionMeanCurvatureFamily_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : TestOrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : TestEffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement boundary parameter patch coordinate base =
      normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull boundary := by
  dsimp only
  rw [normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily,
    normalGraphInducedInverseMatrixFamily_base,
    test_localSectionExtrinsicCurvatureMatrix_base_eq_gauss]
  unfold normalGraphCanonicalGaussMeanCurvature
  exact normalGraphCanonicalHolonomicGaussMeanCurvatureAt_chart_independent
    period hPeriod metric displacement parameter hNonNull boundary patch
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      coordinate
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      hAt
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
end JanusFormal
