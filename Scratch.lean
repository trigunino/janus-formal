import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

namespace JanusFormal
namespace Scratch

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open Bundle ContinuousLinearMap Filter MeasureTheory Module TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev OrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev HolonomicVector4 :=
  P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance orientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance orientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

theorem test_spatial_representative_eventually_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ point in 𝓝 base.1, ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun current : EffectiveThroat period hPeriod =>
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate (current, base.2)) point := by
  let localDiffeomorph := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hGraphBase : normalGraph period hPeriod displacement base.2 base.1 ∈
      localDiffeomorph.localInverse.source := by
    rw [← hAt]
    exact localDiffeomorph.localInverse_mem_source
  let sectionMap := fun point : EffectiveThroat period hPeriod => (point, base.2)
  have hSection : ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      sectionMap := contMDiff_id.prodMk contMDiff_const
  have hGraphContinuous : ContinuousAt
      (normalGraph period hPeriod displacement base.2) base.1 := by
    exact ((normalGraph_joint_contMDiff period hPeriod displacement).comp
      hSection).continuous.continuousAt
  have hGraphEventually : ∀ᶠ point in 𝓝 base.1,
      normalGraph period hPeriod displacement base.2 point ∈
        localDiffeomorph.localInverse.source :=
    hGraphContinuous
      (localDiffeomorph.localInverse.open_source.mem_nhds hGraphBase)
  filter_upwards [hGraphEventually] with point hGraphPoint
  have hInverse := localDiffeomorph.localInverse_contMDiffOn.contMDiffAt
    (localDiffeomorph.localInverse.open_source.mem_nhds hGraphPoint)
  have hCoordinateAt : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate) (point, base.2) := by
    exact hInverse.comp (point, base.2)
      (normalGraph_joint_contMDiff period hPeriod displacement).contMDiffAt
  exact ContMDiffAt.comp (f := sectionMap)
    (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
      patch coordinate) point hCoordinateAt hSection.contMDiffAt

theorem test_source_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    (fun sourceCoordinate =>
      localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate sourceCoordinate)
        (normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod
          metric displacement base patch coordinate ambient sourceCoordinate)
        (fderiv Real
          (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
            patch coordinate) sourceCoordinate tangent)) =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1)]
      fun _ => 0 := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let inverse := (extChartAt throatCoverModelWithCorners base.1).symm
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseContinuous : ContinuousAt inverse
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_extChartAt_symm base.1
  have hInverseBase :
      inverse (extChartAt throatCoverModelWithCorners base.1 base.1) =
        base.1 := by
    dsimp only [inverse]
    rw [extChartAt_to_inv]
  have hInverseTendsto : Tendsto inverse
      (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1))
      (𝓝 base.1) := by
    have hTendsto : Tendsto inverse
        (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1))
        (𝓝 (inverse
          (extChartAt throatCoverModelWithCorners base.1 base.1))) :=
      hInverseContinuous
    rw [hInverseBase] at hTendsto
    exact hTendsto
  have hTarget : ∀ᶠ sourceCoordinate in
      𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1),
      sourceCoordinate ∈
        (extChartAt throatCoverModelWithCorners base.1).target :=
    extChartAt_target_mem_nhds base.1
  have hCurrentPoint : ∀ᶠ point in 𝓝 base.1, point ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1)
  have hRepresentative :=
    test_spatial_representative_eventually_contMDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hRightInverse :=
    normalGraphHolonomicInducedMetricInverseCoordinates_eventually_rightInverse
      period hPeriod metric displacement base hNonNull patch coordinate hGraph
  filter_upwards [hTarget, hInverseTendsto.eventually hCurrentPoint,
    hInverseTendsto.eventually hRepresentative,
    hInverseTendsto.eventually hRightInverse] with sourceCoordinate
      hSourceTarget hCurrent hRepresentativeAt hInverse
  have hDerivative :=
    normalGraphHolonomicSourceChartGerm_fderiv_eq_family_of_mem period hPeriod
      displacement base patch coordinate sourceCoordinate hSourceTarget hCurrent
        hRepresentativeAt tangent
  rw [hDerivative]
  exact
    normalGraphHolonomicMetricUnitNormalCoordinates_orthogonal_of_rightInverse
      period hPeriod metric displacement base (inverse sourceCoordinate, base.2)
        patch coordinate ambient hInverse tangent

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

theorem test_gauss_raw_eq_weingarten_raw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second base =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let sourceGerm :=
    normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
      coordinate
  let normalGerm :=
    normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod metric
      displacement base patch coordinate ambient
  let tangentGerm := fun sourceCoordinate =>
    fderiv Real sourceGerm sourceCoordinate second
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSource : ContDiffAt Real ∞ sourceGerm sourceBase := by
    exact normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hNormal : ContDiffAt Real ∞ normalGerm sourceBase := by
    exact
      normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_contDiffAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt
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
  have hOrthogonal := test_source_eventually_orthogonal period hPeriod metric
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
  rw [normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_base period hPeriod
    metric displacement parameter hNonNull boundary patch coordinate hAt]
    at hGaussWeingarten
  rw [normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_fderiv period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt
      first] at hGaussWeingarten
  rw [hTangentDerivative] at hGaussWeingarten
  change
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
          metric displacement base patch coordinate ambient base first +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first) ambient)
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate second) =
      -localMetricCoordinateForm period hPeriod metric patch coordinate ambient
        (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
            displacement base patch coordinate first second +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate second))
    at hGaussWeingarten
  unfold normalGraphHolonomicRawExtrinsicCurvatureCoordinates
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
  dsimp only
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hGraph]
  rw [normalGraphCanonicalHolonomicLocalUnitNormalCoordinates_eq period hPeriod
    metric displacement parameter hNonNull boundary patch coordinate hAt]
  rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  exact hGaussWeingarten

def testLocalMeanFamily
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  Matrix.trace
    (normalGraphInducedInverseMatrixFamily period hPeriod metric displacement
        base current *
      normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient current)

theorem test_inverse_evaluation_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (input output : ThroatCoverCoordinates →L[Real] Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => output
        (normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement base current input)) base := by
  exact contMDiffAt_const.clm_apply
    ((normalGraphInducedMetricInverseCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull).clm_apply contMDiffAt_const)

theorem test_inverse_matrix_entry_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (row column : Fin 3) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphInducedInverseMatrixFamily period hPeriod metric
        displacement base current row column) base := by
  unfold normalGraphInducedInverseMatrixFamily
  simp only [LinearMap.toMatrix_apply]
  apply test_inverse_evaluation_contMDiffAt

theorem test_extrinsic_matrix_entry_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (row column : Fin 3) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod
        metric displacement base patch coordinate ambient current row column)
      base := by
  unfold normalGraphHolonomicExtrinsicCurvatureMatrix
  apply normalGraphHolonomicExtrinsicCurvatureCoordinates_contMDiffAt <;>
    assumption

theorem test_local_mean_family_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (testLocalMeanFamily period hPeriod metric displacement base patch
        coordinate ambient) base := by
  unfold testLocalMeanFamily Matrix.trace
  apply contMDiffAt_finset_sum
  intro row _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply contMDiffAt_finset_sum
  intro column _
  exact (test_inverse_matrix_entry_contMDiffAt period hPeriod metric displacement
    base hNonNull row column).mul
      (test_extrinsic_matrix_entry_contMDiffAt period hPeriod metric displacement
        base hNonNull patch coordinate ambient hAt hSquare column row)

end
end Scratch
end JanusFormal
