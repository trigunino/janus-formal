import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalSource4D

/-! The finite graph acceleration equals the historical holonomic acceleration
plus the pushed-forward derivative of the source generator. Normal contraction
then gives the existing Gauss second form without an agreement assumption. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalAcceleration4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators Topology BoundedContinuousFunction

private theorem connection_sum {Y ι : Type*} [NormedAddCommGroup Y] [NormedSpace Real Y] [Fintype ι]
    (first second : ι → Real) (frame : ι → Y) (derivative : ι → Y →L[Real] Y)
    (connection : Y →ₗ[Real] Y →ₗ[Real] Y) :
    (∑ a, ∑ b, (first a * second b) • (derivative b (frame a) + connection (frame a) (frame b))) =
      (∑ b, second b • derivative b (∑ a, first a • frame a)) +
        connection (∑ a, first a • frame a) (∑ b, second b • frame b) := by
  simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  congr 1
  all_goals
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryGraphAcceleration4D
open P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalSource4D
open P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local notation "Throat" => MappingTorus (fixedEquatorData period hPeriod)
local notation "Source" => ThroatCoverCoordinates
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : ChartedSpace ThroatCoverModel Throat :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Throat :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried in
theorem frameFreeBoundaryGraphAcceleration_eq_historical_add_sourceDerivative
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (boundary : Boundary) (outer inner : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
    let base := (orientationDoubleToThroat period hPeriod boundary, parameter)
    let source := frameFreeBoundaryHistoricalSourceBase period hPeriod boundary
    let first := frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary outer source
    let second := frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary inner source
    (∑ upper : Index, frameFreeBoundaryGraphAccelerationEvaluation period hPeriod metric outer inner upper current boundary •
      finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period hPeriod variedMetric
        displacement base patch coordinate first second +
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod displacement base patch coordinate
        (fderiv Real (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary inner) source first) := by
  dsimp only
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
  let base := (orientationDoubleToThroat period hPeriod boundary, parameter)
  let source := frameFreeBoundaryHistoricalSourceBase period hPeriod boundary
  let sourcePatch := frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary
  let generator := frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary
  let graph := normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch coordinate
  let coefficient (index : TangentIndex) (row : Index) : Source → Real :=
    (fun point => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row current point) ∘ sourcePatch
  let ambient := finiteFramePulledVector period hPeriod frame patch
  have hGraph : ContDiffAt Real ∞ graph source :=
    normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod displacement base patch coordinate hAt
  have hGraphBase : graph source = coordinate :=
    normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base patch coordinate hAt
  have hLocal := sourcePatch.isLocalDiffeomorphAt (modelWithCornersSelf Real Source)
    throatCoverModelWithCorners ∞ (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  have hBoundaryCoefficient (index : TangentIndex) (row : Index) :=
    frameFreeBoundaryGraphTangentEvaluation_smooth_contMDiff period hPeriod metric tensor displacement parameter index row
  have hCoefficient (row : Index) : DifferentiableAt Real (coefficient inner row) source :=
    (((hBoundaryCoefficient inner row).contMDiffAt.comp source hLocal.contMDiffAt).contDiffAt).differentiableAt (by simp)
  have hDF : DifferentiableAt Real (fderiv Real graph) source :=
    ((hGraph.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hReconstruct (index : TangentIndex) := frameFreeBoundaryHistoricalSourceGenerator_eventually_reconstructs
    period hPeriod metric tensor displacement parameter boundary index patch coordinate hAt
  have hCoefficientBase (index : TangentIndex) (row : Index) : coefficient index row source =
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row current boundary := by
    dsimp only [coefficient, Function.comp_apply, sourcePatch, source]
    rw [frameFreeBoundaryHistoricalSourcePatch_base]
  have hVelocity (index : TangentIndex) :
      (∑ row : Index, frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row current boundary •
        ambient row coordinate) = fderiv Real graph source (generator index source) := by
    have h := (hReconstruct index).eq_of_nhds
    change (∑ row : Index, coefficient index row source • ambient row (graph source)) =
      fderiv Real graph source (generator index source) at h
    simpa only [hGraphBase, hCoefficientBase] using h
  have hCoefficientDerivative (row : Index) :
      fderiv Real (coefficient inner row) source (generator outer source) =
        mvfderiv throatCoverModelWithCorners
          (fun point => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner row current point)
          boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period)
            (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary outer) :=
    frameFreeBoundaryHistoricalSourceGenerator_scalarDerivative period hPeriod boundary outer _ (hBoundaryCoefficient inner row)
  have hDerivative := movingFrameDerivative_eq_hessian_add_sourceDerivative
    graph (generator inner) (coefficient inner) ambient source (generator outer source)
    (hGraph.differentiableAt (by simp)) hDF
    ((frameFreeBoundaryHistoricalSourceGenerator_contDiffAt period hPeriod boundary inner).differentiableAt (by simp))
    hCoefficient (fun row => (finiteFramePulledVector_contDiff period hPeriod frame patch row).differentiable (by simp) _)
    (hReconstruct inner)
  simp only [hGraphBase, hCoefficientDerivative, hCoefficientBase] at hDerivative
  have hConnection := connection_sum
    (fun row => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric outer row current boundary)
    (fun row => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner row current boundary)
    (fun row => ambient row coordinate) (fun row => fderiv Real (ambient row) coordinate)
    (localLeviCivitaChristoffelBilinearMap period hPeriod variedMetric patch coordinate)
  rw [hVelocity outer, hVelocity inner] at hConnection
  have hAcceleration := frameFreeBoundaryGraphAccelerationEvaluation_smooth_reconstructs_local
    period hPeriod metric tensor variedMetric hVaried displacement parameter hCurrent outer inner boundary patch coordinate hAt
  dsimp only at hAcceleration
  rw [hAcceleration]
  change (∑ row : Index, _ • ambient row coordinate) +
    (∑ first : Index, ∑ second : Index, _ •
      (fderiv Real (ambient second) coordinate (ambient first coordinate) +
        localLeviCivitaChristoffelBilinearMap period hPeriod variedMetric patch coordinate
          (ambient first coordinate) (ambient second coordinate))) = _
  rw [hConnection, ← add_assoc, ← Finset.sum_add_distrib, hDerivative]
  change (fderiv Real (fderiv Real graph) source (generator outer source) (generator inner source) +
    fderiv Real graph source (fderiv Real (generator inner) source (generator outer source))) +
    localLeviCivitaChristoffelApply period hPeriod variedMetric patch coordinate
      (fderiv Real graph source (generator outer source)) (fderiv Real graph source (generator inner source)) =
    (fderiv Real (fderiv Real graph) source (generator outer source) (generator inner source) +
      localLeviCivitaChristoffelApply period hPeriod variedMetric patch coordinate
        (fderiv Real graph source (generator outer source)) (fderiv Real graph source (generator inner source))) +
    fderiv Real graph source (fderiv Real (generator inner) source (generator outer source))
  exact add_right_comm _ _ _

include hVaried in
/-- Exact agreement with the historical Gauss second form; the tangential
source correction is removed by its proved canonical normal orthogonality. -/
theorem frameFreeBoundaryGraphAcceleration_normal_eq_gauss
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement parameter)
    (boundary : Boundary) (outer inner : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter);
    -localMetricCoordinateForm period hPeriod variedMetric patch coordinate
      (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod variedMetric
        displacement parameter hNonNull boundary patch coordinate hAt)
      (∑ upper : Index, frameFreeBoundaryGraphAccelerationEvaluation period hPeriod metric outer inner upper current boundary •
        finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt period hPeriod variedMetric
        displacement parameter hNonNull boundary patch coordinate hAt
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          ((finiteSmoothThroatGeneratingFrame (doubledPeriod period)
            (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary outer))
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          ((finiteSmoothThroatGeneratingFrame (doubledPeriod period)
            (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary inner)) := by
  dsimp only
  rw [frameFreeBoundaryGraphAcceleration_eq_historical_add_sourceDerivative period hPeriod metric tensor
    variedMetric hVaried displacement parameter hCurrent boundary outer inner patch coordinate hAt]
  rw [map_add, normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_orthogonal period hPeriod
    variedMetric displacement parameter hNonNull boundary patch coordinate hAt, add_zero]
  simp only [frameFreeBoundaryHistoricalSourceGenerator_base,
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalAcceleration4D
