import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryGraphAcceleration4D
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-! The genuine historical source chart lifted through the local orientation
section. Source generators are pulled back by its inverse differential. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalSource4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators Topology BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
open P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeSpatialJets4D
open P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local notation "Throat" => MappingTorus (fixedEquatorData period hPeriod)
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "Source" => ThroatCoverCoordinates
local notation "SourceModel" => modelWithCornersSelf Real Source
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
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod

private def historicalThroatChart (point : Throat) :
    PartialDiffeomorph throatCoverModelWithCorners SourceModel Throat Source ∞ where
  toPartialEquiv := extChartAt throatCoverModelWithCorners point
  open_source := isOpen_extChartAt_source point
  open_target := isOpen_extChartAt_target point
  contMDiffOn_toFun := by simpa only [extChartAt_source] using
    (contMDiffOn_extChartAt (I := throatCoverModelWithCorners) (x := point) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm point

def frameFreeBoundaryHistoricalSourcePatch (boundary : Boundary) :
    PartialDiffeomorph SourceModel throatCoverModelWithCorners Source Boundary ∞ :=
  (historicalThroatChart period hPeriod (orientationDoubleToThroat period hPeriod boundary)).symm.trans
    (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary).localInverse

def frameFreeBoundaryHistoricalSourceBase (boundary : Boundary) : Source :=
  extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)
    (orientationDoubleToThroat period hPeriod boundary)

theorem frameFreeBoundaryHistoricalSourcePatch_base_mem (boundary : Boundary) :
    frameFreeBoundaryHistoricalSourceBase period hPeriod boundary ∈
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).source := by
  change frameFreeBoundaryHistoricalSourceBase period hPeriod boundary ∈
      (extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)).target ∧
    (extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)).symm
      (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary) ∈
        (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary).localInverse.source
  refine ⟨mem_extChartAt_target _, ?_⟩
  change (extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)).symm
    (extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)
      (orientationDoubleToThroat period hPeriod boundary)) ∈
        (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary).localInverse.source
  rw [extChartAt_to_inv]
  exact (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary).localInverse_mem_source

@[simp] theorem frameFreeBoundaryHistoricalSourcePatch_base (boundary : Boundary) :
    frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary
      (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary) = boundary := by
  change normalGraphOrientationLocalSection period hPeriod boundary
    ((extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)).symm
      (extChartAt throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod boundary)
        (orientationDoubleToThroat period hPeriod boundary))) = boundary
  rw [extChartAt_to_inv, normalGraphOrientationLocalSection_base]

def frameFreeBoundaryHistoricalSourceGenerator (boundary : Boundary) (index : TangentIndex) : Source → Source :=
  VectorField.mpullback SourceModel throatCoverModelWithCorners
    (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary)
    (fun point => (throatFrame).vectorAt point index)

theorem frameFreeBoundaryHistoricalSourceGenerator_contDiffAt
    (boundary : Boundary) (index : TangentIndex) :
    ContDiffAt Real ∞ (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index)
      (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary) := by
  let patch := frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary
  have hLocal := patch.isLocalDiffeomorphAt SourceModel throatCoverModelWithCorners ∞
    (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  apply contMDiffAt_vectorSpace_iff_contDiffAt.mp
  apply ((throatFrame).contMDiff_vector index).contMDiffAt.mpullback_vectorField_preimage
    hLocal.contMDiffAt
  · exact ⟨hLocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · simp

theorem frameFreeBoundaryHistoricalSourceGenerator_pushforward
    (boundary : Boundary) (index : TangentIndex) (source : Source)
    (hSource : source ∈ (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).source) :
    mfderiv SourceModel throatCoverModelWithCorners
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary) source
      (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index source) =
      (throatFrame).vectorAt (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary source) index := by
  have hLocal := (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).isLocalDiffeomorphAt
    SourceModel throatCoverModelWithCorners ∞ hSource
  have hInverse : (mfderiv SourceModel throatCoverModelWithCorners
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary) source).IsInvertible :=
    ⟨hLocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  exact hInverse.self_apply_inverse _

theorem frameFreeBoundaryHistoricalSourceGenerator_scalarDerivative
    (boundary : Boundary) (index : TangentIndex) (field : Boundary → Real)
    (hField : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ field) :
    fderiv Real (field ∘ frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary)
      (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary)
      (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index
        (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary)) =
      mvfderiv throatCoverModelWithCorners field boundary ((throatFrame).vectorAt boundary index) := by
  let source := frameFreeBoundaryHistoricalSourceBase period hPeriod boundary
  have hLocal := (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).isLocalDiffeomorphAt
    SourceModel throatCoverModelWithCorners ∞ (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  have hChain := mfderiv_comp_apply source (hField.mdifferentiableAt (by simp))
    (hLocal.mdifferentiableAt (by simp))
    (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index source)
  rw [mfderiv_eq_fderiv, frameFreeBoundaryHistoricalSourceGenerator_pushforward period hPeriod boundary index
    source (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)] at hChain
  have hBase : (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).toPartialEquiv source = boundary :=
    frameFreeBoundaryHistoricalSourcePatch_base period hPeriod boundary
  erw [hBase] at hChain
  rw [candidateANormalBoundary_mvfderiv_real_eq_mfderiv]
  exact hChain

theorem frameFreeBoundaryHistoricalSourceGenerator_base (boundary : Boundary) (index : TangentIndex) :
    frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index
      (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary) =
    normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary index) := by
  let point := orientationDoubleToThroat period hPeriod boundary
  let source := frameFreeBoundaryHistoricalSourceBase period hPeriod boundary
  let inverse := (extChartAt throatCoverModelWithCorners point).symm
  have hInverseLocal := (historicalThroatChart period hPeriod point).symm.isLocalDiffeomorphAt
    SourceModel throatCoverModelWithCorners ∞ (mem_extChartAt_target point)
  have hInverseDerivative (vector : Source) :
      mfderiv SourceModel throatCoverModelWithCorners inverse source vector = vector := by
    have h := congrArg (fun derivative => derivative vector)
      (mfderivWithin_range_extChartAt_symm (I := throatCoverModelWithCorners) (x := point))
    have hRange : Set.range throatCoverModelWithCorners = Set.univ := by ext x; simp
    rw [hRange, mfderivWithin_univ] at h
    change mfderiv SourceModel throatCoverModelWithCorners inverse source vector = vector at h
    exact h
  have hSection : MDifferentiableAt throatCoverModelWithCorners throatCoverModelWithCorners
      (normalGraphOrientationLocalSection period hPeriod boundary) (inverse source) := by
    simpa only [inverse, source, point, frameFreeBoundaryHistoricalSourceBase, extChartAt_to_inv] using
      (normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary).mdifferentiableAt (by simp)
  have hMap (vector : Source) : mfderiv SourceModel throatCoverModelWithCorners
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary) source vector =
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (normalGraphOrientationLocalSection period hPeriod boundary) point vector := by
    have h := mfderiv_comp_apply source hSection (hInverseLocal.mdifferentiableAt (by simp)) vector
    change mfderiv SourceModel throatCoverModelWithCorners
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary) source vector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (normalGraphOrientationLocalSection period hPeriod boundary) (inverse source)
        (mfderiv SourceModel throatCoverModelWithCorners inverse source vector) at h
    erw [hInverseDerivative] at h
    have hInverseBase : inverse source = point := extChartAt_to_inv point
    erw [hInverseBase] at h
    exact h
  have hLocal := (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).isLocalDiffeomorphAt
    SourceModel throatCoverModelWithCorners ∞ (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  have hInvertible : (mfderiv SourceModel throatCoverModelWithCorners
      (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary) source).IsInvertible :=
    ⟨hLocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  apply hInvertible.injective
  rw [frameFreeBoundaryHistoricalSourceGenerator_pushforward period hPeriod boundary index source
    (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)]
  erw [hMap]
  have hBase : (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).toPartialEquiv source = boundary :=
    frameFreeBoundaryHistoricalSourcePatch_base period hPeriod boundary
  erw [hBase]
  exact
    (normalGraphOrientationLocalSection_mfderiv_tangentEquiv period hPeriod boundary
      ((throatFrame).vectorAt boundary index)).symm

/-- The graph germ in the historical source chart is the actual lifted graph
on a neighborhood, so its derivative can be compared there. -/
theorem frameFreeBoundaryHistoricalSourcePatch_eventually_graph
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    (fun source => patch.coordinateMap (normalGraphHolonomicSourceChartGerm period hPeriod displacement
      (orientationDoubleToThroat period hPeriod boundary, parameter) patch coordinate source)) =ᶠ[
        𝓝 (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary)]
      (fun source => normalGraphOrientationDouble period hPeriod displacement
        (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary source, parameter)) := by
  let point := orientationDoubleToThroat period hPeriod boundary
  let inverse := (extChartAt throatCoverModelWithCorners point).symm
  let sourceBase := frameFreeBoundaryHistoricalSourceBase period hPeriod boundary
  have hInverse : ContinuousAt inverse sourceBase := by
    have hSmooth := contMDiffWithinAt_extChartAt_symm_range_self
      (I := throatCoverModelWithCorners) (n := ∞) point
    have hRange : Set.range throatCoverModelWithCorners = Set.univ := by ext x; simp
    rw [hRange, contMDiffWithinAt_univ] at hSmooth
    exact hSmooth.continuousAt
  have hTendsto : Filter.Tendsto (fun source => (inverse source, parameter))
      (𝓝 sourceBase) (𝓝 (point, parameter)) := by
    have h := hInverse.prodMk (continuousAt_const (y := parameter))
    change Filter.Tendsto (fun source => (inverse source, parameter))
      (𝓝 sourceBase) (𝓝 (inverse sourceBase, parameter)) at h
    have hBase : inverse sourceBase = point := extChartAt_to_inv point
    rw [hBase] at h
    exact h
  have hGraph := (normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
    displacement (point, parameter) patch coordinate hAt).comp_tendsto hTendsto
  have hDomain := (frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary).open_source.mem_nhds
    (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  filter_upwards [hGraph, hDomain] with source hGraphSource hDomainSource
  have hSection := (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary).localInverse_right_inv
    hDomainSource.2
  change patch.coordinateMap (normalGraphHolonomicCoordinateGerm period hPeriod displacement
    (point, parameter) patch coordinate (inverse source, parameter)) = _
  exact hGraphSource.trans (congrArg (normalGraph period hPeriod displacement parameter) hSection.symm)

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

theorem frameFreeBoundaryGraphTangentEvaluation_smooth_contMDiff (index : TangentIndex) (row : Index) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun boundary => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row
        (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary) := by
  have hHorizontal := frameFreeBoundaryHorizontalCoefficient_contMDiff period hPeriod frame metric index row
  have hVertical := frameFreeBoundaryVerticalCoefficient_contMDiff period hPeriod frame metric row
  exact (frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff period hPeriod _ hHorizontal displacement parameter).add
    ((frameFreeBoundaryLatitudeSpatialFirst_smooth_contMDiff period hPeriod displacement parameter index).mul
      (frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff period hPeriod _ hVertical displacement parameter))

/-- The actual completed tangent coefficients reconstruct the derivative of
the historical graph germ on a neighborhood, with the genuinely pulled-back
source generator. This equality is proved, not supplied as an agreement input. -/
theorem frameFreeBoundaryHistoricalSourceGenerator_eventually_reconstructs
    (boundary : Boundary) (index : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let sourcePatch := frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary
    let graph := normalGraphHolonomicSourceChartGerm period hPeriod displacement
      (orientationDoubleToThroat period hPeriod boundary, parameter) patch coordinate
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
    (fun source => ∑ row : Index,
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row current (sourcePatch source) •
        finiteFramePulledVector period hPeriod frame patch row (graph source)) =ᶠ[
          𝓝 (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary)]
      (fun source => fderiv Real graph source
        (frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index source)) := by
  dsimp only
  let sourcePatch := frameFreeBoundaryHistoricalSourcePatch period hPeriod boundary
  let graph := normalGraphHolonomicSourceChartGerm period hPeriod displacement
    (orientationDoubleToThroat period hPeriod boundary, parameter) patch coordinate
  let actualGraph := fun point : Boundary => normalGraphOrientationDouble period hPeriod displacement (point, parameter)
  have hGraph := frameFreeBoundaryHistoricalSourcePatch_eventually_graph period hPeriod
    displacement parameter boundary patch coordinate hAt
  have hGraphSmooth : ContDiffAt Real ∞ graph (frameFreeBoundaryHistoricalSourceBase period hPeriod boundary) :=
    normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod displacement
      (orientationDoubleToThroat period hPeriod boundary, parameter) patch coordinate hAt
  have hGraphEventually := (hGraphSmooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by decide)).eventually (by decide)
  have hDomain := sourcePatch.open_source.mem_nhds (frameFreeBoundaryHistoricalSourcePatch_base_mem period hPeriod boundary)
  have hActualGraph : ContMDiff throatCoverModelWithCorners coverModelWithCorners ∞ actualGraph :=
    (normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp (contMDiff_id.prodMk contMDiff_const)
  filter_upwards [hGraph, hGraph.eventuallyEq_nhds, hGraphEventually, hDomain]
    with source hPoint hEqual hGraphAt hSource
  let vector := frameFreeBoundaryHistoricalSourceGenerator period hPeriod boundary index source
  let derivative : (Fin 4 → Real) →L[Real] CoverCoordinates :=
    mfderiv (modelWithCornersSelf Real (Fin 4 → Real)) coverModelWithCorners patch.coordinateMap (graph source)
  have hPushFrame (row : Index) : derivative (finiteFramePulledVector period hPeriod frame patch row (graph source)) =
      (frame).vectorAt (patch.coordinateMap (graph source)) row :=
    coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch (graph source) row
  let derivativeEquiv := (patch.coordinateMap_isLocalDiffeomorph (graph source)).mfderivToContinuousLinearEquiv (by simp)
  apply derivativeEquiv.injective
  change derivative (∑ row : Index, _ • _) = derivative (fderiv Real graph source vector)
  rw [map_sum]
  dsimp only [graph] at hPushFrame
  simp only [map_smul, hPushFrame]
  rw [hPoint]
  have hReconstruct := frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs period hPeriod metric
    tensor displacement parameter (sourcePatch source) index
  have hLocal := sourcePatch.isLocalDiffeomorphAt SourceModel throatCoverModelWithCorners ∞ hSource
  have hChainActual := mfderiv_comp_apply source (hActualGraph.mdifferentiableAt (by simp))
    (hLocal.mdifferentiableAt (by simp)) vector
  have hChainCoordinate := mfderiv_comp_apply source
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp))
    (hGraphAt.contMDiffAt.mdifferentiableAt (by norm_num)) vector
  rw [mfderiv_eq_fderiv] at hChainCoordinate
  have hEqualDerivativeMap :=
    Filter.EventuallyEq.mfderiv_eq (I := SourceModel) (I' := coverModelWithCorners) hEqual
  have hEqualDerivative := congrArg (fun L : Source →L[Real] CoverCoordinates => L vector)
    hEqualDerivativeMap
  have hPush := frameFreeBoundaryHistoricalSourceGenerator_pushforward period hPeriod boundary index source hSource
  exact hReconstruct.trans ((congrArg (mfderiv throatCoverModelWithCorners coverModelWithCorners
    actualGraph (sourcePatch source)) hPush.symm).trans
      (hChainActual.symm.trans (hEqualDerivative.symm.trans hChainCoordinate)))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalSource4D
