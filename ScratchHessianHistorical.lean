import ScratchHessianGauss

namespace JanusFormal

set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem dependent_section_eq_transport
    {X : Type*} (fiber : X → Type*) {x y : X}
    (h : x = y) (family : (point : X) → fiber point)
    (value : fiber y) (hValue : family y = value) :
    family x = h.symm ▸ value := by
  subst y
  exact hValue

local instance (priority := 30000) historicalOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) historicalOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) historicalEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) historicalEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance (priority := 30000) historicalEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000) historicalEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

/-- Coordinate representative, in an existing holonomic chart, of one
completed candidate graph tangent. -/
def historicalCandidateANormalBoundaryGraphTangentCoordinates
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    TangentSpace
      (modelWithCornersSelf Real
        P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
      coordinate :=
  ∑ row : Fin 4,
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row current boundary •
      pulledRegularFrameVector period hPeriod metric patch row coordinate

set_option backward.isDefEq.respectTransparency false in
/-- The completed regular-frame graph tangent is the historical holonomic
source derivative after the installed orientation-cover tangent equivalence. -/
theorem historical_candidateANormalBoundaryGraphTangent_coordinates
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let sourceVector : TangentSpace throatCoverModelWithCorners boundary :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let targetVector : TangentSpace throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary) :=
      normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
    let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    historicalCandidateANormalBoundaryGraphTangentCoordinates period hPeriod
        metric index
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter)
          boundary patch coordinate =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate targetVector := by
  dsimp only
  classical
  let sourceVector : TangentSpace throatCoverModelWithCorners boundary :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let targetVector : TangentSpace throatCoverModelWithCorners
      (orientationDoubleToThroat period hPeriod boundary) :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
  let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply derivativeEquiv.injective
  change derivativeEquiv.toContinuousLinearMap _ =
    derivativeEquiv.toContinuousLinearMap _
  rw [show derivativeEquiv.toContinuousLinearMap =
      mfderiv (modelWithCornersSelf Real
          P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
        coverModelWithCorners patch.coordinateMap coordinate by
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv_coe (by simp)]
  unfold historicalCandidateANormalBoundaryGraphTangentCoordinates
  rw [map_sum]
  simp_rw [map_smul, coordinateMap_mfderiv_pulledRegularFrameVector]
  have hCandidate :=
    candidateANormalBoundaryGraphTangent_smooth_reconstructs period hPeriod
      metric tensor displacement parameter boundary index
  have hComp := normalGraphOrientationDouble_mfderiv_eq_comp period hPeriod
    displacement parameter boundary sourceVector
  have hTarget : targetVector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod) boundary sourceVector := by
    simpa only [targetVector] using
      (normalBoundaryOrientationTangentEquiv_apply period hPeriod boundary
        sourceVector)
  have hChart : base.1 ∈
      (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hTrivialized :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 targetVector =
        targetVector := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1
            targetVector = targetVector
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa only [base, normalGraphOrientationDouble] using hAt
  rw [normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
    hPeriod displacement base patch coordinate hGraph]
  rw [hTrivialized]
  dsimp only [base]
  rw [hAt, hTarget, ← hComp]
  simpa only [sourceVector] using hCandidate

set_option backward.isDefEq.respectTransparency false in
/-- A smooth scalar has the same directional derivative after pullback through
the installed local orientation section. -/
theorem historical_localSection_mvfderiv
    (coefficient : CutThroatBoundary period hPeriod → Real)
    (hCoefficient : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ coefficient)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    let localSection : MappingTorus (fixedEquatorData period hPeriod) →
        CutThroatBoundary period hPeriod :=
      normalGraphOrientationLocalSection period hPeriod boundary
    let target : MappingTorus (fixedEquatorData period hPeriod) :=
      orientationDoubleToThroat period hPeriod boundary
    let targetVector : TangentSpace throatCoverModelWithCorners target :=
      normalBoundaryOrientationTangentEquiv period hPeriod boundary vector
    mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        coefficient boundary vector =
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        (coefficient ∘ localSection) target targetVector := by
  dsimp only
  let localSection : MappingTorus (fixedEquatorData period hPeriod) →
      CutThroatBoundary period hPeriod :=
    normalGraphOrientationLocalSection period hPeriod boundary
  let target : MappingTorus (fixedEquatorData period hPeriod) :=
    orientationDoubleToThroat period hPeriod boundary
  let targetVector : TangentSpace throatCoverModelWithCorners target :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary vector
  have hSection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners localSection target :=
    (normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary)
      |>.mdifferentiableAt (by simp)
  have hBase : localSection target = boundary :=
    normalGraphOrientationLocalSection_base period hPeriod boundary
  have hCoefficientAt : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) coefficient (localSection target) := by
    rw [hBase]
    exact hCoefficient.mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply target hCoefficientAt hSection targetVector
  have hSectionDerivative :=
    normalGraphOrientationLocalSection_mfderiv_tangentEquiv period hPeriod
      boundary vector
  rw [show targetVector =
      normalBoundaryOrientationTangentEquiv period hPeriod boundary vector by
        rfl,
    hSectionDerivative] at hChain
  rw [hBase] at hChain
  simpa only [localSection, target, targetVector, Function.comp_def] using
    hChain.symm

/-- Regular-frame coordinates of the already installed physical unit normal
inside an existing holonomic chart. -/
def historicalCandidateANormalBoundaryMetricUnitNormalCoordinates
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    TangentSpace
      (modelWithCornersSelf Real
        P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
      coordinate :=
  ∑ row : Fin 4,
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull row
            boundary •
      pulledRegularFrameVector period hPeriod metric patch row coordinate

set_option backward.isDefEq.respectTransparency false in
/-- Those regular-frame coordinates are exactly the historical holonomic
coordinates of the same physical unit normal. -/
theorem historical_candidateANormalBoundaryMetricUnitNormal_coordinates
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    historicalCandidateANormalBoundaryMetricUnitNormalCoordinates period hPeriod
        metric variedMetric displacement parameter hNonNull boundary patch
          coordinate =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt := by
  classical
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply derivativeEquiv.injective
  change derivativeEquiv.toContinuousLinearMap _ =
    derivativeEquiv.toContinuousLinearMap _
  rw [show derivativeEquiv.toContinuousLinearMap =
      mfderiv (modelWithCornersSelf Real
          P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
        coverModelWithCorners patch.coordinateMap coordinate by
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv_coe (by simp)]
  unfold historicalCandidateANormalBoundaryMetricUnitNormalCoordinates
  rw [map_sum]
  simp_rw [map_smul, coordinateMap_mfderiv_pulledRegularFrameVector]
  rw [normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs]
  have hReconstruct :=
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_reconstructs
      period hPeriod metric variedMetric displacement parameter hNonNull boundary
  let regularNormal := fun point :
      MappingTorus (reflectedSphereData period hPeriod) =>
    ∑ row : Fin 4,
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull row
              boundary •
        metric.frame row point
  simpa only [regularNormal] using
    (dependent_section_eq_transport
      (fun point : MappingTorus (reflectedSphereData period hPeriod) =>
        TangentSpace coverModelWithCorners point)
      hAt regularNormal
      (normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary) hReconstruct)

/-- The same regular-frame normal, allowed to move through the already
installed local orientation section and holonomic inverse germ. -/
def historicalCandidateANormalBoundaryMetricUnitNormalField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4 :=
  let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let currentBoundary :=
    normalGraphOrientationLocalSection period hPeriod boundary point
  let currentCoordinate :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, parameter)
  ∑ row : Fin 4,
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull row
            currentBoundary •
      pulledRegularFrameVector period hPeriod metric patch row currentCoordinate

set_option backward.isDefEq.respectTransparency false in
/-- Near the anchor, the moving regular-frame normal is the historical local
normal germ.  This only combines the two existing inverse-germ reconstruction
theorems. -/
theorem historicalCandidateANormalBoundaryMetricUnitNormalField_eventuallyEq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    historicalCandidateANormalBoundaryMetricUnitNormalField period hPeriod
        metric variedMetric displacement parameter hNonNull boundary patch
          coordinate =ᶠ[𝓝 (orientationDoubleToThroat period hPeriod boundary)]
      fun point =>
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod variedMetric displacement boundary parameter patch coordinate
            (point, parameter) := by
  classical
  let throatBase := orientationDoubleToThroat period hPeriod boundary
  let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
    (throatBase, parameter)
  have hSlice : Filter.Tendsto
      (fun point : MappingTorus (fixedEquatorData period hPeriod) =>
        (point, parameter)) (𝓝 throatBase) (𝓝 base) := by
    have h : Filter.Tendsto
        (fun point : MappingTorus (fixedEquatorData period hPeriod) =>
          (point, parameter)) (𝓝 throatBase) (𝓝 (throatBase, parameter)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [base] using h
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, throatBase, normalGraphOrientationDouble] using hAt
  have hCoordinateReconstruct :=
    (normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hGraph).comp_tendsto hSlice
  have hSectionReconstruct :=
    normalGraphOrientationLocalSection_eventually_reconstructs period hPeriod
      boundary
  have hReanchor := hSlice.eventually
    (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventuallyEq_reanchored
      period hPeriod variedMetric displacement parameter hNonNull boundary patch
        coordinate hAt)
  filter_upwards [hCoordinateReconstruct, hSectionReconstruct, hReanchor] with
    point hCoordinateAt hSectionAt hReanchorAt
  let currentBoundary :=
    normalGraphOrientationLocalSection period hPeriod boundary point
  let currentCoordinate :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, parameter)
  have hProjection :
      orientationDoubleToThroat period hPeriod currentBoundary = point := by
    simpa [currentBoundary] using hSectionAt
  have hCurrentAt : patch.coordinateMap currentCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (currentBoundary, parameter) := by
    simpa [currentCoordinate, currentBoundary, normalGraphOrientationDouble,
      hProjection] using hCoordinateAt
  have hCurrentBase :
      (orientationDoubleToThroat period hPeriod currentBoundary, parameter) =
        (point, parameter) := Prod.ext hProjection rfl
  have hCandidate :=
    historical_candidateANormalBoundaryMetricUnitNormal_coordinates period
      hPeriod metric variedMetric displacement parameter hNonNull currentBoundary
        patch currentCoordinate hCurrentAt
  have hBaseEq :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq period
      hPeriod variedMetric displacement parameter hNonNull currentBoundary patch
        currentCoordinate hCurrentAt
  rw [hCurrentBase] at hBaseEq
  have hGermValue := hReanchorAt.eq_of_nhds
  calc
    historicalCandidateANormalBoundaryMetricUnitNormalField period hPeriod
        metric variedMetric displacement parameter hNonNull boundary patch
          coordinate point =
      historicalCandidateANormalBoundaryMetricUnitNormalCoordinates period
        hPeriod metric variedMetric displacement parameter hNonNull
          currentBoundary patch currentCoordinate := by
            rfl
    _ = normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod variedMetric displacement parameter hNonNull currentBoundary
            patch currentCoordinate hCurrentAt := hCandidate
    _ = normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod variedMetric displacement currentBoundary parameter patch
            currentCoordinate (point, parameter) := hBaseEq.symm
    _ = normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod variedMetric displacement boundary parameter patch coordinate
            (point, parameter) := hGermValue.symm

set_option backward.isDefEq.respectTransparency false in
/-- Consequently the historical stored normal derivative is the derivative of
the moving regular-frame representative. -/
theorem historicalCandidateANormalBoundaryMetricUnitNormalField_mfderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (vector : ThroatCoverCoordinates) :
    let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod variedMetric displacement boundary parameter patch coordinate
          base vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real
          P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
        (historicalCandidateANormalBoundaryMetricUnitNormalField period hPeriod
          metric variedMetric displacement parameter hNonNull boundary patch
            coordinate)
        base.1 vector := by
  dsimp only
  let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  rw [normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_base_eq_mfderiv
    period hPeriod variedMetric displacement boundary parameter patch coordinate
      vector]
  have hChart : base.1 ∈ (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector =
        vector := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1 vector =
        vector
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  rw [hVector]
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (historicalCandidateANormalBoundaryMetricUnitNormalField_eventuallyEq
      period hPeriod metric variedMetric displacement parameter hNonNull boundary
        patch coordinate hAt)
  exact congrArg (fun derivative => derivative vector) hDerivative.symm

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end
end JanusFormal
