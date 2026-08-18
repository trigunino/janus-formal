import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalCovariantNormalGerm4D

/-!
# Leibniz expansion of the historical normal germ for H10

The historical physical unit normal is already reconstructed from its smooth
regular-frame coefficients.  This gate differentiates that finite
reconstruction along a transported graph generator and identifies the two
Leibniz terms with the installed coefficient derivative and the derivative of
the pulled regular frame.  No normal, connection, frame, chart, boundary datum,
or axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
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
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance historicalNormalLeibnizCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance historicalNormalLeibnizCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalNormalLeibnizOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalNormalLeibnizOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalNormalLeibnizEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalNormalLeibnizEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance (priority := 30000)
    historicalCovariantNormalEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantNormalEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

private theorem mvfderiv_finset_sum_smul_apply
    {index : Type*} [DecidableEq index]
    (indices : Finset index)
    (coefficients : index → EffectiveThroat period hPeriod → Real)
    (vectors : index → EffectiveThroat period hPeriod → CoordinateVector)
    (point : EffectiveThroat period hPeriod)
    (direction : TangentSpace throatCoverModelWithCorners point)
    (hCoefficients : ∀ current,
      MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) (coefficients current) point)
    (hVectors : ∀ current,
      MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector) (vectors current) point) :
    mvfderiv throatCoverModelWithCorners
        (fun current => ∑ currentIndex ∈ indices,
          coefficients currentIndex current • vectors currentIndex current)
        point direction =
      ∑ currentIndex ∈ indices,
        (coefficients currentIndex point •
            mvfderiv throatCoverModelWithCorners (vectors currentIndex)
              point direction +
          mvfderiv throatCoverModelWithCorners (coefficients currentIndex)
              point direction • vectors currentIndex point) := by
  have hDifferentiable : ∀ currentIndices : Finset index,
      MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector)
        (fun current => ∑ currentIndex ∈ currentIndices,
          coefficients currentIndex current • vectors currentIndex current)
        point := by
    intro currentIndices
    induction currentIndices using Finset.induction_on with
    | empty =>
        simpa using
          (contMDiff_const : ContMDiff throatCoverModelWithCorners
            (modelWithCornersSelf Real CoordinateVector) ∞
            (fun _ : EffectiveThroat period hPeriod => (0 : CoordinateVector)))
            |>.mdifferentiableAt (by simp)
    | @insert currentIndex currentIndices hNotMem inductionHypothesis =>
        have hTerm :=
          (hCoefficients currentIndex).smul (hVectors currentIndex)
        have hFunction :
            (fun current => ∑ index ∈ insert currentIndex currentIndices,
              coefficients index current • vectors index current) =
              ((fun current =>
                coefficients currentIndex current • vectors currentIndex current) +
                fun current => ∑ index ∈ currentIndices,
                  coefficients index current • vectors index current) := by
          funext current
          simp only [Finset.sum_insert hNotMem, Pi.add_apply]
        rw [hFunction]
        exact hTerm.add inductionHypothesis
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [mvfderiv_const]
      rfl
  | @insert currentIndex currentIndices hNotMem inductionHypothesis =>
      have hTerm :=
        (hCoefficients currentIndex).smul (hVectors currentIndex)
      have hRest := hDifferentiable currentIndices
      have hAdd := congrArg (fun derivative => derivative direction)
        (mvfderiv_add hTerm hRest)
      have hProduct := congrArg (fun derivative => derivative direction)
        (mvfderiv_smul (hCoefficients currentIndex) (hVectors currentIndex))
      have hAddApply :
          mvfderiv throatCoverModelWithCorners
              (fun current =>
                coefficients currentIndex current • vectors currentIndex current +
                  ∑ index ∈ currentIndices,
                    coefficients index current • vectors index current)
              point direction =
            mvfderiv throatCoverModelWithCorners
                (fun current =>
                  coefficients currentIndex current • vectors currentIndex current)
                point direction +
              mvfderiv throatCoverModelWithCorners
                (fun current => ∑ index ∈ currentIndices,
                  coefficients index current • vectors index current)
                point direction := by
        change mvfderiv throatCoverModelWithCorners
            ((fun current =>
              coefficients currentIndex current • vectors currentIndex current) +
              fun current => ∑ index ∈ currentIndices,
                coefficients index current • vectors index current)
            point direction = _
        simpa only [add_apply] using hAdd
      have hProductApply :
          mvfderiv throatCoverModelWithCorners
              (fun current =>
                coefficients currentIndex current • vectors currentIndex current)
              point direction =
            coefficients currentIndex point •
                mvfderiv throatCoverModelWithCorners (vectors currentIndex)
                  point direction +
              mvfderiv throatCoverModelWithCorners
                  (coefficients currentIndex) point direction •
                vectors currentIndex point := by
        change mvfderiv throatCoverModelWithCorners
            (coefficients currentIndex • vectors currentIndex)
            point direction = _
        exact hProduct
      simp only [Finset.sum_insert hNotMem]
      rw [hAddApply, hProductApply, inductionHypothesis]

set_option backward.isDefEq.respectTransparency false in
/-- Leibniz expansion of the already reconstructed historical normal field
along one transported graph generator. -/
theorem candidateANormalBoundaryMetricUnitNormalField_historical_mvfderiv_expand
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let sourceVector := frame.vectorAt boundary outer
    let targetVector :=
      normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let tangentCoordinate :=
      candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
        metric outer current boundary patch coordinate
    mvfderiv throatCoverModelWithCorners
        (candidateANormalBoundaryMetricUnitNormalField_historical period hPeriod
          metric variedMetric displacement parameter hNonNull boundary patch
            coordinate)
        base.1 targetVector =
      ∑ row : Fin 4,
        (candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter hNonNull
                row boundary •
            fderiv Real
              (pulledRegularFrameVector period hPeriod metric patch row)
              coordinate tangentCoordinate +
          candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
                period hPeriod metric variedMetric displacement parameter hNonNull
                  outer row boundary •
            pulledRegularFrameVector period hPeriod metric patch row coordinate) := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let sourceVector := frame.vectorAt boundary outer
  let targetVector :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let localSection :=
    normalGraphOrientationLocalSection period hPeriod boundary
  let coefficient := fun row : Fin 4 =>
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull row ∘
        localSection
  let coordinateField := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, parameter)
  let vectorField := fun row : Fin 4 => fun point : EffectiveThroat period hPeriod =>
    pulledRegularFrameVector period hPeriod metric patch row
      (coordinateField point)
  let tangentCoordinate :=
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
      metric outer current boundary patch coordinate
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSectionSmooth : ContMDiffAt throatCoverModelWithCorners
      throatCoverModelWithCorners ∞ localSection base.1 :=
    normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary
  have hSectionBase : localSection base.1 = boundary := by
    exact normalGraphOrientationLocalSection_base period hPeriod boundary
  have hCoordinateSmooth : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real CoordinateVector) ∞ coordinateField base.1 := by
    exact ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) base.1
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
        base patch coordinate hGraph)
      ((contMDiff_id.prodMk contMDiff_const).contMDiffAt)
  have hCoordinateBase : coordinateField base.1 = coordinate := by
    exact normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hGraph
  have hChart : base.1 ∈ (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hTargetTrivialized :
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
  have hTangentSource : tangentCoordinate =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate targetVector := by
    simpa only [current, frame, sourceVector, targetVector, base,
      tangentCoordinate] using
      (candidateANormalBoundaryGraphTangentCoordinates_historical_eq_source
        period hPeriod metric tensor displacement parameter boundary outer patch
          coordinate hAt)
  have hCoordinateDerivative :
      mvfderiv throatCoverModelWithCorners coordinateField base.1 targetVector =
        tangentCoordinate := by
    change mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector) coordinateField base.1
          targetVector = tangentCoordinate
    rw [hTangentSource]
    rw [normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family
      period hPeriod displacement base patch coordinate hGraph]
    rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_base_eq_mfderiv]
    rw [hTargetTrivialized]
  have hCoefficientSmooth (row : Fin 4) :
      MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) (coefficient row) base.1 := by
    exact ((candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_contMDiff
      period hPeriod metric variedMetric displacement parameter hNonNull row)
      |>.contMDiffAt.comp base.1 hSectionSmooth).mdifferentiableAt (by simp)
  have hVectorSmooth (row : Fin 4) :
      MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector) (vectorField row) base.1 := by
    have hComposed : ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector) ∞ (vectorField row) base.1 :=
      ContDiff.comp_contMDiffAt
        (pulledRegularFrameVector_contDiff period hPeriod metric patch row)
        hCoordinateSmooth
    exact hComposed.mdifferentiableAt (by simp)
  have hCoefficientValue (row : Fin 4) :
      coefficient row base.1 =
        candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull row
            boundary := by
    simp only [coefficient, Function.comp_apply]
    rw [hSectionBase]
  have hVectorValue (row : Fin 4) :
      vectorField row base.1 =
        pulledRegularFrameVector period hPeriod metric patch row coordinate := by
    simp only [vectorField]
    rw [hCoordinateBase]
  have hCoefficientDerivative (row : Fin 4) :
      mvfderiv throatCoverModelWithCorners (coefficient row) base.1
          targetVector =
        candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            outer row boundary := by
    change mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) (coefficient row) base.1 targetVector = _
    unfold
      candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
    have hDerivative :=
      candidateANormalBoundarySmoothCoefficient_localSection_mfderiv period
        hPeriod
        (candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull row)
        (candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_contMDiff
          period hPeriod metric variedMetric displacement parameter hNonNull row)
        boundary sourceVector
    simpa only [coefficient, localSection, targetVector] using hDerivative.symm
  have hVectorDerivative (row : Fin 4) :
      mvfderiv throatCoverModelWithCorners (vectorField row) base.1
          targetVector =
        fderiv Real
          (pulledRegularFrameVector period hPeriod metric patch row)
          coordinate tangentCoordinate := by
    have hOuter : MDifferentiableAt
        (modelWithCornersSelf Real CoordinateVector)
        (modelWithCornersSelf Real CoordinateVector)
        (pulledRegularFrameVector period hPeriod metric patch row)
        (coordinateField base.1) := by
      exact
        (pulledRegularFrameVector_contDiff period hPeriod metric patch row)
          |>.contMDiff.mdifferentiableAt (by simp)
    have hChain := mfderiv_comp_apply base.1 hOuter
      (hCoordinateSmooth.mdifferentiableAt (by simp)) targetVector
    have hCoordinateMFDerivative :
        mfderiv throatCoverModelWithCorners
            (modelWithCornersSelf Real CoordinateVector) coordinateField base.1
            targetVector = tangentCoordinate := by
      change mvfderiv throatCoverModelWithCorners coordinateField base.1
        targetVector = tangentCoordinate
      exact hCoordinateDerivative
    change mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real CoordinateVector) (vectorField row) base.1
          targetVector = _
    calc
      _ = mfderiv (modelWithCornersSelf Real CoordinateVector)
            (modelWithCornersSelf Real CoordinateVector)
            (pulledRegularFrameVector period hPeriod metric patch row)
            (coordinateField base.1)
            (mfderiv throatCoverModelWithCorners
              (modelWithCornersSelf Real CoordinateVector) coordinateField base.1
              targetVector) := by
          simpa only [vectorField, Function.comp_def] using hChain
      _ = mfderiv (modelWithCornersSelf Real CoordinateVector)
            (modelWithCornersSelf Real CoordinateVector)
            (pulledRegularFrameVector period hPeriod metric patch row)
            (coordinateField base.1) tangentCoordinate := by
          exact congrArg
            (fun direction => mfderiv
              (modelWithCornersSelf Real CoordinateVector)
              (modelWithCornersSelf Real CoordinateVector)
              (pulledRegularFrameVector period hPeriod metric patch row)
              (coordinateField base.1) direction)
            hCoordinateMFDerivative
      _ = _ := by
          rw [mfderiv_eq_fderiv, hCoordinateBase]
          rfl
  have hField :
      candidateANormalBoundaryMetricUnitNormalField_historical period hPeriod
          metric variedMetric displacement parameter hNonNull boundary patch
            coordinate =
        fun point => ∑ row : Fin 4,
          coefficient row point • vectorField row point := by
    rfl
  have hLeibniz := mvfderiv_finset_sum_smul_apply period hPeriod Finset.univ
    coefficient vectorField base.1 targetVector hCoefficientSmooth hVectorSmooth
  simp_rw [hCoefficientValue, hVectorValue, hCoefficientDerivative,
    hVectorDerivative] at hLeibniz
  rw [hField]
  simpa [current, frame, sourceVector, targetVector, base, tangentCoordinate] using
    hLeibniz

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
