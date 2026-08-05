import ScratchHessian

namespace JanusFormal

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance nextCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance nextCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) nextOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) nextOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) nextEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) nextEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- Smooth-core boundary regularity of each completed graph-tangent
coefficient. -/
theorem next_candidateANormalBoundaryGraphTangentRegularFrameCoefficient_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (inner : NormalBoundaryTangentIndex period hPeriod) (row : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let latitude : CutThroatBoundary period hPeriod → Real := fun point =>
    Real.arctan (parameter *
      normalDisplacementOrientationScalar period hPeriod displacement point)
  let slope : CutThroatBoundary period hPeriod → Real := fun point =>
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
      period hPeriod metric inner current point
  let horizontal : CutThroatBoundary period hPeriod × Real → Real :=
    normalBoundaryLatitudeHorizontalRegularFrameCoefficient
      period hPeriod metric inner row
  let vertical : CutThroatBoundary period hPeriod × Real → Real :=
    normalBoundaryLatitudeVerticalRegularFrameCoefficient
      period hPeriod metric row
  let horizontalGraph : CutThroatBoundary period hPeriod → Real := fun point =>
    horizontal (point, latitude point)
  let verticalGraph : CutThroatBoundary period hPeriod → Real := fun point =>
    vertical (point, latitude point)
  let graphCoefficient : CutThroatBoundary period hPeriod → Real :=
    horizontalGraph + slope * verticalGraph
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hLatitudeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude := by
    exact Real.contDiff_arctan.contMDiff.comp
      (contMDiff_const.mul
        (normalDisplacementOrientationScalar_contMDiff
          period hPeriod displacement))
  have hHorizontalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ horizontalGraph :=
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric inner row).comp
        (contMDiff_id.prodMk hLatitudeSmooth)
  have hVerticalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ verticalGraph :=
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row).comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hSlopeAt (point : CutThroatBoundary period hPeriod) :
      slope point = mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point inner) :=
    test_candidateANormalBoundaryLatitudeSpatialFirst_smooth
      period hPeriod metric tensor displacement parameter point inner
  let latitudeField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    { toFun := latitude
      contMDiff_toFun := hLatitudeSmooth }
  have hSlopeFunction : slope =
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        latitudeField inner).toFun := by
    funext point
    rw [hSlopeAt]
    change mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point inner) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame latitudeField point inner
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hSlopeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ slope := by
    rw [hSlopeFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      latitudeField inner).contMDiff_toFun
  have hCoefficient :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point) = graphCoefficient := by
    funext point
    unfold graphCoefficient horizontalGraph verticalGraph
    change
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point =
        horizontal (point, latitude point) +
          slope point * vertical (point, latitude point)
    rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
    change horizontal (point, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod point
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) *
            vertical (point, Real.arctan (parameter *
              normalBoundaryC2JetCoreValueAt period hPeriod point
                (smoothNormalDisplacementToBoundaryC2JetCore
                  period hPeriod displacement)))) = _
    unfold latitude slope
      candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    simp only [BoundedContinuousFunction.mul_apply]
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
          metric current point =
        parameter * normalBoundaryC2JetCoreValueAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) by rfl]
    rw [normalBoundaryC2ScaledRawSpatialFirst_apply,
      normalBoundaryC2JetCoreValueAt_smooth]
    have hCurrentNormal : current.1.2 =
        smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
          displacement := rfl
    rw [hCurrentNormal]
    ring
  rw [hCoefficient]
  exact hHorizontalGraphSmooth.add (hSlopeSmooth.mul hVerticalGraphSmooth)

set_option backward.isDefEq.respectTransparency false in
/-- Smooth-core boundary regularity of each completed actual-metric
coefficient. -/
theorem next_candidateANormalBoundaryActualMetricMatrix_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (row column : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) row column point) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let graph : CutThroatBoundary period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) := fun point =>
    normalGraphOrientationDouble period hPeriod displacement (point, parameter)
  let field := test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
    tensor row column
  have hFunction :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column point) = field ∘ graph := by
    funext point
    unfold field graph current
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_existing]
    change regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column
        (normalBoundaryC2Graph period hPeriod
          (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
            displacement) parameter point) = _
    rw [normalBoundaryC2Graph_smooth]
    exact test_regularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
      period hPeriod metric tensor row column _
  rw [hFunction]
  exact field.contMDiff_toFun.comp
    ((normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp
      (contMDiff_id.prodMk contMDiff_const))

private theorem next_mvfderiv_finset_sum_apply
    {index : Type*} [DecidableEq index]
    (indices : Finset index)
    (functions : index → CutThroatBoundary period hPeriod → Real)
    (hFunctions : ∀ current, ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (functions current))
    (point : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    mvfderiv throatCoverModelWithCorners
        (fun current => ∑ currentIndex ∈ indices,
          functions currentIndex current) point vector =
      ∑ currentIndex ∈ indices,
        mvfderiv throatCoverModelWithCorners
          (functions currentIndex) point vector := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [mvfderiv_const]
      rfl
  | @insert currentIndex indices hNotMem inductionHypothesis =>
      have hCurrent : MDifferentiableAt throatCoverModelWithCorners
          (modelWithCornersSelf Real Real) (functions currentIndex) point :=
        (hFunctions currentIndex).mdifferentiableAt (by simp)
      have hSum : MDifferentiableAt throatCoverModelWithCorners
          (modelWithCornersSelf Real Real)
          (fun current => ∑ index ∈ indices, functions index current) point := by
        exact (ContMDiff.sum fun index _ => hFunctions index)
          |>.mdifferentiableAt (by simp)
      have hAdd := congrArg (fun derivative => derivative vector)
        (mvfderiv_add hCurrent hSum)
      simp only [Finset.sum_insert hNotMem]
      rw [show mvfderiv throatCoverModelWithCorners
            (fun current => functions currentIndex current +
              ∑ index ∈ indices, functions index current) point vector =
          mvfderiv throatCoverModelWithCorners
              (functions currentIndex) point vector +
            mvfderiv throatCoverModelWithCorners
              (fun current => ∑ index ∈ indices, functions index current)
                point vector by
          change mvfderiv throatCoverModelWithCorners
              (functions currentIndex +
                fun current => ∑ index ∈ indices, functions index current)
                point vector = _
          simpa only [add_apply] using hAdd]
      rw [inductionHypothesis]

set_option backward.isDefEq.respectTransparency false in
/-- Differentiated regular-frame orthogonality on the smooth admissible
core.  The only derivatives left are those already stored by the completed
metric and graph jets, plus the derivative of the historical physical normal. -/
theorem next_candidateANormalBoundaryMetricUnitNormalGraphTangent_derivative_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary outer
    let normal := fun row : Fin 4 =>
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
        period hPeriod metric variedMetric displacement parameter hNonNull row
    let actual := fun row column : Fin 4 => fun point =>
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric current row column point
    let tangent := fun column : Fin 4 => fun point =>
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric inner column current point
    (∑ row : Fin 4, ∑ column : Fin 4,
      (mvfderiv throatCoverModelWithCorners (normal row) boundary vector *
          actual row column boundary * tangent column boundary +
        normal row boundary *
          (∑ regular : Fin 4,
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric outer regular current boundary *
              regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
                    metric) metric.metric tensor)
                regular row column
                (normalGraphOrientationDouble period hPeriod displacement
                  (boundary, parameter))) *
            tangent column boundary +
        normal row boundary * actual row column boundary *
          candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
            period hPeriod metric outer inner column current boundary)) = 0 := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let normal := fun row : Fin 4 =>
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull row
  let actual := fun row column : Fin 4 => fun point =>
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
      period hPeriod metric current row column point
  let tangent := fun column : Fin 4 => fun point =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric inner column current point
  let summand := fun row column : Fin 4 => fun point =>
    normal row point * actual row column point * tangent column point
  have hNormal (row : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (normal row) :=
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_contMDiff
      period hPeriod metric variedMetric displacement parameter hNonNull row
  have hActual (row column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (actual row column) := by
    simpa [actual, current] using
      (next_candidateANormalBoundaryActualMetricMatrix_smooth period hPeriod
        metric tensor displacement parameter row column)
  have hTangent (column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (tangent column) := by
    simpa [tangent, current] using
      (next_candidateANormalBoundaryGraphTangentRegularFrameCoefficient_smooth
        period hPeriod metric tensor displacement parameter inner column)
  have hSummand (row column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (summand row column) :=
    ((hNormal row).mul (hActual row column)).mul (hTangent column)
  have hOrthogonal :
      (fun point : CutThroatBoundary period hPeriod =>
        ∑ row : Fin 4, ∑ column : Fin 4, summand row column point) =
        fun _ => 0 := by
    funext point
    unfold summand normal actual tangent current
    exact
      test_candidateANormalBoundaryMetricUnitNormalGraphTangent_orthogonal_smooth
        period hPeriod metric hTransverse tensor variedMetric hVaried displacement
          parameter hNonNull hCurrent point inner (hRootNonneg point)
  have hSummandDerivative (row column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (summand row column) boundary vector =
        mvfderiv throatCoverModelWithCorners (normal row) boundary vector *
              actual row column boundary * tangent column boundary +
          normal row boundary *
              mvfderiv throatCoverModelWithCorners (actual row column) boundary
                vector * tangent column boundary +
          normal row boundary * actual row column boundary *
              mvfderiv throatCoverModelWithCorners (tangent column) boundary
                vector := by
    have hFirst := congrArg (fun derivative => derivative vector)
      (mvfderiv_mul
        ((hNormal row).mdifferentiableAt (by simp))
        ((hActual row column).mdifferentiableAt (by simp)))
    have hSecond := congrArg (fun derivative => derivative vector)
      (mvfderiv_mul
        (((hNormal row).mul (hActual row column)).mdifferentiableAt (by simp))
        ((hTangent column).mdifferentiableAt (by simp)))
    change mvfderiv throatCoverModelWithCorners
        (normal row * actual row column) boundary vector = _ at hFirst
    change mvfderiv throatCoverModelWithCorners (summand row column)
        boundary vector = _ at hSecond
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
      at hFirst hSecond
    rw [hFirst] at hSecond
    rw [hSecond]
    ring
  have hInnerDerivative (row : Fin 4) :
      mvfderiv throatCoverModelWithCorners
          (fun point => ∑ column : Fin 4, summand row column point)
          boundary vector =
        ∑ column : Fin 4,
          mvfderiv throatCoverModelWithCorners (summand row column)
            boundary vector :=
    next_mvfderiv_finset_sum_apply period hPeriod Finset.univ
      (summand row) (hSummand row) boundary vector
  have hOuterSmooth (row : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point => ∑ column : Fin 4, summand row column point) :=
    ContMDiff.sum fun column _ => hSummand row column
  have hOuterDerivative :
      mvfderiv throatCoverModelWithCorners
          (fun point => ∑ row : Fin 4, ∑ column : Fin 4,
            summand row column point) boundary vector =
        ∑ row : Fin 4,
          mvfderiv throatCoverModelWithCorners
            (fun point => ∑ column : Fin 4, summand row column point)
              boundary vector :=
    next_mvfderiv_finset_sum_apply period hPeriod Finset.univ _
      hOuterSmooth boundary vector
  have hDerivativeZero := congrArg
    (fun function => mvfderiv throatCoverModelWithCorners function boundary
      vector) hOrthogonal
  have hZero : mvfderiv throatCoverModelWithCorners
      (fun _ : CutThroatBoundary period hPeriod => (0 : Real)) boundary vector =
      0 := by
    rw [mvfderiv_const]
    rfl
  rw [hOuterDerivative] at hDerivativeZero
  simp_rw [hInnerDerivative] at hDerivativeZero
  rw [hZero] at hDerivativeZero
  simp_rw [hSummandDerivative] at hDerivativeZero
  have hActualDerivative (row column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (actual row column) boundary vector =
        ∑ regular : Fin 4,
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer regular current boundary *
            regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              regular row column
              (normalGraphOrientationDouble period hPeriod displacement
                (boundary, parameter)) := by
    unfold actual vector current
    exact test_candidateANormalBoundaryActualMetricMatrix_mvfderiv_smooth period
      hPeriod metric tensor displacement parameter boundary outer row column
  have hTangentDerivative (column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (tangent column) boundary vector =
        candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner column current boundary := by
    unfold tangent vector current
    exact
      test_candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivative_smooth
        period hPeriod metric tensor displacement parameter boundary outer inner
          column |>.symm
  simp_rw [hActualDerivative, hTangentDerivative] at hDerivativeZero
  unfold vector normal actual tangent at hDerivativeZero
  simp only [current] at hDerivativeZero
  convert hDerivativeZero using 1 <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- A completed Christoffel coefficient contracted with the completed metric
is exactly the genuine varied-metric covariant derivative pairing. -/
theorem next_candidateANormalBoundaryChristoffel_metricPairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (first second lower : Fin 4) :
    (∑ upper : Fin 4,
      candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
            upper first second
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            upper lower boundary) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := test_variedRegularFrameLocalCovariantDerivativeVector
    period hPeriod metric variedMetric patch first second coordinate
  have hChristoffel (upper : Fin 4) :
      candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
          upper first second current boundary = basis.repr connection upper := by
    exact test_candidateANormalBoundaryChristoffel_smooth_apply period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent upper first second
  have hMetric (upper : Fin 4) :
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current upper lower boundary =
        test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
          upper lower (patch.coordinateMap coordinate) := by
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary upper lower]
    rw [test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
    rw [hAt]
  symm
  calc
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        connection
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (∑ upper : Fin 4, basis.repr connection upper • basis upper)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by rw [basis.sum_repr]
    _ = ∑ upper : Fin 4,
        basis.repr connection upper *
          test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
            tensor upper lower (patch.coordinateMap coordinate) := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro upper _
      rw [map_smul]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [show basis upper = pulledRegularFrameVector period hPeriod metric
          patch upper coordinate by
        exact pulledRegularFrameBasis_apply period hPeriod metric patch
          coordinate upper]
      rw [test_localMetricCoordinateForm_pulledRegularFrameVector period hPeriod
        metric tensor variedMetric hVaried]
    _ = ∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper first second current boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current upper lower boundary := by
      apply Finset.sum_congr rfl
      intro upper _
      rw [hChristoffel, hMetric]

set_option backward.isDefEq.respectTransparency false in
/-- Metric compatibility in the completed regular frame, specialized to the
same smooth moving graph. -/
theorem next_candidateANormalBoundaryActualMetricFirstDerivative_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (derivative row column : Fin 4) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) =
      (∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper derivative row
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              upper column boundary) +
      ∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper derivative column
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              upper row boundary := by
  have hCompatibility :=
    test_variedRegularFrameLocalCovariantDerivative_metricCompatible period
      hPeriod metric tensor variedMetric hVaried patch coordinate derivative row
        column
  have hFirst :=
    next_candidateANormalBoundaryChristoffel_metricPairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent derivative row column
  have hSecond :=
    next_candidateANormalBoundaryChristoffel_metricPairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent derivative column row
  have hSymmetry :
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch row coordinate)
          (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
            metric variedMetric patch derivative column coordinate) =
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
            metric variedMetric patch derivative column coordinate)
          (pulledRegularFrameVector period hPeriod metric patch row
            coordinate) := by
    rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
    exact variedMetric.tensor.symmetric _ _ _
  rw [test_regularGeneralMetricC0MetricFirstDerivative_smooth]
  rw [← hAt]
  rw [hCompatibility, hSymmetry, ← hFirst, ← hSecond]

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end
end JanusFormal
