import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryLocalLeviCivitaCompatibility4D

/-!
# Smooth Koszul and Christoffel identification for Candidate A

The completed finite-frame Koszul and Christoffel coefficients are identified
with the existing local Levi-Civita derivative of the same varied metric.
The inverse-matrix cancellations are proved from the installed relative and
background inverse gates; no connection or inverse is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
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

variable (period : Real) (hPeriod : period ≠ 0)

local instance smoothKoszulCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothKoszulCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothKoszulOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothKoszulOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) smoothKoszulEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) smoothKoszulEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev CandidateANormalBoundaryCoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- The fixed background inverse matrix cancels the fixed background metric
on every point of the moving graph. -/
theorem candidateANormalBoundaryBaseInverse_mul_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
          metric current = 1 := by
  classical
  ext row column boundary
  let point := normalBoundaryC2Graph period hPeriod current.1.2 current.2
    boundary
  have hProduct := regularFrameMetricInverse_mul_matrix period hPeriod metric
  have hEntry := congrFun (congrFun hProduct row) column
  have hPoint := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point) hEntry
  simp only [Matrix.mul_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  have hInverse (middle : Fin 4) :
      candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
          period hPeriod metric current row middle boundary =
        regularFrameMetricInverseMatrix period hPeriod metric row middle
          point :=
    candidateANormalBoundarySmoothMatrixFiberEvaluation_apply period hPeriod
      metric (regularFrameMetricInverseMatrix period hPeriod metric) current.1
        current.2 boundary row middle
  have hBase (middle : Fin 4) :
      candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
          metric current middle column boundary =
        regularFrameMetricMatrix period hPeriod metric middle column point :=
    candidateANormalBoundarySmoothMatrixFiberEvaluation_apply period hPeriod
      metric (regularFrameMetricMatrix period hPeriod metric) current.1
        current.2 boundary middle column
  simp_rw [hInverse, hBase]
  have hPoint' :
      (∑ middle : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric row middle point *
          regularFrameMetricMatrix period hPeriod metric middle column point) =
        if row = column then 1 else 0 := by
    simpa [smoothFiniteMatrixProduct,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
      smoothFiniteMatrixIdentity, Matrix.one_apply,
      constantSmoothField] using hPoint
  have hOne :
      ((1 : CandidateANormalBoundaryMatrixField period hPeriod) row column)
          boundary = if row = column then 1 else 0 := by
    by_cases h : row = column <;> simp [Matrix.one_apply, h]
  rw [hOne]
  exact hPoint'

/-- On the admissible metric domain, the completed actual inverse cancels the
completed actual metric. -/
theorem candidateANormalBoundaryActualInverse_mul_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric) :
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current = 1 := by
  rw [candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation,
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
      period hPeriod metric current)]
  rw [candidateANormalBoundaryBaseInverse_mul_metric
    period hPeriod metric current]
  rw [Matrix.one_mul]
  rw [candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
    period hPeriod metric current hCurrent]
  exact candidateANormalBoundaryC2Inverse_mul_totalRelativeMetric
    period hPeriod metric current hCurrent

/-- Regular-frame structure coefficients contracted with the varied metric
are the local metric pairing with the frame Lie bracket. -/
theorem candidateANormalBoundaryRegularFrameStructureVariedMetricContraction_eq_localLieBracket
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (row first second : Fin 4) :
    (∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second upper
          (patch.coordinateMap coordinate) *
        candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row upper
            (patch.coordinateMap coordinate)) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch row coordinate)
        (VectorField.lieBracket Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second)
          coordinate) := by
  rw [regularFrameLocalLieBracket_eq_sum period hPeriod metric patch coordinate]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro upper _
  rw [map_smul]
  rw [candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
    period hPeriod metric tensor variedMetric hVaried]
  rfl

/-- The completed lower Koszul coefficient is exactly the local metric
pairing of the genuine varied-metric Levi-Civita derivative. -/
theorem candidateANormalBoundaryRegularGeneralMetricC0KoszulLower_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (first second lower : Fin 4) :
    regularGeneralMetricC0KoszulLower period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        first second lower (patch.coordinateMap coordinate) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  unfold regularGeneralMetricC0KoszulLower
  change (1 / 2 : Real) *
      (regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            first second lower (patch.coordinateMap coordinate) +
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            second lower first (patch.coordinateMap coordinate) -
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            lower first second (patch.coordinateMap coordinate) -
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              second lower contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              first contracted (patch.coordinateMap coordinate) +
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              lower first contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              second contracted (patch.coordinateMap coordinate) +
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              first second contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              lower contracted (patch.coordinateMap coordinate)) = _
  simp only [candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth,
    regularFrameStructureCoefficientContinuous_apply,
    candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix]
  rw [candidateANormalBoundaryRegularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate first
      second lower]
  rw [candidateANormalBoundaryRegularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate second
      lower first]
  rw [candidateANormalBoundaryRegularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate lower
      first second]
  rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricCompatible
    period hPeriod metric tensor variedMetric hVaried patch coordinate first
      second lower]
  rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricCompatible
    period hPeriod metric tensor variedMetric hVaried patch coordinate second
      lower first]
  rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricCompatible
    period hPeriod metric tensor variedMetric hVaried patch coordinate lower
      first second]
  rw [← candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_torsion
    period hPeriod metric variedMetric patch coordinate second lower]
  rw [← candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_torsion
    period hPeriod metric variedMetric patch coordinate lower first]
  rw [← candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_torsion
    period hPeriod metric variedMetric patch coordinate first second]
  rw [candidateANormalBoundaryLocalMetricCoordinateForm_sub_right,
    candidateANormalBoundaryLocalMetricCoordinateForm_sub_right,
    candidateANormalBoundaryLocalMetricCoordinateForm_sub_right]
  simp only [candidateANormalBoundaryLocalMetricCoordinateForm_symmetric]
  ring

private theorem candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (first second : Fin 4) :
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor first second point =
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor second first point := by
  rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried,
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
  exact variedMetric.tensor.symmetric _ _ _

private theorem
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricPairing_mulVec
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (first second lower : Fin 4) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      Matrix.mulVec
        (fun row column =>
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column
              (patch.coordinateMap coordinate))
        ((pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch first second coordinate))
        lower := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch first second coordinate
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
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor upper lower
              (patch.coordinateMap coordinate) := by
      rw [map_sum]
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro upper _
      rw [map_smul]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [show basis upper =
          pulledRegularFrameVector period hPeriod metric patch upper coordinate by
        exact pulledRegularFrameBasis_apply period hPeriod metric patch
          coordinate upper]
      rw [candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
        period hPeriod metric tensor variedMetric hVaried]
    _ = Matrix.mulVec
        (fun row column =>
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column
              (patch.coordinateMap coordinate))
        (basis.repr connection) lower := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro upper _
      rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_symmetric
        period hPeriod metric tensor variedMetric hVaried]
      ring

/-- On the smooth admissible core, the completed Christoffel coefficient is
the regular-frame coefficient of the genuine local Levi-Civita derivative. -/
theorem candidateANormalBoundaryChristoffel_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (upper first second : Fin 4) :
    candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
        upper first second
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        upper := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch first second coordinate
  let inverseMatrix : Matrix (Fin 4) (Fin 4) Real := fun row column =>
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
      period hPeriod metric current row column boundary
  let actualMatrix : Matrix (Fin 4) (Fin 4) Real := fun row column =>
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
      period hPeriod metric current row column boundary
  have hKoszul (lower : Fin 4) :
      candidateANormalBoundaryKoszulLowerFiberEvaluation period hPeriod metric
          first second lower current boundary =
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          connection
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate) := by
    rw [candidateANormalBoundaryKoszulLowerFiberEvaluation_eq_existing]
    change regularGeneralMetricC0KoszulLower period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
          (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
            tensor))
        first second lower
        (normalBoundaryC2Graph period hPeriod
          (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
            displacement) parameter boundary) = _
    rw [regularGeneralMetricBoundaryC3CoreToC2_smooth,
      normalBoundaryC2Graph_smooth, ← hAt]
    exact candidateANormalBoundaryRegularGeneralMetricC0KoszulLower_smooth_apply
      period hPeriod metric tensor variedMetric hVaried patch coordinate first
        second lower
  have hMetric (row column : Fin 4) :
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row column
            (patch.coordinateMap coordinate) =
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current row column boundary := by
    rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
    dsimp only [current]
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary row column]
    rw [hAt]
  have hPairing (lower : Fin 4) :
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          connection
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate) =
        Matrix.mulVec actualMatrix (basis.repr connection) lower := by
    rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricPairing_mulVec
      period hPeriod metric tensor variedMetric hVaried patch coordinate]
    simp_rw [hMetric]
    rfl
  have hProduct : inverseMatrix * actualMatrix = 1 := by
    have hField := candidateANormalBoundaryActualInverse_mul_metric
      period hPeriod metric current hCurrent
    ext row column
    have hEntry := congrFun (congrFun hField row) column
    have hEvaluated := congrArg
      (fun field : BoundedContinuousFunction
        (CutThroatBoundary period hPeriod) Real => field boundary) hEntry
    change (∑ middle : Fin 4,
      inverseMatrix row middle * actualMatrix middle column) =
        if row = column then 1 else 0
    by_cases h : row = column
    · subst column
      simpa [inverseMatrix, actualMatrix, Matrix.mul_apply, Matrix.one_apply]
        using hEvaluated
    · simpa [inverseMatrix, actualMatrix, Matrix.mul_apply, Matrix.one_apply, h]
        using hEvaluated
  unfold candidateANormalBoundaryChristoffelFiberEvaluation
  change (∑ lower : Fin 4,
      candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
          period hPeriod metric current upper lower boundary *
        candidateANormalBoundaryKoszulLowerFiberEvaluation period hPeriod metric
          first second lower current boundary) = basis.repr connection upper
  simp_rw [hKoszul, hPairing]
  change Matrix.mulVec inverseMatrix
      (Matrix.mulVec actualMatrix (basis.repr connection)) upper =
        basis.repr connection upper
  rw [Matrix.mulVec_mulVec, hProduct, Matrix.one_mulVec]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
