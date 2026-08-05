import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

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

local instance scratchCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance scratchCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) scratchOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) scratchOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) scratchEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) scratchEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

def test_normalBoundarySmoothGraphVerticalTangentialCovector
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real] Real :=
  (variedMetric.tensor.tensor
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary)).comp
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : CutThroatBoundary period hPeriod =>
        normalGraphOrientationDouble period hPeriod displacement
          (current, parameter)) boundary)

theorem test_candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric index (variation, parameter) boundary =
      test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary vector := by
  dsimp only
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  have hMetric (first second : Fin 4) :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary first second
  have hVertical := candidateANormalBoundaryVertical_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary
  have hTangent := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary index
  unfold candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
    test_normalBoundarySmoothGraphVerticalTangentialCovector
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, ContinuousLinearMap.comp_apply]
  simp_rw [hMetric]
  change _ = variedMetric.tensor.tensor point
    (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
      boundary)
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : CutThroatBoundary period hPeriod =>
        normalGraphOrientationDouble period hPeriod displacement
          (current, parameter)) boundary vector)
  rw [← hVertical, ← hTangent]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem test_candidateANormalBoundaryVerticalTangentialReferenceDual_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
        period hPeriod metric row (variation, parameter) boundary =
      intrinsicThroatFiniteFrameAnalysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (intrinsicThroatInverseMusical
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          boundary
          (test_normalBoundarySmoothGraphVerticalTangentialCovector
            period hPeriod variedMetric displacement parameter boundary)) row := by
  dsimp only
  classical
  have hApplied := congrFun
    (intrinsicThroatFiniteFrameEndomorphismMatrixAt_inverseOperator_mulVec
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (test_normalBoundarySmoothGraphVerticalTangentialCovector
        period hPeriod variedMetric displacement parameter boundary)) row
  unfold candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply,
    normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse]
  simp_rw [test_candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  unfold Matrix.mulVec dotProduct at hApplied
  convert hApplied using 1 <;> rfl

def test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary :=
  intrinsicThroatFiniteFrameSynthesisAt
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    boundary
    (fun row =>
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
        period hPeriod metric row current boundary)

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryTangentialProjectionVector_smooth_relative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
        variedMetric displacement parameter boundary
        (test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      intrinsicThroatInverseMusical
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        boundary
        (test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
          variedMetric displacement parameter boundary) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let lift := candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    period hPeriod metric current
  let inverse :=
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
      period hPeriod metric current
  let reference := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
      period hPeriod metric row current
  let coefficients := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric row current
  have hCoefficients : coefficients = inverse.mulVec reference := by
    funext row
    unfold coefficients inverse reference
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      Matrix.mulVec dotProduct
    rfl
  have hInverse := candidateANormalBoundaryInducedRelativeLift_mul_inverse
    period hPeriod metric current hCurrent
  have hSolve : lift.mulVec coefficients = reference := by
    rw [hCoefficients, Matrix.mulVec_mulVec]
    have hProduct : lift * inverse = 1 := by
      simpa only [lift, inverse] using hInverse
    rw [hProduct, Matrix.one_mulVec]
  have hSolveAt :
      (intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap).mulVec
          (fun row => coefficients row boundary) =
        intrinsicThroatFiniteFrameAnalysisAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (intrinsicThroatInverseMusical
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            boundary
            (test_normalBoundarySmoothGraphVerticalTangentialCovector
              period hPeriod variedMetric displacement parameter boundary)) := by
    have hLiftEntry (first second : NormalBoundaryTangentIndex period hPeriod) :
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
              period hPeriod metric current first second boundary =
          intrinsicThroatFiniteFrameLiftAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary
            (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
              variedMetric displacement parameter boundary).toLinearMap
            first second := by
      exact candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_smooth_apply
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary first second
    have hReferenceEntry (index : NormalBoundaryTangentIndex period hPeriod) :
        candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
              period hPeriod metric index current boundary =
          intrinsicThroatFiniteFrameAnalysisAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary
            (intrinsicThroatInverseMusical
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              boundary
              (test_normalBoundarySmoothGraphVerticalTangentialCovector
                period hPeriod variedMetric displacement parameter boundary))
            index := by
      exact
        test_candidateANormalBoundaryVerticalTangentialReferenceDual_smooth_apply
          period hPeriod metric tensor variedMetric hVaried displacement parameter
            boundary index
    funext row
    have hApplied := congrArg
      (fun field : BoundedContinuousFunction
          (CutThroatBoundary period hPeriod) Real => field boundary)
      (congrFun hSolve row)
    unfold lift reference at hApplied
    unfold Matrix.mulVec dotProduct at hApplied ⊢
    simp only [BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.mul_apply] at hApplied
    simp_rw [hLiftEntry, hReferenceEntry] at hApplied
    convert hApplied using 1 <;> rfl
  have hSynthesis := congrArg
    (intrinsicThroatFiniteFrameSynthesisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary) hSolveAt
  rw [intrinsicThroatFiniteFrameSynthesisAt_liftAt_mulVec] at hSynthesis
  have hReconstruct := LinearMap.congr_fun
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary)
    (intrinsicThroatInverseMusical
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      boundary
      (test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hReconstruct
  rw [hReconstruct] at hSynthesis
  dsimp only [coefficients] at hSynthesis
  unfold test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
  convert hSynthesis using 1 <;> rfl

theorem test_candidateANormalBoundaryTangentialProjectionVector_smooth_musical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod
        variedMetric displacement parameter boundary
        (test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary := by
  have hRelative :=
    test_candidateANormalBoundaryTangentialProjectionVector_smooth_relative
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent
  unfold normalBoundarySmoothGraphRelativeEndomorphism at hRelative
  exact (intrinsicThroatInverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    boundary).injective hRelative

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
        (test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      normalGraphInducedMetricInverse period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphTangentialPairing period hPeriod variedMetric displacement
          parameter (orientationDoubleToThroat period hPeriod boundary)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter boundary)) := by
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let target := orientationDoubleToThroat period hPeriod boundary
  let projection :=
    test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary
  let vertical := normalGraphCanonicalLatitudeVector period hPeriod displacement
    parameter boundary
  apply (normalGraphInducedMetricEquiv period hPeriod variedMetric displacement
    parameter hNonNull target).injective
  rw [normalGraphInducedMetricEquiv_apply,
    normalGraphInducedMetricEquiv_apply,
    normalGraphInducedMetric_metricInverse]
  apply ContinuousLinearMap.ext
  intro targetSecond
  have hMusical := congrArg
    (fun covector : TangentSpace throatCoverModelWithCorners boundary →L[Real]
        Real => covector (tangentEquiv.symm targetSecond))
    (test_candidateANormalBoundaryTangentialProjectionVector_smooth_musical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent)
  rw [normalBoundarySmoothGraphInducedMetricMusical_apply] at hMusical
  unfold test_normalBoundarySmoothGraphVerticalTangentialCovector at hMusical
  simp only [ContinuousLinearMap.comp_apply] at hMusical
  rw [normalGraphOrientationDouble_mfderiv_eq_comp,
    ← normalBoundaryOrientationTangentEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hMusical
  exact hMusical

/- Split below: this monolithic version triggered excessive elaboration.
set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryTangentialProjectionAmbient_smooth_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    (∑ index : NormalBoundaryTangentIndex period hPeriod,
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
            period hPeriod metric index current boundary •
        ∑ row : Fin 4,
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric index row current boundary •
            metric.frame row point) =
      normalGraphTangentialProjection period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let derivative := mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun current : CutThroatBoundary period hPeriod =>
      normalGraphOrientationDouble period hPeriod displacement
        (current, parameter)) boundary
  let projection :=
    test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric current boundary
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let target := orientationDoubleToThroat period hPeriod boundary
  have hTangent (index : NormalBoundaryTangentIndex period hPeriod) :=
    candidateANormalBoundaryGraphTangent_smooth_reconstructs
      period hPeriod metric tensor displacement parameter boundary index
  have hProjection :=
    test_candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent hNonNull
  unfold normalGraphTangentialProjection
  calc
    (∑ index : NormalBoundaryTangentIndex period hPeriod,
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
            period hPeriod metric index current boundary •
        ∑ row : Fin 4,
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric index row current boundary •
            metric.frame row
              (normalGraphOrientationDouble period hPeriod displacement
                (boundary, parameter))) =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index current boundary •
          derivative
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt boundary index) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [hTangent index]
    _ = derivative
        (∑ index : NormalBoundaryTangentIndex period hPeriod,
          candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                period hPeriod metric index current boundary •
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt boundary index) := by
      rw [map_sum]
      simp only [map_smul]
    _ = derivative projection := by
      unfold projection
        test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      rw [intrinsicThroatFiniteFrameSynthesisAt_apply]
    _ = mfderiv throatCoverModelWithCorners coverModelWithCorners
          (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
            period hPeriod displacement parameter)
          target (tangentEquiv projection) := by
      rw [normalGraphOrientationDouble_mfderiv_eq_comp,
        normalBoundaryOrientationTangentEquiv_apply]
    _ = mfderiv throatCoverModelWithCorners coverModelWithCorners
          (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
            period hPeriod displacement parameter)
          target
          (normalGraphInducedMetricInverse period hPeriod variedMetric
            displacement parameter hNonNull target
            (normalGraphTangentialPairing period hPeriod variedMetric
              displacement parameter target
              (normalGraphCanonicalLatitudeVector period hPeriod displacement
                parameter boundary))) := by
      rw [hProjection]
-/

def test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun current : CutThroatBoundary period hPeriod =>
      normalGraphOrientationDouble period hPeriod displacement
        (current, parameter)) boundary
    (test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary)

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
        period hPeriod metric tensor displacement parameter boundary =
      normalGraphTangentialProjection period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) := by
  unfold test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
    normalGraphTangentialProjection
  rw [normalGraphOrientationDouble_mfderiv_eq_comp,
    ← normalBoundaryOrientationTangentEquiv_apply]
  rw [test_candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent hNonNull]

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
        period hPeriod metric tensor displacement parameter boundary =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index current boundary •
          ∑ row : Fin 4,
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric index row current boundary •
              metric.frame row point := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let coefficients := fun index : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric index current boundary
  let projection :=
    test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric current boundary
  let derivative := mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun point : CutThroatBoundary period hPeriod =>
      normalGraphOrientationDouble period hPeriod displacement
        (point, parameter)) boundary
  have hSynthesis : projection =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        coefficients index • frame.vectorAt boundary index := by
    unfold projection
      test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    exact intrinsicThroatFiniteFrameSynthesisAt_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary coefficients
  have hDerivative := congrArg derivative hSynthesis
  rw [map_sum] at hDerivative
  simp only [map_smul] at hDerivative
  unfold test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
  change derivative projection = _
  rw [hDerivative]
  apply Finset.sum_congr rfl
  intro index _
  rw [candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary index]

def test_candidateANormalBoundaryMetricNormalVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod metric
        tensor displacement parameter boundary =
      normalGraphMetricNormal period hPeriod variedMetric displacement parameter
        hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  have hAlgebra :
      (∑ upper : Fin 4,
        candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
              period hPeriod metric upper current boundary •
          metric.frame upper point) =
        (∑ upper : Fin 4,
          candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
                period hPeriod metric upper current boundary •
            metric.frame upper point) -
          ∑ index : NormalBoundaryTangentIndex period hPeriod,
            candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                  period hPeriod metric index current boundary •
              ∑ upper : Fin 4,
                candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                      period hPeriod metric index upper current boundary •
                  metric.frame upper point := by
    unfold candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
    simp only [BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
  have hVertical := candidateANormalBoundaryVertical_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary
  have hProjectionSum :=
    test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_sum
      period hPeriod metric tensor displacement parameter boundary
  have hProjectionHistorical :=
    test_candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_historical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent hNonNull
  unfold test_candidateANormalBoundaryMetricNormalVector_smooth
    normalGraphMetricNormal
  rw [hAlgebra, hVertical, ← hProjectionSum, hProjectionHistorical]

theorem test_candidateANormalBoundaryMetricNormalSquare_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary)
        (test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary) := by
  classical
  unfold candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    test_candidateANormalBoundaryMetricNormalVector_smooth
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro second _
  rw [variedMetric.tensor.symmetric]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryMetricNormalSquare_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      normalGraphMetricNormalSquare period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          boundary) := by
  rw [test_candidateANormalBoundaryMetricNormalSquare_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [test_candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent hNonNull]
  unfold normalGraphMetricNormalSquare normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]
  rfl

def test_candidateANormalBoundaryMetricUnitNormalVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

theorem test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    test_candidateANormalBoundaryMetricUnitNormalVector_smooth period hPeriod
        metric tensor displacement parameter boundary =
      candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric current boundary •
        test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary := by
  dsimp only
  classical
  unfold test_candidateANormalBoundaryMetricUnitNormalVector_smooth
    test_candidateANormalBoundaryMetricNormalVector_smooth
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.mul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro upper _
  rw [smul_smul]

set_option backward.isDefEq.respectTransparency false in
theorem
    test_candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary =
      (Real.sqrt
        |normalGraphMetricNormalSquare period hPeriod variedMetric displacement
          parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
          (normalGraphCanonicalNormalClass period hPeriod displacement parameter
            boundary)|)⁻¹ := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
      period hPeriod metric current
  let root := Real.sqrt
    |normalGraphMetricNormalSquare period hPeriod variedMetric displacement
      parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary)|
  have hMagnitudeHistorical : magnitude boundary = root := by
    unfold magnitude root
    rw [candidateANormalBoundaryMetricNormalMagnitude_eq_sqrt_abs
      period hPeriod metric hTransverse hCurrent boundary hRootNonneg]
    rw [test_candidateANormalBoundaryMetricNormalSquare_smooth_eq_historical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent.1.2 hNonNull]
  have hMagnitudeUnit : IsUnit magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_isUnit
      period hPeriod metric hTransverse hCurrent
  have hInverse := Ring.inverse_mul_cancel magnitude hMagnitudeUnit
  have hInverseAt := congrArg (fun field => field boundary) hInverse
  change Ring.inverse magnitude boundary * magnitude boundary = 1 at hInverseAt
  rw [hMagnitudeHistorical] at hInverseAt
  have hRootNe : root ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hInverseAt
    exact zero_ne_one hInverseAt
  change Ring.inverse magnitude boundary = root⁻¹
  calc
    Ring.inverse magnitude boundary =
        Ring.inverse magnitude boundary * (root * root⁻¹) := by
      rw [mul_inv_cancel₀ hRootNe, mul_one]
    _ = (Ring.inverse magnitude boundary * root) * root⁻¹ := by ring
    _ = root⁻¹ := by rw [hInverseAt, one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    test_candidateANormalBoundaryMetricUnitNormalVector_smooth period hPeriod
        metric tensor displacement parameter boundary =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
  rw [test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
  rw [
    test_candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_eq_historical
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter boundary hCurrent hNonNull hRootNonneg]
  rw [test_candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent.1.2 hNonNull]
  unfold normalGraphCanonicalMetricUnitNormal normalGraphMetricUnitNormal
    normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]

def test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer inner upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

theorem test_candidateANormalBoundaryGaussRaw_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary)
        (test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
          period hPeriod metric tensor displacement parameter outer inner
            boundary) := by
  classical
  unfold candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
    test_candidateANormalBoundaryMetricNormalVector_smooth
    test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
  simp only [BoundedContinuousFunction.neg_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro second _
  rw [variedMetric.tensor.symmetric]
  ring

theorem test_candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (test_candidateANormalBoundaryMetricUnitNormalVector_smooth period
          hPeriod metric tensor displacement parameter boundary)
        (test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
          period hPeriod metric tensor displacement parameter outer inner
            boundary) := by
  unfold
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
  simp only [BoundedContinuousFunction.mul_apply]
  rw [test_candidateANormalBoundaryGaussRaw_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      outer inner boundary]
  rw [test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Scratch-only global fidelity check for the already installed smooth
relative-metric chart. -/
theorem test_regularGeneralMetricC0MetricCoefficient_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column point =
      metric.metric.tensor.tensor point (metric.frame row point)
          (metric.frame column point) +
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
  classical
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let raised := inverseMetricSharp period hPeriod metric.metric point
    (tensor.tensor point (metric.frame column point))
  have hCoefficient (middle : Fin 4) :
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point middle raised := by
    rfl
  have hReconstruct := generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod frame metric.metric point raised
  have hRaised : raised = ∑ middle : Fin 4,
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point •
        metric.frame middle point := by
    calc
      raised = ∑ middle : Fin 4,
          generalMetricFiniteFrameCoefficientAt period hPeriod frame
              metric.metric point middle raised • metric.frame middle point :=
        hReconstruct
      _ = _ := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hCoefficient]
  have hPair :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
            metric.metric tensor middle column point =
        metric.metric.tensor.tensor point (metric.frame row point) raised := by
    calc
      _ = ∑ middle : Fin 4,
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
              metric.metric tensor middle column point *
            regularFrameMetricMatrix period hPeriod metric row middle point := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [mul_comm]
      _ = metric.metric.tensor.tensor point (metric.frame row point)
          (∑ middle : Fin 4,
            smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
                metric.metric tensor middle column point •
              metric.frame middle point) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, regularFrameMetricMatrix_apply]
      _ = _ := congrArg
        (fun vector => metric.metric.tensor.tensor point
          (metric.frame row point) vector) hRaised.symm
  have hFlat := congrArg
    (fun covector => covector (metric.frame row point))
    (metric_flat_inverseMetricSharp period hPeriod metric.metric point
      (tensor.tensor point (metric.frame column point)))
  have hPairRaised :
      metric.metric.tensor.tensor point (metric.frame row point) raised =
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
    calc
      metric.metric.tensor.tensor point (metric.frame row point) raised =
          metric.metric.tensor.tensor point raised (metric.frame row point) :=
        metric.metric.tensor.symmetric _ _ _
      _ = tensor.tensor point (metric.frame column point)
          (metric.frame row point) := by
        rw [← metric.metric.musical_eq_tensor point]
        exact hFlat
      _ = _ := tensor.symmetric _ _ _
  have hBase :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          (1 : Matrix (Fin 4) (Fin 4) Real) middle column =
        regularFrameMetricMatrix period hPeriod metric row column point := by
    let base : Matrix (Fin 4) (Fin 4) Real := fun first second =>
      regularFrameMetricMatrix period hPeriod metric first second point
    exact congrFun (congrFun (Matrix.mul_one base) row) column
  rw [regularGeneralMetricC0MetricCoefficient_apply_expansion]
  change (∑ middle : Fin 4,
      regularFrameMetricMatrix period hPeriod metric row middle point *
        ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
            metric.metric tensor middle column point)) = _
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hBase, hPair, hPairRaised,
    regularFrameMetricMatrix_apply]

def test_smoothRegularGeneralMetricRelativeMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothFiniteMatrix period hPeriod 4 := by
  simpa using
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor)

def test_smoothRegularGeneralMetricActualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :=
  smoothFiniteMatrixProduct period hPeriod 4
    (regularFrameMetricMatrix period hPeriod metric)
    (smoothFiniteMatrixIdentity period hPeriod 4 +
      test_smoothRegularGeneralMetricRelativeMatrix period hPeriod metric
        tensor)

theorem test_regularGeneralMetricC2MetricMatrix_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2MetricMatrix period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor) := by
  unfold regularGeneralMetricC2MetricMatrix
    generalMetricRelativeC2ExtendedMatrix
    regularFrameMetricC2Matrix
    test_smoothRegularGeneralMetricActualMatrix
    smoothToGeneralMetricRelativeC2Core
    smoothGeneralMetricRelativeEndomorphismToC2
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (smoothFiniteMatrixToC2 period hPeriod 4
        (regularFrameMetricMatrix period hPeriod metric))
      (c2FiniteMatrixIdentity period hPeriod 4 +
        smoothFiniteMatrixToC2 period hPeriod 4
          (test_smoothRegularGeneralMetricRelativeMatrix period hPeriod metric
            tensor)) = _
  rw [show c2FiniteMatrixIdentity period hPeriod 4 +
        smoothFiniteMatrixToC2 period hPeriod 4
          (test_smoothRegularGeneralMetricRelativeMatrix period hPeriod metric
            tensor) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothFiniteMatrixIdentity period hPeriod 4 +
          test_smoothRegularGeneralMetricRelativeMatrix period hPeriod metric
            tensor) by
      rw [map_add]
      rfl]
  exact c2FiniteMatrixProduct_smooth period hPeriod 4 _ _

theorem test_regularGeneralMetricC0MetricFirstDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column point =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor row column) point derivative := by
  unfold regularGeneralMetricC0MetricFirstDerivative
  rw [test_regularGeneralMetricC2MetricMatrix_smooth]
  exact regularFrameC2FirstDerivative_smooth period hPeriod metric derivative
    (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
      row column) point

theorem test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
        row column point =
      variedMetric.tensor.tensor point (metric.frame row point)
        (metric.frame column point) := by
  have hMatrix :
      regularGeneralMetricC0MetricCoefficient period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          row column point =
        test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor row column point := by
    unfold regularGeneralMetricC0MetricCoefficient
    rw [test_regularGeneralMetricC2MetricMatrix_smooth]
    rfl
  rw [← hMatrix]
  rw [test_regularGeneralMetricC0MetricCoefficient_smooth]
  change _ = variedMetric.tensor.tensor point (metric.frame row point)
    (metric.frame column point)
  rw [hVaried]
  rfl

theorem test_candidateANormalBoundaryBaseMetric_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
          metric current *
        candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
          period hPeriod metric current = 1 := by
  classical
  ext row column boundary
  let point := normalBoundaryC2Graph period hPeriod current.1.2 current.2
    boundary
  have hProduct := regularFrameMetricMatrix_mul_inverse period hPeriod metric
  have hEntry := congrFun (congrFun hProduct row) column
  have hPoint := congrArg
    (fun field : SmoothQuotientField period hPeriod Real =>
      field point) hEntry
  simp only [Matrix.mul_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  have hBase (middle : Fin 4) :
      candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
          metric current row middle boundary =
        regularFrameMetricMatrix period hPeriod metric row middle point :=
    candidateANormalBoundarySmoothMatrixFiberEvaluation_apply period hPeriod
      metric (regularFrameMetricMatrix period hPeriod metric) current.1
        current.2 boundary row middle
  have hInverse (middle : Fin 4) :
      candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
          period hPeriod metric current middle column boundary =
        regularFrameMetricInverseMatrix period hPeriod metric middle column
          point :=
    candidateANormalBoundarySmoothMatrixFiberEvaluation_apply period hPeriod
      metric (regularFrameMetricInverseMatrix period hPeriod metric) current.1
        current.2 boundary middle column
  simp_rw [hBase, hInverse]
  have hPoint' :
      (∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          regularFrameMetricInverseMatrix period hPeriod metric middle column
            point) = if row = column then 1 else 0 := by
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

theorem test_candidateANormalBoundaryActualMetric_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric) :
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current *
        candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
          period hPeriod metric current = 1 := by
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation,
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
      period hPeriod metric current)]
  rw [candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
    period hPeriod metric current hCurrent]
  rw [candidateANormalBoundaryTotalRelativeMetric_mul_c2Inverse
    period hPeriod metric current hCurrent]
  rw [Matrix.one_mul]
  exact test_candidateANormalBoundaryBaseMetric_mul_inverse
    period hPeriod metric current

theorem test_candidateANormalBoundaryBaseInverse_mul_metric
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

theorem test_candidateANormalBoundaryActualInverse_mul_metric
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
  rw [test_candidateANormalBoundaryBaseInverse_mul_metric
    period hPeriod metric current]
  rw [Matrix.one_mul]
  rw [candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
    period hPeriod metric current hCurrent]
  exact candidateANormalBoundaryC2Inverse_mul_totalRelativeMetric
    period hPeriod metric current hCurrent

private abbrev TestCoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

def test_variedRegularFrameLocalCovariantDerivativeVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Fin 4) (coordinate : TestCoordinateVector) :
    TestCoordinateVector :=
  fderiv Real
      (pulledRegularFrameVector period hPeriod metric patch second)
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate) +
    localLeviCivitaChristoffelApply period hPeriod variedMetric patch
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate)

theorem test_localMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (first second : Fin 4) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate) =
      test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
        first second (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    coordinateMap_mfderiv_pulledRegularFrameVector]
  exact (test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
    period hPeriod metric tensor variedMetric hVaried first second
      (patch.coordinateMap coordinate)).symm

theorem test_fderiv_localMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (derivative first second : Fin 4) :
    fderiv Real
        (fun current =>
          localMetricCoordinateForm period hPeriod variedMetric patch current
            (pulledRegularFrameVector period hPeriod metric patch first current)
            (pulledRegularFrameVector period hPeriod metric patch second current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor first second)
        (patch.coordinateMap coordinate) derivative := by
  have hFunction :
      (fun current =>
        localMetricCoordinateForm period hPeriod variedMetric patch current
          (pulledRegularFrameVector period hPeriod metric patch first current)
          (pulledRegularFrameVector period hPeriod metric patch second current)) =
        (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor first second).toFun ∘ patch.coordinateMap := by
    funext current
    exact test_localMetricCoordinateForm_pulledRegularFrameVector period
      hPeriod metric tensor variedMetric hVaried patch current first second
  rw [hFunction]
  exact fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
    metric (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
      tensor first second) patch coordinate derivative

private theorem test_localMetricCoordinateForm_add_left
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : TestCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (first + second) third =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first third +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          second third := by
  exact congrArg (fun form => form third)
    (map_add
      (localMetricCoordinateForm period hPeriod variedMetric patch coordinate)
      first second)

private theorem test_localMetricCoordinateForm_add_right
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : TestCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first (second + third) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first second +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first third := by
  exact map_add
    (localMetricCoordinateForm period hPeriod variedMetric patch coordinate
      first) second third

private theorem test_localMetricCoordinateForm_sub_right
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : TestCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first (second - third) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first second -
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first third := by
  exact map_sub
    (localMetricCoordinateForm period hPeriod variedMetric patch coordinate
      first) second third

private theorem test_localMetricCoordinateForm_symmetric
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : TestCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first second =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        second first := by
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  exact variedMetric.tensor.symmetric _ _ _

private theorem
    test_fderiv_localMetricCoordinateForm_pulledRegularFrameVector_expand
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (derivative first second : Fin 4) :
    fderiv Real
        (fun current =>
          localMetricCoordinateForm period hPeriod variedMetric patch current
            (pulledRegularFrameVector period hPeriod metric patch first current)
            (pulledRegularFrameVector period hPeriod metric patch second current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch first)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate))
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricDerivativeTrilinearForm period hPeriod variedMetric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch second)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate)) := by
  have hMatrix : DifferentiableAt Real
      (localMetricMatrix period hPeriod variedMetric patch) coordinate :=
    (localMetricMatrix_contDiff period hPeriod variedMetric patch)
      |>.differentiable (by simp) coordinate
  simpa only [localMetricCoordinateForm,
    localMetricDerivativeTrilinearForm_apply] using
    (fderiv_matrix_toBilin_dynamic_apply
      (localMetricMatrix period hPeriod variedMetric patch)
      (pulledRegularFrameVector period hPeriod metric patch first)
      (pulledRegularFrameVector period hPeriod metric patch second)
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate)
      hMatrix
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate first)
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate second))

theorem test_variedRegularFrameLocalCovariantDerivative_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (derivative first second : Fin 4) :
    frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
          tensor first second)
        (patch.coordinateMap coordinate) derivative =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
            metric variedMetric patch derivative first coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
            metric variedMetric patch derivative second coordinate) := by
  rw [← test_fderiv_localMetricCoordinateForm_pulledRegularFrameVector
    period hPeriod metric tensor variedMetric hVaried patch coordinate
      derivative first second]
  rw [test_fderiv_localMetricCoordinateForm_pulledRegularFrameVector_expand]
  have hCompatibility := congrArg
    (fun form => form
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate)
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate))
    (localMetricDerivativeTrilinearForm_eq_leviCivita period hPeriod
      variedMetric patch coordinate)
  rw [hCompatibility]
  simp only [localLeviCivitaMetricCompatibilityForm_apply,
    localLeviCivitaChristoffelBilinearMap_apply,
    test_variedRegularFrameLocalCovariantDerivativeVector]
  rw [test_localMetricCoordinateForm_add_left,
    test_localMetricCoordinateForm_add_right]
  abel

theorem test_variedRegularFrameLocalCovariantDerivative_torsion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (first second : Fin 4) :
    test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch first second coordinate -
        test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch second first coordinate =
      VectorField.lieBracket Real
        (pulledRegularFrameVector period hPeriod metric patch first)
        (pulledRegularFrameVector period hPeriod metric patch second)
        coordinate := by
  unfold test_variedRegularFrameLocalCovariantDerivativeVector
    VectorField.lieBracket
  rw [localLeviCivitaChristoffelApply_symmetric period hPeriod variedMetric
    patch coordinate
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)]
  abel

theorem test_regularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column point =
      test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
        row column point := by
  unfold regularGeneralMetricC0MetricCoefficient
  rw [test_regularGeneralMetricC2MetricMatrix_smooth]
  rfl

theorem test_regularFrameStructureVariedMetricContraction_eq_localLieBracket
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (row first second : Fin 4) :
    (∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second upper
          (patch.coordinateMap coordinate) *
        test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
          row upper (patch.coordinateMap coordinate)) =
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
  rw [test_localMetricCoordinateForm_pulledRegularFrameVector period hPeriod
    metric tensor variedMetric hVaried]
  rfl

theorem test_regularGeneralMetricC0KoszulLower_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (first second lower : Fin 4) :
    regularGeneralMetricC0KoszulLower period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        first second lower (patch.coordinateMap coordinate) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch first second coordinate)
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
  simp only [test_regularGeneralMetricC0MetricFirstDerivative_smooth,
    regularFrameStructureCoefficientContinuous_apply,
    test_regularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix]
  rw [test_regularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate first
      second lower]
  rw [test_regularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate second
      lower first]
  rw [test_regularFrameStructureVariedMetricContraction_eq_localLieBracket
    period hPeriod metric tensor variedMetric hVaried patch coordinate lower
      first second]
  rw [test_variedRegularFrameLocalCovariantDerivative_metricCompatible period
    hPeriod metric tensor variedMetric hVaried patch coordinate first second
      lower]
  rw [test_variedRegularFrameLocalCovariantDerivative_metricCompatible period
    hPeriod metric tensor variedMetric hVaried patch coordinate second lower
      first]
  rw [test_variedRegularFrameLocalCovariantDerivative_metricCompatible period
    hPeriod metric tensor variedMetric hVaried patch coordinate lower first
      second]
  rw [← test_variedRegularFrameLocalCovariantDerivative_torsion period hPeriod
    metric variedMetric patch coordinate second lower]
  rw [← test_variedRegularFrameLocalCovariantDerivative_torsion period hPeriod
    metric variedMetric patch coordinate lower first]
  rw [← test_variedRegularFrameLocalCovariantDerivative_torsion period hPeriod
    metric variedMetric patch coordinate first second]
  rw [test_localMetricCoordinateForm_sub_right,
    test_localMetricCoordinateForm_sub_right,
    test_localMetricCoordinateForm_sub_right]
  simp only [test_localMetricCoordinateForm_symmetric]
  ring

private theorem test_smoothRegularGeneralMetricActualMatrix_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (first second : Fin 4) :
    test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
        first second point =
      test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
        second first point := by
  rw [test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried,
    test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
  exact variedMetric.tensor.symmetric _ _ _

private theorem
    test_variedRegularFrameLocalCovariantDerivative_metricPairing_mulVec
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector) (first second lower : Fin 4) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      Matrix.mulVec
        (fun row column =>
          test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
            tensor row column (patch.coordinateMap coordinate))
        ((pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
          (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
            metric variedMetric patch first second coordinate)) lower := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := test_variedRegularFrameLocalCovariantDerivativeVector
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
          test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
            tensor upper lower (patch.coordinateMap coordinate) := by
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
      rw [test_localMetricCoordinateForm_pulledRegularFrameVector period hPeriod
        metric tensor variedMetric hVaried]
    _ = Matrix.mulVec
        (fun row column =>
          test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
            tensor row column (patch.coordinateMap coordinate))
        (basis.repr connection) lower := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro upper _
      rw [test_smoothRegularGeneralMetricActualMatrix_symmetric period hPeriod
        metric tensor variedMetric hVaried]
      ring

theorem test_candidateANormalBoundaryChristoffel_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : TestCoordinateVector)
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
        (test_variedRegularFrameLocalCovariantDerivativeVector period hPeriod
          metric variedMetric patch first second coordinate) upper := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := test_variedRegularFrameLocalCovariantDerivativeVector
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
    exact test_regularGeneralMetricC0KoszulLower_smooth_apply period hPeriod
      metric tensor variedMetric hVaried patch coordinate first second lower
  have hMetric (row column : Fin 4) :
      test_smoothRegularGeneralMetricActualMatrix period hPeriod metric tensor
          row column (patch.coordinateMap coordinate) =
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current row column boundary := by
    rw [test_smoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
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
    rw [test_variedRegularFrameLocalCovariantDerivative_metricPairing_mulVec
      period hPeriod metric tensor variedMetric hVaried patch coordinate]
    simp_rw [hMetric]
    rfl
  have hProduct : inverseMatrix * actualMatrix = 1 := by
    have hField := test_candidateANormalBoundaryActualInverse_mul_metric
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

set_option backward.isDefEq.respectTransparency false in
theorem test_normalBoundarySmoothCollarField_mvfderiv_graph
    (field : CutThroatBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (latitude : CutThroatBoundary period hPeriod → Real)
    (hLatitude : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude)
    (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let slope := mvfderiv throatCoverModelWithCorners latitude boundary vector
    mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        (fun point : CutThroatBoundary period hPeriod =>
          field (point, latitude point)) boundary vector =
      normalBoundaryHorizontalFieldDerivative period hPeriod index field
          (boundary, latitude boundary) +
        slope • normalBoundaryLatitudeFieldDerivative period hPeriod field
          (boundary, latitude boundary) := by
  dsimp only
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let slope := mvfderiv throatCoverModelWithCorners latitude boundary vector
  let graphParameter : CutThroatBoundary period hPeriod →
      CutThroatBoundary period hPeriod × Real :=
    fun point => (point, latitude point)
  have hParameter : MDifferentiableAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      graphParameter boundary :=
    (contMDiff_id.prodMk hLatitude).mdifferentiableAt (by simp)
  have hFieldAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) field (graphParameter boundary) :=
    hField.mdifferentiableAt (by simp)
  have hParameterDerivative := congrArg (fun derivative => derivative vector)
    (mfderiv_prodMk
      (f := fun point : CutThroatBoundary period hPeriod => point)
      (g := latitude) mdifferentiableAt_id
      (hLatitude.mdifferentiableAt (by simp)))
  have hParameterApply :
      mfderiv throatCoverModelWithCorners
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          graphParameter boundary vector = (vector, slope) := by
    refine hParameterDerivative.trans ?_
    change
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners id
          boundary vector,
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          latitude boundary vector) = (vector, slope)
    rw [mfderiv_id]
    rfl
  have hCompApply :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (field ∘ graphParameter) boundary vector =
        mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) field (graphParameter boundary)
            (mfderiv throatCoverModelWithCorners
              (throatCoverModelWithCorners.prod
                (modelWithCornersSelf Real Real))
              graphParameter boundary vector) := by
    exact mfderiv_comp_apply boundary hFieldAt hParameter vector
  have hGraph :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (fun point : CutThroatBoundary period hPeriod =>
            field (point, latitude point)) boundary vector =
        mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) field
          (boundary, latitude boundary) (vector, slope) := by
    rw [hParameterApply] at hCompApply
    simpa only [graphParameter, Function.comp_def] using hCompApply
  rw [hGraph]
  have hSplit := mfderiv_prod_eq_add_apply
    (E := ThroatCoverCoordinates) (E' := Real)
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (v := (vector, slope)) hFieldAt
  dsimp only [graphParameter] at hSplit
  have hFieldAtCurrent : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) field
      (boundary, latitude boundary) := by
    simpa only [graphParameter] using hFieldAt
  have hHorizontal :
      normalBoundaryHorizontalFieldDerivative period hPeriod index field
          (boundary, latitude boundary) =
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (fun point : CutThroatBoundary period hPeriod =>
            field (point, latitude boundary)) boundary vector := by
    have hProduct := mfderiv_prod_eq_add_apply
      (E := ThroatCoverCoordinates) (E' := Real)
      (I := throatCoverModelWithCorners)
      (I' := modelWithCornersSelf Real Real)
      (v := (vector, 0)) hFieldAtCurrent
    rw [map_zero, add_zero] at hProduct
    unfold normalBoundaryHorizontalFieldDerivative
      normalBoundaryLatitudeHorizontalTangentLift
    change mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) field
        (boundary, latitude boundary) (vector, 0) = _
    exact hProduct
  have hVertical :
      normalBoundaryLatitudeFieldDerivative period hPeriod field
          (boundary, latitude boundary) =
        mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by
    have hProduct := mfderiv_prod_eq_add_apply
      (E := ThroatCoverCoordinates) (E' := Real)
      (I := throatCoverModelWithCorners)
      (I' := modelWithCornersSelf Real Real)
      (v := (0, 1)) hFieldAtCurrent
    rw [map_zero, zero_add] at hProduct
    unfold normalBoundaryLatitudeFieldDerivative
      normalBoundaryLatitudeQuotientVerticalTangentLift
    change mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) field
        (boundary, latitude boundary) (0, 1) = _
    exact hProduct
  have hVerticalSlope :
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) slope =
        slope • mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by
    calc
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) slope =
        mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) (slope • (1 : Real)) := by simp
      _ = slope • mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by rw [map_smul]
  rw [hSplit, ← hHorizontal, hVerticalSlope, ← hVertical]

set_option backward.isDefEq.respectTransparency false in
theorem test_reciprocalQuadratic_mvfderiv
    (raw : CutThroatBoundary period hPeriod → Real)
    (hRaw : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ raw)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mvfderiv throatCoverModelWithCorners
        (fun point => 1 / (1 + raw point ^ 2)) boundary vector =
      (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2) *
        mvfderiv throatCoverModelWithCorners raw boundary vector := by
  let reciprocalQuadratic : Real → Real := fun value =>
    1 / (1 + value ^ 2)
  have hReciprocalQuadratic (value : Real) : HasDerivAt
      reciprocalQuadratic
      (-2 * value * (1 / (1 + value ^ 2)) ^ 2) value := by
    let denominator : Real → Real := fun varied => 1 + varied ^ 2
    have hDenominator : HasDerivAt denominator
        (2 * value) value := by
      simpa [denominator] using ((hasDerivAt_id value).pow 2).const_add 1
    have hInverse := (hasDerivAt_inv
      (show denominator value ≠ 0 by dsimp only [denominator]; positivity))
        |>.comp value hDenominator
    convert! hInverse using 1
    · funext varied
      change 1 / (1 + varied ^ 2) = (1 + varied ^ 2)⁻¹
      exact one_div _
    · change -2 * value * (1 / (1 + value ^ 2)) ^ 2 =
        -((1 + value ^ 2) ^ 2)⁻¹ * (2 * value)
      field_simp
  have hOuter :=
    (hReciprocalQuadratic (raw boundary)).hasFDerivAt.hasMFDerivAt
  have hComp := hOuter.comp boundary
    (hRaw.mdifferentiableAt (by simp)).hasMFDerivAt
  have hDerivative := congrArg (fun derivative => derivative vector) hComp.mfderiv
  have hDerivative' := congrArg
    (NormedSpace.fromTangentSpace (reciprocalQuadratic (raw boundary)))
    hDerivative
  change mvfderiv throatCoverModelWithCorners
      (reciprocalQuadratic ∘ raw) boundary vector = _
  refine hDerivative'.trans ?_
  change (NormedSpace.fromTangentSpace (reciprocalQuadratic (raw boundary)))
      (ContinuousLinearMap.toSpanSingleton Real
        (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2)
          (mfderiv throatCoverModelWithCorners
            (modelWithCornersSelf Real Real) raw boundary vector)) = _
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  change mvfderiv throatCoverModelWithCorners raw boundary vector *
      (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2) = _
  ring

set_option backward.isDefEq.respectTransparency false in
theorem test_normalBoundaryC2ScaledRawSpatialFirst_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement, parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          parameter * normalDisplacementOrientationScalar
            period hPeriod displacement point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let field := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  have hScaled := congrFun (congrFun
    (throatFrameDerivative_smul
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame parameter field) boundary) index
  rw [normalBoundaryC2ScaledRawSpatialFirst_apply,
    normalBoundaryC2JetCoreFirstAt_smooth]
  rw [throatFrameDerivative_eq_mvfderiv] at hScaled
  change parameter * throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field boundary index = _
  change mvfderiv throatCoverModelWithCorners
      (fun point : CutThroatBoundary period hPeriod =>
        parameter * normalDisplacementOrientationScalar
          period hPeriod displacement point)
      boundary
      ((finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index) =
    parameter * throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field boundary index at hScaled
  exact hScaled.symm

set_option backward.isDefEq.respectTransparency false in
theorem test_normalBoundaryC2ScaledRawSpatialSecond_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement, parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement, parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let field := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  let scaledField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    parameter • field
  have hFunction :
      (fun point : CutThroatBoundary period hPeriod =>
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement, parameter) point) =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          scaledField inner).toFun := by
    funext point
    rw [test_normalBoundaryC2ScaledRawSpatialFirst_smooth]
    change mvfderiv throatCoverModelWithCorners
        (fun current : CutThroatBoundary period hPeriod =>
          parameter * normalDisplacementOrientationScalar
            period hPeriod displacement current)
        point (frame.vectorAt point inner) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame scaledField point inner
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  rw [hFunction]
  change normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
      (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement, parameter) boundary =
    throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        scaledField inner) boundary outer
  change normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
      (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement, parameter) boundary =
    normalBoundaryFrameSecondDerivative period hPeriod frame scaledField
      boundary outer inner
  rw [normalBoundaryC2ScaledRawSpatialSecond_apply,
    normalBoundaryC2JetCoreSecondAt_smooth]
  have hScaled := congrFun (congrFun (congrFun
    (normalBoundaryFrameSecondDerivative_smul period hPeriod frame
      parameter field) boundary) outer) inner
  simpa only [scaledField, field, frame, Pi.smul_apply, smul_eq_mul] using
    hScaled.symm

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryLatitudeSpatialSecond_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
            period hPeriod metric inner
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let normal := smoothNormalDisplacementToBoundaryC2JetCore
    period hPeriod displacement
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let raw : CutThroatBoundary period hPeriod → Real := fun point =>
    parameter * normalDisplacementOrientationScalar
      period hPeriod displacement point
  let first (index : NormalBoundaryTangentIndex period hPeriod) :
      CutThroatBoundary period hPeriod → Real := fun point =>
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
      (normal, parameter) point
  let reciprocal : CutThroatBoundary period hPeriod → Real := fun point =>
    1 / (1 + raw point ^ 2)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let scalarField := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  let scaledField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    parameter • scalarField
  have hCurrentNormal : current.1.2 = normal := rfl
  have hCurrentParameter : current.2 = parameter := rfl
  have hRawEvaluation :
      candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
          current boundary = raw boundary := by
    rfl
  have hReciprocalEvaluation :
      candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
          period hPeriod metric current boundary = reciprocal boundary := by
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rfl
  have hRawSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ raw := by
    exact contMDiff_const.mul
      (normalDisplacementOrientationScalar_contMDiff
        period hPeriod displacement)
  have hFirstFunction (index : NormalBoundaryTangentIndex period hPeriod) :
      first index =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          scaledField index).toFun := by
    funext point
    dsimp only [first, normal]
    rw [test_normalBoundaryC2ScaledRawSpatialFirst_smooth]
    change mvfderiv throatCoverModelWithCorners raw point
        (frame.vectorAt point index) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame scaledField point index
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hFirstSmooth (index : NormalBoundaryTangentIndex period hPeriod) :
      ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞ (first index) := by
    rw [hFirstFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      scaledField index).contMDiff_toFun
  have hReciprocalSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ reciprocal := by
    have hDenominator : ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞
        (fun point => 1 + raw point ^ 2) :=
      contMDiff_const.add (hRawSmooth.pow 2)
    have hInverse := hDenominator.inv₀ (fun point => by positivity)
    simpa only [reciprocal, one_div] using hInverse
  have hCandidateFirst :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
          period hPeriod metric inner current point) =
        first inner * reciprocal := by
    funext point
    unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    change normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
          (normal, parameter) point *
        candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
          period hPeriod metric current point =
      first inner point * reciprocal point
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rfl
  have hRawDerivative :
      mvfderiv throatCoverModelWithCorners raw boundary vector =
        first outer boundary := by
    exact (test_normalBoundaryC2ScaledRawSpatialFirst_smooth period hPeriod
      displacement parameter boundary outer).symm
  have hFirstDerivative :
      mvfderiv throatCoverModelWithCorners (first inner) boundary vector =
        normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
          (normal, parameter) boundary := by
    exact (test_normalBoundaryC2ScaledRawSpatialSecond_smooth period hPeriod
      displacement parameter boundary outer inner).symm
  have hReciprocalDerivative :
      mvfderiv throatCoverModelWithCorners reciprocal boundary vector =
        (-2 * raw boundary * reciprocal boundary ^ 2) *
          first outer boundary := by
    have hDerivative := test_reciprocalQuadratic_mvfderiv
      period hPeriod raw hRawSmooth boundary vector
    rw [hRawDerivative] at hDerivative
    simpa only [reciprocal] using hDerivative
  have hProduct := congrArg (fun derivative => derivative vector)
    (mvfderiv_mul
      ((hFirstSmooth inner).mdifferentiableAt (by simp))
      (hReciprocalSmooth.mdifferentiableAt (by simp)))
  have hProductApply :
      mvfderiv throatCoverModelWithCorners
          (first inner * reciprocal) boundary vector =
        first inner boundary *
            mvfderiv throatCoverModelWithCorners reciprocal boundary vector +
          reciprocal boundary *
            mvfderiv throatCoverModelWithCorners (first inner) boundary
              vector := by
    simpa only [add_apply, smul_apply, smul_eq_mul] using hProduct
  have hCandidateSecond :
      candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
          period hPeriod metric outer inner current boundary =
        normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
              (normal, parameter) boundary * reciprocal boundary -
          2 * raw boundary * first outer boundary * first inner boundary *
            reciprocal boundary ^ 2 := by
    unfold candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
    change
      normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
            (current.1.2, current.2) boundary *
          candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
            period hPeriod metric current boundary -
        2 * (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
              metric current boundary *
            normalBoundaryC2ScaledRawSpatialFirst period hPeriod outer
              (current.1.2, current.2) boundary *
            normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
              (current.1.2, current.2) boundary *
            candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
              period hPeriod metric current boundary ^ 2) = _
    rw [hCurrentNormal, hCurrentParameter, hRawEvaluation,
      hReciprocalEvaluation]
    dsimp only [first]
    ring
  rw [hCandidateSecond, hCandidateFirst, hProductApply,
    hReciprocalDerivative, hFirstDerivative]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem test_mvfderiv_real_eq_mfderiv
    (field : CutThroatBoundary period hPeriod → Real)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mvfderiv throatCoverModelWithCorners field boundary vector =
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        field boundary vector := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryLatitudeSpatialFirst_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
        period hPeriod metric index
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          Real.arctan (parameter *
            normalDisplacementOrientationScalar period hPeriod displacement
              point)) boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) := by
  have hLatitude := normalGraphLatitude_mvfderiv_frame period hPeriod
    displacement parameter boundary index
  unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
  change
    (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) index) *
      candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary = _
  rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
  rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
        metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) by rfl]
  rw [hLatitude]
  ring

theorem test_candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (field : CutThroatBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation
        period hPeriod metric field hField
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      field (boundary, Real.arctan (parameter *
        normalDisplacementOrientationScalar period hPeriod displacement
          boundary)) := by
  rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_apply]
  change field (boundary, Real.arctan (parameter *
      normalBoundaryC2JetCoreValueAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement))) = _
  rw [normalBoundaryC2JetCoreValueAt_smooth]

set_option backward.isDefEq.respectTransparency false in
theorem
    test_candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
        period hPeriod metric outer inner row
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric inner row
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let latitude : CutThroatBoundary period hPeriod → Real := fun point =>
    Real.arctan (parameter *
      normalDisplacementOrientationScalar period hPeriod displacement point)
  let slope (index : NormalBoundaryTangentIndex period hPeriod) :
      CutThroatBoundary period hPeriod → Real := fun point =>
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
      period hPeriod metric index current point
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
    horizontalGraph + slope inner * verticalGraph
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hLatitudeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude := by
    exact Real.contDiff_arctan.contMDiff.comp
      (contMDiff_const.mul
        (normalDisplacementOrientationScalar_contMDiff
          period hPeriod displacement))
  have hHorizontalSmooth : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ horizontal :=
    normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric inner row
  have hVerticalSmooth : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ vertical :=
    normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row
  have hHorizontalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ horizontalGraph :=
    hHorizontalSmooth.comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hVerticalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ verticalGraph :=
    hVerticalSmooth.comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hSlopeAt (index : NormalBoundaryTangentIndex period hPeriod)
      (point : CutThroatBoundary period hPeriod) :
      slope index point =
        mvfderiv throatCoverModelWithCorners latitude point
          (frame.vectorAt point index) := by
    exact test_candidateANormalBoundaryLatitudeSpatialFirst_smooth
      period hPeriod metric tensor displacement parameter point index
  let latitudeField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    { toFun := latitude
      contMDiff_toFun := hLatitudeSmooth }
  have hSlopeFunction (index : NormalBoundaryTangentIndex period hPeriod) :
      slope index =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          latitudeField index).toFun := by
    funext point
    rw [hSlopeAt]
    change mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point index) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame latitudeField point index
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hSlopeSmooth (index : NormalBoundaryTangentIndex period hPeriod) :
      ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞ (slope index) := by
    rw [hSlopeFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      latitudeField index).contMDiff_toFun
  have hHorizontalSource :
      candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
          period hPeriod metric outer inner row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
    rw [test_candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hHorizontalLatitude :
      candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
          period hPeriod metric inner row current boundary =
        normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
    rw [test_candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hVerticalSource :
      candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
          period hPeriod metric outer row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer vertical
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
    rw [test_candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hVerticalLatitude :
      candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
          period hPeriod metric row current boundary =
        normalBoundaryLatitudeFieldDerivative period hPeriod vertical
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
    rw [test_candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hHorizontalValue :
      candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current boundary =
        horizontalGraph boundary := by
    rw [candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation_apply]
    change horizontal
        (boundary, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod boundary
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) = _
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hVerticalValue :
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row current boundary =
        verticalGraph boundary := by
    rw [candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply]
    change vertical
        (boundary, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod boundary
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) = _
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hHorizontalChain :=
    test_normalBoundarySmoothCollarField_mvfderiv_graph period hPeriod
      horizontal hHorizontalSmooth latitude hLatitudeSmooth boundary outer
  change mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) horizontalGraph boundary vector =
    normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
        (boundary, latitude boundary) +
      mvfderiv throatCoverModelWithCorners latitude boundary vector •
        normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
          (boundary, latitude boundary) at hHorizontalChain
  rw [← test_mvfderiv_real_eq_mfderiv period hPeriod horizontalGraph boundary
    vector] at hHorizontalChain
  rw [← hSlopeAt outer boundary] at hHorizontalChain
  have hVerticalChain :=
    test_normalBoundarySmoothCollarField_mvfderiv_graph period hPeriod
      vertical hVerticalSmooth latitude hLatitudeSmooth boundary outer
  change mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) verticalGraph boundary vector =
    normalBoundaryHorizontalFieldDerivative period hPeriod outer vertical
        (boundary, latitude boundary) +
      mvfderiv throatCoverModelWithCorners latitude boundary vector •
        normalBoundaryLatitudeFieldDerivative period hPeriod vertical
          (boundary, latitude boundary) at hVerticalChain
  rw [← test_mvfderiv_real_eq_mfderiv period hPeriod verticalGraph boundary
    vector] at hVerticalChain
  rw [← hSlopeAt outer boundary] at hVerticalChain
  have hSlopeDerivative :
      mvfderiv throatCoverModelWithCorners (slope inner) boundary vector =
        candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
          period hPeriod metric outer inner current boundary := by
    exact (test_candidateANormalBoundaryLatitudeSpatialSecond_smooth
      period hPeriod metric tensor displacement parameter boundary outer
        inner).symm
  have hProduct := congrArg (fun derivative => derivative vector)
    (mvfderiv_mul
      ((hSlopeSmooth inner).mdifferentiableAt (by simp))
      (hVerticalGraphSmooth.mdifferentiableAt (by simp)))
  have hProductApply :
      mvfderiv throatCoverModelWithCorners
          (slope inner * verticalGraph) boundary vector =
        slope inner boundary *
            mvfderiv throatCoverModelWithCorners verticalGraph boundary vector +
          verticalGraph boundary *
            mvfderiv throatCoverModelWithCorners (slope inner) boundary
              vector := by
    simpa only [add_apply, smul_apply, smul_eq_mul] using hProduct
  have hSum := congrArg (fun derivative => derivative vector)
    (mvfderiv_add
      (hHorizontalGraphSmooth.mdifferentiableAt (by simp))
      (((hSlopeSmooth inner).mul hVerticalGraphSmooth).mdifferentiableAt
        (by simp)))
  have hGraphDerivative :
      mvfderiv throatCoverModelWithCorners graphCoefficient boundary vector =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
              (boundary, latitude boundary) +
          slope outer boundary *
              normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
                (boundary, latitude boundary) +
          candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
              period hPeriod metric outer inner current boundary *
            verticalGraph boundary +
          slope inner boundary *
            (normalBoundaryHorizontalFieldDerivative period hPeriod outer
                vertical (boundary, latitude boundary) +
              slope outer boundary *
                normalBoundaryLatitudeFieldDerivative period hPeriod vertical
                  (boundary, latitude boundary)) := by
    change mvfderiv throatCoverModelWithCorners
        (horizontalGraph + slope inner * verticalGraph) boundary vector = _
    rw [show mvfderiv throatCoverModelWithCorners
          (horizontalGraph + slope inner * verticalGraph) boundary vector =
        mvfderiv throatCoverModelWithCorners horizontalGraph boundary vector +
          mvfderiv throatCoverModelWithCorners
            (slope inner * verticalGraph) boundary vector by
      simpa only [add_apply] using hSum]
    rw [hHorizontalChain, hProductApply, hVerticalChain, hSlopeDerivative]
    ring
  have hCandidateFormula :
      candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
              (boundary, latitude boundary) +
          slope outer boundary *
              normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
                (boundary, latitude boundary) +
          candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
              period hPeriod metric outer inner current boundary *
            verticalGraph boundary +
          slope inner boundary *
            (normalBoundaryHorizontalFieldDerivative period hPeriod outer
                vertical (boundary, latitude boundary) +
              slope outer boundary *
                normalBoundaryLatitudeFieldDerivative period hPeriod vertical
                  (boundary, latitude boundary)) := by
    unfold candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
    change
      candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
            period hPeriod metric outer inner row current boundary +
        slope outer boundary *
          candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
            period hPeriod metric inner row current boundary +
        candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
            period hPeriod metric outer inner current boundary *
          candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
            period hPeriod metric row current boundary +
        slope inner boundary *
          (candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
              period hPeriod metric outer row current boundary +
            slope outer boundary *
              candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
                period hPeriod metric row current boundary) = _
    rw [hHorizontalSource, hHorizontalLatitude, hVerticalValue,
      hVerticalSource, hVerticalLatitude]
  have hCoefficient :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point) = graphCoefficient := by
    funext point
    unfold graphCoefficient
    change
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point =
        horizontalGraph point + slope inner point * verticalGraph point
    rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
    change horizontalGraph point +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) * verticalGraph point) = _
    unfold slope
    unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    change horizontalGraph point +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) * verticalGraph point) =
      horizontalGraph point +
        (normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement, parameter) point *
          candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
            period hPeriod metric current point) * verticalGraph point
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
          metric current point =
        parameter * normalBoundaryC2JetCoreValueAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) by rfl]
    rw [normalBoundaryC2ScaledRawSpatialFirst_apply]
    ring
  rw [hCandidateFormula, ← hGraphDerivative, hCoefficient]

/-- Regular-frame coefficient of the already installed smooth canonical unit
normal, pulled back to the orientation double at fixed graph parameter. -/
def test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (row : Fin 4) (boundary : CutThroatBoundary period hPeriod) : Real :=
  normalBoundaryRegularFrameCoefficient period hPeriod metric
    (fun current : CutThroatBoundary period hPeriod × Real =>
      normalGraphCanonicalMetricUnitNormalLift period hPeriod variedMetric
        displacement parameter hNonNull current.1)
    row (boundary, 0)

theorem
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (row : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
        period hPeriod metric variedMetric displacement parameter hNonNull
          row) := by
  have hLift : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : CutThroatBoundary period hPeriod × Real =>
        normalGraphCanonicalMetricUnitNormalLift period hPeriod variedMetric
          displacement parameter hNonNull current.1) :=
    (normalGraphCanonicalMetricUnitNormalLift_contMDiff period hPeriod
      variedMetric displacement parameter hNonNull).comp contMDiff_fst
  have hCoefficient := normalBoundaryRegularFrameCoefficient_contMDiff
    period hPeriod metric _ hLift row
  exact hCoefficient.comp (contMDiff_id.prodMk contMDiff_const)

theorem
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod) :
    (∑ row : Fin 4,
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            row boundary •
        metric.frame row
          (normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter))) =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
  symm
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter))
    (normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
      displacement parameter hNonNull boundary)

set_option backward.isDefEq.respectTransparency false in
theorem test_candidateANormalBoundaryActualMetricMatrix_mvfderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (row column : Fin 4) :
    mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) row column point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) =
      ∑ regular : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            regular row column
            (normalGraphOrientationDouble period hPeriod displacement
              (boundary, parameter)) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let graph : CutThroatBoundary period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) := fun point =>
    normalGraphOrientationDouble period hPeriod displacement (point, parameter)
  let field := test_smoothRegularGeneralMetricActualMatrix period hPeriod metric
    tensor row column
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
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
  have hGraphSmooth : ContMDiff throatCoverModelWithCorners
      coverModelWithCorners ∞ graph := by
    exact (normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp
      (contMDiff_id.prodMk contMDiff_const)
  have hComp := mfderiv_comp_apply boundary
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (hGraphSmooth.mdifferentiableAt (by simp)) vector
  have hTangent := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary outer
  change mvfderiv throatCoverModelWithCorners
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column point) boundary vector = _
  rw [hFunction, test_mvfderiv_real_eq_mfderiv, hComp]
  change mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
      field.toFun (graph boundary)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
          vector) = _
  change (∑ regular : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer regular current boundary •
        metric.frame regular (graph boundary)) =
    mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
      vector at hTangent
  rw [← hTangent, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro regular _
  change _ * mvfderiv coverModelWithCorners field.toFun (graph boundary)
      ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric).vectorAt
        (graph boundary) regular) = _
  rw [← frameDerivative_eq_mfderiv]
  unfold field graph current
  rw [test_regularGeneralMetricC0MetricFirstDerivative_smooth]

set_option backward.isDefEq.respectTransparency false in
/-- The already installed finite-frame projection solves the smooth induced
metric pairing equation on every admissible graph. -/
theorem test_candidateANormalBoundaryTangentialProjection_pairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    (∑ index : NormalBoundaryTangentIndex period hPeriod,
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
            period hPeriod metric index
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary *
        candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            index outer boundary) =
      candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric outer
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let projection :=
    test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric current boundary
  let vector := frame.vectorAt boundary outer
  have hSynthesis : projection =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index current boundary •
          frame.vectorAt boundary index := by
    unfold projection
      test_candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    exact intrinsicThroatFiniteFrameSynthesisAt_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary _
  have hMusical := congrArg (fun covector => covector vector)
    (test_candidateANormalBoundaryTangentialProjectionVector_smooth_musical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent)
  change normalBoundarySmoothGraphInducedMetricMusical period hPeriod
      variedMetric displacement parameter boundary projection vector =
    test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
      variedMetric displacement parameter boundary vector at hMusical
  have hInduced (index : NormalBoundaryTangentIndex period hPeriod) :
      candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
          period hPeriod metric current index outer boundary =
        normalBoundarySmoothGraphInducedMetricMusical period hPeriod
          variedMetric displacement parameter boundary
            (frame.vectorAt boundary index) vector := by
    simpa [current, frame, vector] using
      (candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_pulledBackMusical
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary index outer)
  have hVertical :
      candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
          period hPeriod metric outer current boundary =
        test_normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
          variedMetric displacement parameter boundary vector := by
    simpa [current, frame, vector] using
      (test_candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary outer)
  rw [hSynthesis, map_sum] at hMusical
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hMusical
  simp_rw [← hInduced] at hMusical
  rw [← hVertical] at hMusical
  simpa [current, frame, vector] using hMusical

/-- Subtracting that solved projection makes the completed metric normal
orthogonal to each completed graph generator. -/
theorem test_candidateANormalBoundaryMetricNormal_pairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
            period hPeriod metric first
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            first second boundary *
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric outer second
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary) = 0 := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let projection := fun index : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric index current boundary
  let vertical := fun first : Fin 4 =>
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric first current boundary
  let tangent := fun index : NormalBoundaryTangentIndex period hPeriod =>
    fun first : Fin 4 =>
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index first current boundary
  let actual := fun first second : Fin 4 =>
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
      period hPeriod metric current first second boundary
  have hProjection :
      (∑ index : NormalBoundaryTangentIndex period hPeriod,
        projection index *
          (∑ first : Fin 4, ∑ second : Fin 4,
            tangent index first * actual first second * tangent outer second)) =
        ∑ first : Fin 4, ∑ second : Fin 4,
          vertical first * actual first second * tangent outer second := by
    simpa [current, projection, vertical, tangent, actual,
      candidateANormalBoundaryInducedMetricMatrixFiberEvaluation,
      candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation] using
        test_candidateANormalBoundaryTangentialProjection_pairing_smooth
          period hPeriod metric tensor variedMetric hVaried displacement
            parameter boundary outer hCurrent
  unfold
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  change (∑ first : Fin 4, ∑ second : Fin 4,
      (vertical first - ∑ index : NormalBoundaryTangentIndex period hPeriod,
          projection index * tangent index first) *
        actual first second * tangent outer second) = 0
  calc
    _ = (∑ first : Fin 4, ∑ second : Fin 4,
          vertical first * actual first second * tangent outer second) -
        ∑ index : NormalBoundaryTangentIndex period hPeriod,
          projection index *
            (∑ first : Fin 4, ∑ second : Fin 4,
              tangent index first * actual first second *
                tangent outer second) := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
        Finset.mul_sum]
      congr 1
      calc
        (∑ first : Fin 4, ∑ second : Fin 4,
          ∑ index : NormalBoundaryTangentIndex period hPeriod,
            projection index * tangent index first * actual first second *
              tangent outer second) =
            ∑ first : Fin 4,
              ∑ index : NormalBoundaryTangentIndex period hPeriod,
                ∑ second : Fin 4,
                  projection index * tangent index first * actual first second *
                    tangent outer second := by
              apply Finset.sum_congr rfl
              intro first _
              rw [Finset.sum_comm]
        _ = ∑ index : NormalBoundaryTangentIndex period hPeriod,
              ∑ first : Fin 4, ∑ second : Fin 4,
                projection index * tangent index first * actual first second *
                  tangent outer second := by
            rw [Finset.sum_comm]
        _ = ∑ index : NormalBoundaryTangentIndex period hPeriod,
              ∑ first : Fin 4, ∑ second : Fin 4,
                projection index * (tangent index first * actual first second *
                  tangent outer second) := by
            apply Finset.sum_congr rfl
            intro index _
            apply Finset.sum_congr rfl
            intro first _
            apply Finset.sum_congr rfl
            intro second _
            ring
    _ = 0 := by rw [hProjection]; ring

set_option backward.isDefEq.respectTransparency false in
/-- The historical unit normal and the completed graph tangent are exactly
orthogonal in the common installed regular frame. -/
theorem test_candidateANormalBoundaryMetricUnitNormalGraphTangent_orthogonal_smooth
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
    (boundary : CutThroatBoundary period hPeriod)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull
              first boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            first second boundary *
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric outer second
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary) = 0 := by
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let normal := ∑ first : Fin 4,
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            first boundary •
      metric.frame first point
  let tangent := ∑ second : Fin 4,
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer second
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
            metric (tensor, displacement), parameter) boundary •
      metric.frame second point
  have hNormal : normal =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
    simpa [normal, point] using
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_reconstructs
        period hPeriod metric variedMetric displacement parameter hNonNull
          boundary
  have hTangent : tangent =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun current : CutThroatBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (current, parameter)) boundary vector := by
    simpa [tangent, point, vector] using
      candidateANormalBoundaryGraphTangent_smooth_reconstructs period hPeriod
        metric tensor displacement parameter boundary outer
  have hMetricNormalOrthogonal :
      variedMetric.tensor.tensor point
          (test_candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
            metric tensor displacement parameter boundary) tangent = 0 := by
    have hExpansion :
        variedMetric.tensor.tensor point
            (test_candidateANormalBoundaryMetricNormalVector_smooth period
              hPeriod metric tensor displacement parameter boundary) tangent =
          ∑ first : Fin 4, ∑ second : Fin 4,
            candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric first
                  (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                    metric (tensor, displacement), parameter) boundary *
              candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                  period hPeriod metric
                  (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                    metric (tensor, displacement), parameter)
                  first second boundary *
                candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric outer second
                  (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                    metric (tensor, displacement), parameter) boundary := by
      unfold test_candidateANormalBoundaryMetricNormalVector_smooth tangent
      rw [variedMetric.tensor.symmetric point]
      rw [map_sum]
      simp only [map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro first _
      rw [map_sum]
      simp only [map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro second _
      rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary]
      rw [variedMetric.tensor.symmetric]
      ring
    rw [hExpansion]
    exact test_candidateANormalBoundaryMetricNormal_pairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary outer
        hCurrent.1.2
  have hUnitNormalOrthogonal :
      variedMetric.tensor.tensor point
          (normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
            displacement parameter hNonNull boundary) tangent = 0 := by
    rw [← test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter boundary hCurrent hNonNull hRootNonneg]
    rw [test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hMetricNormalOrthogonal, mul_zero]
  have hExpansion :
      variedMetric.tensor.tensor point normal tangent =
        ∑ first : Fin 4, ∑ second : Fin 4,
          test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
                period hPeriod metric variedMetric displacement parameter
                  hNonNull first boundary *
            candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                period hPeriod metric
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter)
                first second boundary *
              candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer second
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter) boundary := by
    unfold normal tangent
    rw [variedMetric.tensor.symmetric point]
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro second _
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    rw [variedMetric.tensor.symmetric]
    ring
  rw [← hExpansion, hNormal]
  exact hUnitNormalOrthogonal

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end
end JanusFormal
