import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothGraphTangentDerivative4D

/-!
# Smooth graph-normal orthogonality for Candidate A

The existing finite-frame projection is shown to solve the induced-metric
pairing equation, hence the completed metric normal and its canonical unit
rescaling are orthogonal to every completed graph generator.  No new normal
or projection is introduced.
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

local instance smoothOrthogonalityCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothOrthogonalityCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothOrthogonalityOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothOrthogonalityOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) smoothOrthogonalityEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) smoothOrthogonalityEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- The installed finite-frame projection solves the smooth induced-metric
pairing equation on every admissible graph. -/
theorem candidateANormalBoundaryTangentialProjection_pairing_smooth
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
    candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric current boundary
  let vector := frame.vectorAt boundary outer
  have hSynthesis : projection =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index current boundary •
          frame.vectorAt boundary index := by
    unfold projection
      candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    exact intrinsicThroatFiniteFrameSynthesisAt_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary _
  have hMusical := congrArg (fun covector => covector vector)
    (candidateANormalBoundaryTangentialProjectionVector_smooth_musical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent)
  change normalBoundarySmoothGraphInducedMetricMusical period hPeriod
      variedMetric displacement parameter boundary projection vector =
    normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
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
        normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
          variedMetric displacement parameter boundary vector := by
    simpa [current, frame, vector] using
      (candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
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
theorem candidateANormalBoundaryMetricNormal_pairing_smooth
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
        candidateANormalBoundaryTangentialProjection_pairing_smooth
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
/-- The historical canonical unit normal and each completed graph tangent are
exactly orthogonal in the common installed regular frame. -/
theorem candidateANormalBoundaryMetricUnitNormalGraphTangent_orthogonal_smooth
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
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
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
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
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
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_reconstructs
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
          (candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
            metric tensor displacement parameter boundary) tangent = 0 := by
    have hExpansion :
        variedMetric.tensor.tensor point
            (candidateANormalBoundaryMetricNormalVector_smooth period
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
      unfold candidateANormalBoundaryMetricNormalVector_smooth tangent
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
    exact candidateANormalBoundaryMetricNormal_pairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary outer
        hCurrent.1.2
  have hUnitNormalOrthogonal :
      variedMetric.tensor.tensor point
          (normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
            displacement parameter hNonNull boundary) tangent = 0 := by
    rw [← candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter boundary hCurrent hNonNull hRootNonneg]
    rw [candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hMetricNormalOrthogonal, mul_zero]
  have hExpansion :
      variedMetric.tensor.tensor point normal tangent =
        ∑ first : Fin 4, ∑ second : Fin 4,
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
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

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
