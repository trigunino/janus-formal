import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussLocalSectionReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussWeingartenClosure4D

/-!
# Historical Weingarten coordinate pairing for H10

The completed regular-frame Weingarten scalar is rewritten as one local metric
pairing.  Its first vector is reconstructed from the already installed
normal-coefficient derivative and completed Christoffel coefficients; its
second vector is the already installed historical graph tangent coordinate.
No connection, normal, metric, frame, chart, or boundary datum is added.
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
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance historicalWeingartenCoordinateCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance historicalWeingartenCoordinateCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalWeingartenCoordinateOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalWeingartenCoordinateOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalWeingartenCoordinateEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalWeingartenCoordinateEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Coordinate representative of the historical covariant derivative of the
physical unit normal along one completed graph tangent.  Both the coefficient
derivative and connection coefficients are those already used by the
completed Gauss--Weingarten reduction. -/
def candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
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
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4 :=
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  ∑ row : Fin 4,
    (candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            outer row boundary +
      ∑ regular : Fin 4, ∑ upper : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular current boundary *
          candidateANormalBoundaryChristoffelFiberEvaluation
              period hPeriod metric row regular upper current boundary *
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter hNonNull
                upper boundary) •
      pulledRegularFrameVector period hPeriod metric patch row coordinate

set_option backward.isDefEq.respectTransparency false in
/-- The historical regular-frame Weingarten scalar is exactly the local metric
pairing of its reconstructed covariant-normal derivative with the historical
graph tangent coordinate. -/
theorem
    candidateANormalBoundaryHistoricalWeingartenRegularPairingAt_eq_coordinatePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull outer boundary patch coordinate)
        (candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
          metric inner
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter)
            boundary patch coordinate) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  have hMetric (row column : Fin 4) :
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch row coordinate)
          (pulledRegularFrameVector period hPeriod metric patch column
            coordinate) =
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current row column boundary := by
    rw [candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
      period hPeriod metric tensor variedMetric hVaried patch coordinate]
    rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    rw [hAt]
  unfold candidateANormalBoundaryHistoricalWeingartenRegularPairingAt
    candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
    candidateANormalBoundaryGraphTangentCoordinates_historical
  dsimp only [current]
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Eq.symm
  rw [← Finset.sum_add_distrib]
  simp_rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro column _
  rw [hMetric]
  ring

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
