import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussRawLocalSectionReduction4D

/-!
# Historical covariant-normal germ for terminal H10

This gate begins the final identification of the historical regular-frame
Weingarten derivative with the already installed holonomic local-section
normal derivative.  The first step is purely geometric finite-frame algebra:
the completed Christoffel coefficients reconstruct exactly the local
Levi--Civita derivatives of the pulled regular frame.  No connection, frame,
normal, chart, boundary datum, or axiom is introduced.
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
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance historicalCovariantNormalCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance historicalCovariantNormalCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalCovariantNormalOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantNormalOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalCovariantNormalEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantNormalEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem finiteBasisConnectionReconstruction
    (basis : Module.Basis (Fin 4) Real CoordinateVector)
    (tangent normal : Fin 4 → Real)
    (connection : Fin 4 → Fin 4 → CoordinateVector) :
    (∑ row : Fin 4,
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        tangent regular * basis.repr (connection regular upper) row *
          normal upper) • basis row) =
      ∑ regular : Fin 4, ∑ upper : Fin 4,
        (tangent regular * normal upper) • connection regular upper := by
  classical
  apply basis.repr.injective
  ext row
  simp only [map_sum, map_smul, Finsupp.smul_apply]
  simp [Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro regular _
  apply Finset.sum_congr rfl
  intro upper _
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The regular-frame Christoffel contribution in the historical covariant
normal derivative is exactly the finite sum of the genuine local
Levi--Civita derivatives of the pulled regular frame. -/
theorem
    candidateANormalBoundaryHistoricalRegularConnectionNormalCoordinatesAt_eq_covariantFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
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
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    (∑ row : Fin 4,
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular current boundary *
          candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod
              metric row regular upper current boundary *
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter hNonNull
                upper boundary) •
        pulledRegularFrameVector period hPeriod metric patch row coordinate) =
      ∑ regular : Fin 4, ∑ upper : Fin 4,
        (candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular current boundary *
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter hNonNull
                upper boundary) •
        candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch regular upper coordinate := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let tangent := fun regular : Fin 4 =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric outer regular current boundary
  let normal := fun upper : Fin 4 =>
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull upper
        boundary
  let connection := fun regular upper : Fin 4 =>
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch regular upper coordinate
  have hBasis (row : Fin 4) :
      basis row =
        pulledRegularFrameVector period hPeriod metric patch row coordinate :=
    pulledRegularFrameBasis_apply period hPeriod metric patch coordinate row
  have hChristoffel (row regular upper : Fin 4) :
      candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
          row regular upper current boundary =
        basis.repr (connection regular upper) row := by
    exact candidateANormalBoundaryChristoffel_smooth_apply period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent row regular upper
  have hAlgebra := finiteBasisConnectionReconstruction
    (basis := basis) (tangent := tangent) (normal := normal)
      (connection := connection)
  simp_rw [hBasis] at hAlgebra
  simp_rw [← hChristoffel] at hAlgebra
  simpa only [current, tangent, normal, connection] using hAlgebra

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
