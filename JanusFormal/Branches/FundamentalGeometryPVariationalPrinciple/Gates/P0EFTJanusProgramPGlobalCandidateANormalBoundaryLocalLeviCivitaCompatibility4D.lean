import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetricDerivative4D

/-!
# Local Levi-Civita compatibility for the Candidate-A smooth metric core

This file transports the existing holonomic Levi-Civita connection into the
installed regular frame.  It proves metric compatibility and torsion for the
same varied metric represented by the completed smooth matrix.  No connection
or geometric datum is introduced.
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

local instance localLeviCivitaCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance localLeviCivitaCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) localLeviCivitaOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) localLeviCivitaOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) localLeviCivitaEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) localLeviCivitaEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev CandidateANormalBoundaryCoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- The already installed local Levi-Civita derivative of one pulled regular
frame vector along another. -/
def candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Fin 4)
    (coordinate : CandidateANormalBoundaryCoordinateVector) :
    CandidateANormalBoundaryCoordinateVector :=
  fderiv Real
      (pulledRegularFrameVector period hPeriod metric patch second)
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate) +
    localLeviCivitaChristoffelApply period hPeriod variedMetric patch
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate)

/-- The local metric form on two pulled regular-frame vectors is the smooth
actual-metric matrix coefficient. -/
theorem candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (first second : Fin 4) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate) =
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor first second
          (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    coordinateMap_mfderiv_pulledRegularFrameVector]
  exact
    (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried first second
        (patch.coordinateMap coordinate)).symm

/-- Differentiating the preceding local matrix coefficient along a pulled
regular-frame direction gives the installed frame derivative. -/
theorem candidateANormalBoundaryFderivLocalMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (derivative first second : Fin 4) :
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
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor first second)
        (patch.coordinateMap coordinate) derivative := by
  have hFunction :
      (fun current =>
        localMetricCoordinateForm period hPeriod variedMetric patch current
          (pulledRegularFrameVector period hPeriod metric patch first current)
          (pulledRegularFrameVector period hPeriod metric patch second current)) =
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor first second).toFun ∘
            patch.coordinateMap := by
    funext current
    exact
      candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
        period hPeriod metric tensor variedMetric hVaried patch current first
          second
  rw [hFunction]
  exact fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
    metric
      (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor first second)
      patch coordinate derivative

private theorem candidateANormalBoundaryLocalMetricCoordinateForm_add_left
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CandidateANormalBoundaryCoordinateVector) :
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

private theorem candidateANormalBoundaryLocalMetricCoordinateForm_add_right
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CandidateANormalBoundaryCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first (second + third) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first second +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first third := by
  exact map_add
    (localMetricCoordinateForm period hPeriod variedMetric patch coordinate
      first) second third

theorem candidateANormalBoundaryLocalMetricCoordinateForm_sub_right
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CandidateANormalBoundaryCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first (second - third) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first second -
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          first third := by
  exact map_sub
    (localMetricCoordinateForm period hPeriod variedMetric patch coordinate
      first) second third

theorem candidateANormalBoundaryLocalMetricCoordinateForm_symmetric
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CandidateANormalBoundaryCoordinateVector) :
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        first second =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        second first := by
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  exact variedMetric.tensor.symmetric _ _ _

private theorem
    candidateANormalBoundaryFderivLocalMetricCoordinateForm_pulledRegularFrameVector_expand
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (derivative first second : Fin 4) :
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

/-- Metric compatibility of the transported local Levi-Civita derivative in
the installed regular frame. -/
theorem candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (derivative first second : Fin 4) :
    frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor first second)
        (patch.coordinateMap coordinate) derivative =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch derivative first coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch derivative second
              coordinate) := by
  rw [← candidateANormalBoundaryFderivLocalMetricCoordinateForm_pulledRegularFrameVector
    period hPeriod metric tensor variedMetric hVaried patch coordinate
      derivative first second]
  rw [candidateANormalBoundaryFderivLocalMetricCoordinateForm_pulledRegularFrameVector_expand]
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
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector]
  rw [candidateANormalBoundaryLocalMetricCoordinateForm_add_left,
    candidateANormalBoundaryLocalMetricCoordinateForm_add_right]
  abel

/-- Torsion-freeness of the same transported local Levi-Civita derivative. -/
theorem candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_torsion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CandidateANormalBoundaryCoordinateVector)
    (first second : Fin 4) :
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate -
        candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch second first coordinate =
      VectorField.lieBracket Real
        (pulledRegularFrameVector period hPeriod metric patch first)
        (pulledRegularFrameVector period hPeriod metric patch second)
        coordinate := by
  unfold candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
    VectorField.lieBracket
  rw [localLeviCivitaChristoffelApply_symmetric period hPeriod variedMetric
    patch coordinate
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)]
  abel

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
