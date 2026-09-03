import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothKoszulChristoffel4D

/-!
# Global nonzero smooth Christoffel bridge

The completed fixed-frame Christoffel coefficients are identified with the
Levi--Civita coefficients of the genuine affine metric at every bulk chart
point.  This removes the previous restriction to the normal-boundary graph.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The completed Christoffel coefficient of any admissible smooth variation
is the fixed regular-frame coefficient of the genuine varied Levi--Civita
connection. -/
theorem regularGeneralMetricC0Christoffel_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (upper first second : Fin 4) :
    regularGeneralMetricC0Christoffel period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        upper first second (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        upper := by
  classical
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let point := patch.coordinateMap coordinate
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch first second coordinate
  let inverseMatrix : Matrix (Fin 4) (Fin 4) Real := fun row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation row column point
  let actualMatrix : Matrix (Fin 4) (Fin 4) Real := fun row column =>
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column point
  have hKoszul (lower : Fin 4) :
      regularGeneralMetricC0KoszulLower period hPeriod metric variation
          first second lower point =
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          connection
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate) := by
    exact
      candidateANormalBoundaryRegularGeneralMetricC0KoszulLower_smooth_apply
        period hPeriod metric tensor variedMetric hVaried patch coordinate
          first second lower
  have hPairing (lower : Fin 4) :
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          connection
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate) =
        Matrix.mulVec actualMatrix (basis.repr connection) lower := by
    exact
      candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricPairing_mulVec
        period hPeriod metric tensor variedMetric hVaried patch coordinate
          first second lower
  have hProduct : inverseMatrix * actualMatrix = 1 := by
    ext row column
    exact regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
      period hPeriod metric tensor hVariation point row column
  unfold regularGeneralMetricC0Christoffel
  change (∑ lower : Fin 4,
      inverseMatrix upper lower *
        regularGeneralMetricC0KoszulLower period hPeriod metric variation
          first second lower point) = basis.repr connection upper
  simp_rw [hKoszul, hPairing]
  change Matrix.mulVec inverseMatrix
      (Matrix.mulVec actualMatrix (basis.repr connection)) upper =
    basis.repr connection upper
  rw [Matrix.mulVec_mulVec, hProduct, Matrix.one_mulVec]

/-- Gate marker: the nonzero smooth Christoffel bridge holds throughout the
bulk admissible chart, not only on its boundary graph. -/
theorem regular_general_metric_c2_smooth_christoffel_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (upper first second : Fin 4) :
    regularGeneralMetricC0Christoffel period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        upper first second (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        upper := by
  exact regularGeneralMetricC0Christoffel_smooth_apply period hPeriod metric
    tensor variedMetric hVaried hVariation patch coordinate upper first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
end JanusFormal
