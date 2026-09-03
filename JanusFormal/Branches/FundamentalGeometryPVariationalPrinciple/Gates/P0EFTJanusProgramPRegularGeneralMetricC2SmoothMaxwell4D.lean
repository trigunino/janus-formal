import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D

/-! # Exact Maxwell pairing of a smooth varied metric -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Continuous value of the completed Maxwell pairing. -/
def regularGeneralMetricC0MaxwellPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (regularGeneralMetricC2MaxwellPairing period hPeriod metric first second
      variation)

theorem regularGeneralMetricC0MaxwellPairing_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC0MaxwellPairing period hPeriod metric first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  exact (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff
    |>.contDiffOn.comp
      (regularGeneralMetricC2MaxwellPairing_contDiffOn_two period hPeriod metric
        first second) (fun _ _ => mem_univ _)

/-- Pointwise identification with the intrinsic pairing of the genuine affine
metric. -/
theorem regularGeneralMetricC0MaxwellPairing_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈ regularGeneralMetricC2Domain period hPeriod metric)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0MaxwellPairing period hPeriod metric first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) (patch.coordinateMap coordinate) =
      globalMaxwellPairing period hPeriod variedMetric first second
        (patch.coordinateMap coordinate) := by
  unfold regularGeneralMetricC0MaxwellPairing
    regularGeneralMetricC2MaxwellPairing c2MaxwellMatrixContraction
  simp only [map_sum, ContinuousMap.sum_apply]
  change (∑ component : Fin 2, matrixMaxwellContraction
      (regularGeneralMetricC0SmoothInverseMatrix period hPeriod metric tensor
        (patch.coordinateMap coordinate))
      (fun row column => regularFrameGaugeCurvatureCoefficient period hPeriod
        metric first component row column (patch.coordinateMap coordinate))
      (fun row column => regularFrameGaugeCurvatureCoefficient period hPeriod
        metric second component row column (patch.coordinateMap coordinate))) = _
  rw [globalMaxwellPairing_eq_local]
  change _ = ∑ component : Fin 2, matrixMaxwellContraction
    (localMetricMatrix period hPeriod variedMetric patch coordinate)⁻¹
    (localGaugeCurvatureMatrix period hPeriod first component patch coordinate)
    (localGaugeCurvatureMatrix period hPeriod second component patch coordinate)
  apply Finset.sum_congr rfl
  intro component _
  have hInvariant := matrixMaxwellContraction_congruence
    (regularFrameChangeMatrix period hPeriod metric patch coordinate)
    (localMetricMatrix period hPeriod variedMetric patch coordinate)
    (localGaugeCurvatureMatrix period hPeriod first component patch coordinate)
    (localGaugeCurvatureMatrix period hPeriod second component patch coordinate)
    (regularFrameChangeMatrix_isUnit period hPeriod metric patch coordinate)
  rw [← smoothActualMetricMatrix_congruence period hPeriod metric tensor
      variedMetric hVaried patch coordinate,
    ← regularFrameGaugeCurvatureMatrix_congruence period hPeriod metric first
      component patch coordinate,
    ← regularFrameGaugeCurvatureMatrix_congruence period hPeriod metric second
      component patch coordinate] at hInvariant
  rw [regularGeneralMetricC0InverseMetricMatrix_smooth_eq_inv period hPeriod
    metric tensor hVariation (patch.coordinateMap coordinate)]
  exact hInvariant

/-- Global field identification. -/
theorem regularGeneralMetricC0MaxwellPairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈ regularGeneralMetricC2Domain period hPeriod metric)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0MaxwellPairing period hPeriod metric first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothMaxwellPairing period hPeriod variedMetric first second) := by
  apply ContinuousMap.ext
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  exact regularGeneralMetricC0MaxwellPairing_smooth_apply period hPeriod metric
    tensor variedMetric hVaried hVariation first second patch coordinate

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D
end JanusFormal
