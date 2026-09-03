import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetricDerivative4D

/-!
# Exact second derivative of the smooth varied metric

The completed C² metric matrix already stores the exact two spacetime jets
of every smooth affine metric variation.  This file exposes the missing
nonzero second-derivative bridge used by the curvature formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Smooth scalar field represented by the ordered second derivative of one
actual-metric coefficient in the fixed regular frame. -/
def regularGeneralMetricSmoothActualMetricSecondDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Fin 4) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    frameSecondDerivative period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column)
      point outer inner
  contMDiff_toFun :=
    (contMDiff_pi_space.mp (contMDiff_pi_space.mp
      (frameSecondDerivative_contMDiff period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row column)) outer) inner)

/-- Pointwise exactness of the completed second metric derivative for every
smooth, not necessarily zero, variation. -/
theorem regularGeneralMetricC0MetricSecondDerivative_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        outer inner row column point =
      regularGeneralMetricSmoothActualMetricSecondDerivative period hPeriod
        metric tensor outer inner row column point := by
  unfold regularGeneralMetricC0MetricSecondDerivative
    regularGeneralMetricSmoothActualMetricSecondDerivative
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
  exact regularFrameC2SecondDerivative_smooth period hPeriod metric outer inner
    (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
      period hPeriod metric tensor row column) point

/-- Continuous-field form of the exact nonzero second-jet bridge. -/
theorem regularGeneralMetricC0MetricSecondDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Fin 4) :
    regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        outer inner row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularGeneralMetricSmoothActualMetricSecondDerivative period hPeriod
          metric tensor outer inner row column) := by
  apply ContinuousMap.ext
  intro point
  exact regularGeneralMetricC0MetricSecondDerivative_smooth_apply period
    hPeriod metric tensor outer inner row column point

/-- In a holonomic patch, differentiating the completed first metric jet of
a smooth nonzero variation gives its completed second metric jet. -/
theorem regularGeneralMetricC0MetricFirstDerivative_smooth_local_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (outer inner row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            inner row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch outer
          coordinate) =
      regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        outer inner row column (patch.coordinateMap coordinate) := by
  have hFunction :
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          inner row column (patch.coordinateMap current)) =
        (frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column) inner).toFun ∘
          patch.coordinateMap := by
    funext current
    exact
      candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth
        period hPeriod metric tensor inner row column
          (patch.coordinateMap current)
  rw [hFunction,
    regularGeneralMetricC0MetricSecondDerivative_smooth_apply]
  simpa only [regularGeneralMetricSmoothActualMetricSecondDerivative,
      frameSecondDerivative] using
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row column) inner)
      patch coordinate outer)

/-- Gate marker: both spacetime derivatives of every smooth varied-metric
coefficient are now represented exactly by the completed C² core. -/
theorem regular_general_metric_c2_smooth_actual_metric_second_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Fin 4) :
    regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        outer inner row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularGeneralMetricSmoothActualMetricSecondDerivative period hPeriod
          metric tensor outer inner row column) := by
  exact regularGeneralMetricC0MetricSecondDerivative_smooth period hPeriod
    metric tensor outer inner row column

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D
end JanusFormal
