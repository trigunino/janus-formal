import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D

/-! # Exact Ricci velocity from the regular-frame connection -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Index4 := Fin 4

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedSpace

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Fréchet derivative, in the metric chart, of one connection coefficient. -/
def regularGeneralMetricC0ChristoffelFDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Index4) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (fun variation => regularGeneralMetricC0Christoffel period hPeriod metric
      variation upper first second) 0

theorem regularGeneralMetricC0Christoffel_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Index4) :
    HasFDerivAt
      (fun variation => regularGeneralMetricC0Christoffel period hPeriod metric
        variation upper first second)
      (regularGeneralMetricC0ChristoffelFDerivativeAtZero
        period hPeriod metric upper first second) 0 := by
  exact (((regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
    upper first second).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by simp)).hasFDerivAt

/-- Fréchet derivative of the stored regular-frame derivative of a
connection coefficient. -/
def regularGeneralMetricC0ChristoffelSpatialFDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Index4) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (fun variation => regularGeneralMetricC0ChristoffelDerivative
      period hPeriod metric variation derivative upper first second) 0

theorem regularGeneralMetricC0ChristoffelDerivative_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Index4) :
    HasFDerivAt
      (fun variation => regularGeneralMetricC0ChristoffelDerivative
        period hPeriod metric variation derivative upper first second)
      (regularGeneralMetricC0ChristoffelSpatialFDerivativeAtZero
        period hPeriod metric derivative upper first second) 0 := by
  exact (((regularGeneralMetricC0ChristoffelDerivative_contDiffOn
    period hPeriod metric derivative upper first second).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by simp)).hasFDerivAt

/-- An anholonomic frame, its base connection, and the two connection
velocities that enter the Ricci product rule. -/
structure RegularFrameConnectionVariationJet4 where
  structureCoefficient : Index4 → Index4 → Index4 → Real
  connection : Index4 → Index4 → Index4 → Real
  variation : Index4 → Index4 → Index4 → Real
  frameVariationDerivative :
    Index4 → Index4 → Index4 → Index4 → Real

/-- Product-rule Ricci velocity in a fixed, possibly anholonomic, frame. -/
def regularFrameRicciVelocityFromConnection
    (jet : RegularFrameConnectionVariationJet4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    (jet.frameVariationDerivative contracted contracted second first -
      jet.frameVariationDerivative second contracted contracted first +
      (∑ auxiliary : Index4,
        (jet.connection auxiliary second first *
            jet.variation contracted contracted auxiliary +
          jet.connection contracted contracted auxiliary *
            jet.variation auxiliary second first)) -
      (∑ auxiliary : Index4,
        (jet.connection auxiliary contracted first *
            jet.variation contracted second auxiliary +
          jet.connection contracted second auxiliary *
            jet.variation auxiliary contracted first)) -
      ∑ auxiliary : Index4,
        jet.structureCoefficient contracted second auxiliary *
          jet.variation contracted auxiliary first)

/-- The actual C² connection-variation jet at a quotient point. -/
def regularGeneralMetricC2ConnectionVariationJetAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    RegularFrameConnectionVariationJet4 where
  structureCoefficient := fun first second upper =>
    regularFrameStructureCoefficientContinuous period hPeriod metric
      first second upper point
  connection := fun upper first second =>
    regularGeneralMetricC0Christoffel period hPeriod metric 0
      upper first second point
  variation := fun upper first second =>
    regularGeneralMetricC0ChristoffelFDerivativeAtZero period hPeriod metric
      upper first second direction point
  frameVariationDerivative := fun derivative upper first second =>
    regularGeneralMetricC0ChristoffelSpatialFDerivativeAtZero
      period hPeriod metric derivative upper first second direction point

set_option maxHeartbeats 5000000 in
/-- The abstract Ricci velocity from Gate479 is exactly the product-rule
velocity of the concrete regular-frame connection. -/
theorem regularGeneralMetricC0RicciVelocityAt_eq_connection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : Index4) :
    regularGeneralMetricC0RicciVelocityAt period hPeriod metric direction point
        first second =
      regularFrameRicciVelocityFromConnection
        (regularGeneralMetricC2ConnectionVariationJetAt
          period hPeriod metric direction point) first second := by
  have hTerm (contracted : Index4) :=
    (((regularGeneralMetricC0ChristoffelDerivative_hasFDerivAt_zero
        period hPeriod metric contracted contracted second first).sub
      (regularGeneralMetricC0ChristoffelDerivative_hasFDerivAt_zero
        period hPeriod metric second contracted contracted first)).add
      (HasFDerivAt.fun_sum (u := Finset.univ) fun auxiliary _ =>
        (regularGeneralMetricC0Christoffel_hasFDerivAt_zero
            period hPeriod metric auxiliary second first).mul
          (regularGeneralMetricC0Christoffel_hasFDerivAt_zero
            period hPeriod metric contracted contracted auxiliary))).sub
      (HasFDerivAt.fun_sum (u := Finset.univ) fun auxiliary _ =>
        (regularGeneralMetricC0Christoffel_hasFDerivAt_zero
            period hPeriod metric auxiliary contracted first).mul
          (regularGeneralMetricC0Christoffel_hasFDerivAt_zero
            period hPeriod metric contracted second auxiliary)) |>.sub
      (HasFDerivAt.fun_sum (u := Finset.univ) fun auxiliary _ =>
        (hasFDerivAt_const
          (x := (0 : RegularGeneralMetricC2Core period hPeriod metric))
          (c := regularFrameStructureCoefficientContinuous
            period hPeriod metric contracted second auxiliary)).mul
          (regularGeneralMetricC0Christoffel_hasFDerivAt_zero
            period hPeriod metric contracted auxiliary first))
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) fun contracted _ =>
    hTerm contracted
  change HasFDerivAt
    (fun variation => regularGeneralMetricC0Ricci period hPeriod metric
      variation first second) _ 0 at hSum
  have hApply := congrArg (fun derivative => derivative direction) hSum.fderiv
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simpa only [regularGeneralMetricC0RicciVelocityAt,
    regularGeneralMetricC0RicciDerivativeAtZero,
    regularFrameRicciVelocityFromConnection,
    regularGeneralMetricC2ConnectionVariationJetAt,
    regularGeneralMetricC0ChristoffelFDerivativeAtZero,
    regularGeneralMetricC0ChristoffelSpatialFDerivativeAtZero,
    Pi.mul_apply, Pi.zero_apply, Pi.add_apply, Pi.sub_apply,
    sum_apply, add_apply, sub_apply, smul_apply, zero_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    zero_mul, mul_zero, zero_add, add_zero, smul_eq_mul] using hPoint

/-- Gate marker for the concrete connection formula for the C² Ricci
velocity. -/
theorem regular_general_metric_c2_ricci_connection_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : Index4) :
    regularGeneralMetricC0RicciVelocityAt period hPeriod metric direction point
        first second =
      regularFrameRicciVelocityFromConnection
        (regularGeneralMetricC2ConnectionVariationJetAt
          period hPeriod metric direction point) first second :=
  regularGeneralMetricC0RicciVelocityAt_eq_connection
    period hPeriod metric direction point first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
end JanusFormal
