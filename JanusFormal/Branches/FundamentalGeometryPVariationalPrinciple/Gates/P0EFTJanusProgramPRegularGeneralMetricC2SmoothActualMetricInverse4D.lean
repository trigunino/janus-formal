import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D

/-!
# Exact inverse of the smooth varied metric matrix

The completed inverse matrix cancels the completed actual metric on the full
admissible general-metric domain.  Evaluation gives the corresponding exact
nonzero smooth-metric identity needed to raise Koszul coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- The completed inverse metric is a left inverse of the completed actual
metric throughout the genuine admissible domain. -/
theorem regularGeneralMetricC2InverseMetricMatrix_mul_metricMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (hVariation : variation ∈
      regularGeneralMetricC2Domain period hPeriod metric) :
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric
          variation)
        (regularGeneralMetricC2MetricMatrix period hPeriod metric variation) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  let inverseRelative := generalMetricRelativeC2InverseMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric variation
  let inverseBase := regularFrameMetricInverseC2Matrix period hPeriod metric
  let base := regularFrameMetricC2Matrix period hPeriod metric
  let relative := generalMetricRelativeC2ExtendedMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric variation
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        inverseRelative inverseBase)
      (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        base relative) = _
  calc
    _ = c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        inverseRelative
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          inverseBase
          (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
            base relative)) :=
      c2FiniteMatrixProduct_assoc period hPeriod 4 inverseRelative inverseBase
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          base relative)
    _ = c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        inverseRelative
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
            inverseBase base) relative) := by
      rw [c2FiniteMatrixProduct_assoc period hPeriod 4 inverseBase base
        relative]
    _ = c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        inverseRelative relative := by
      rw [show c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 inverseBase base =
          c2FiniteMatrixIdentity period hPeriod 4 from
        regularFrameMetricInverseC2Matrix_mul_matrix period hPeriod metric,
        c2FiniteMatrixProduct_identity_left]
    _ = _ := generalMetricRelativeC2Inverse_mul_extended period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric variation hVariation.1

/-- Pointwise smooth specialization of inverse-times-metric cancellation. -/
theorem regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    ∀ row column : Fin 4,
      (∑ middle : Fin 4,
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            row middle point *
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor middle column point) =
        if row = column then 1 else 0 := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  have hC2 := regularGeneralMetricC2InverseMetricMatrix_mul_metricMatrix
    period hPeriod metric variation hVariation
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
    at hC2
  have hPoint := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hC2
  simp only [c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_identity] at hPoint
  have hInverseEval :
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric
            variation) point =
        fun row column =>
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            variation row column point := by
    rfl
  have hMetricEval :
      c2FiniteMatrixValueAt period hPeriod 4
          (smoothFiniteMatrixToC2 period hPeriod 4
            (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
              period hPeriod metric tensor)) point =
        fun row column =>
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column point := by
    ext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column)) point = _
    rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    rfl
  rw [hInverseEval, hMetricEval] at hPoint
  intro row column
  have hEntry := congrFun (congrFun hPoint row) column
  simpa only [Matrix.mul_apply, Matrix.one_apply, variation] using hEntry

/-- Gate marker: inverse-metric raising is exact at every smooth nonzero
variation in the admissible chart. -/
theorem regular_general_metric_c2_smooth_actual_metric_inverse_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    ∀ row column : Fin 4,
      (∑ middle : Fin 4,
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            row middle point *
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor middle column point) =
        if row = column then 1 else 0 := by
  exact regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
    period hPeriod metric tensor hVariation point

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D
end JanusFormal
