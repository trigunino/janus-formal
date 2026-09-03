import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D

/-!
# Exact Gram transport for the completed Lorentz chart

The inverse-root frame transport preserves the stored Gram matrix.  Hence its
smooth inverse, completed `C²` lifts, metric adjoint, and self-adjoint root
domain are unchanged by passage to the varied regular metric.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGramTransport4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2AdjointAlgebra4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The transported regular frame reads the varied metric with exactly the
same smooth Gram matrix as the base frame reads the base metric. -/
theorem regularGeneralMetricC2LorentzChart_frameMetricMatrix_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricMatrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularFrameMetricMatrix period hPeriod metric := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameMetricMatrix_apply, regularFrameMetricMatrix_apply,
    regularGeneralMetricC2LorentzChartRegularMetric_frame_apply,
    regularGeneralMetricC2LorentzChartRegularMetric_frame_apply,
    regularGeneralMetricC2LorentzChartRegularMetric_metric,
    regularGeneralMetricC2LorentzChartMetric_congruence]
  have hRoot (index : Fin 4) :
      regularGeneralMetricC2IdentityRootAt period hPeriod metric tensor point
          (regularGeneralMetricC2IdentityRootInverseAt period hPeriod metric
            tensor point (metric.frame index point)) =
        metric.frame index point := by
    have hApply := DFunLike.congr_fun
      (regularGeneralMetricC2IdentityRootAt_comp_inverse
        period hPeriod metric tensor hVariation point)
      (metric.frame index point)
    simpa [ContinuousLinearMap.comp_apply] using hApply
  rw [hRoot row, hRoot column]

/-- Exact equality of the completed `C²` Gram matrices. -/
theorem regularGeneralMetricC2LorentzChart_frameMetricC2Matrix_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricC2Matrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularFrameMetricC2Matrix period hPeriod metric := by
  unfold regularFrameMetricC2Matrix
  rw [regularGeneralMetricC2LorentzChart_frameMetricMatrix_eq
    period hPeriod metric tensor hVariation]

/-- The pointwise smooth inverse Gram matrix is transported exactly. -/
theorem regularGeneralMetricC2LorentzChart_frameMetricInverseMatrix_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricInverseMatrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularFrameMetricInverseMatrix period hPeriod metric := by
  have hMatrix := regularGeneralMetricC2LorentzChart_frameMetricMatrix_eq
    period hPeriod metric tensor hVariation
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    (regularFrameMetricMatrixMap period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) point)⁻¹ row column =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ row column
  have hMap :
      regularFrameMetricMatrixMap period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            metric tensor hVariation) point =
        regularFrameMetricMatrixMap period hPeriod metric point := by
    funext currentRow currentColumn
    exact congrArg (fun field => field point)
      (congrFun (congrFun hMatrix currentRow) currentColumn)
  rw [hMap]

/-- Exact equality of the completed `C²` inverse Gram matrices. -/
theorem regularGeneralMetricC2LorentzChart_frameMetricInverseC2Matrix_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricInverseC2Matrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularFrameMetricInverseC2Matrix period hPeriod metric := by
  unfold regularFrameMetricInverseC2Matrix
  rw [regularGeneralMetricC2LorentzChart_frameMetricInverseMatrix_eq
    period hPeriod metric tensor hVariation]

/-- The completed metric adjoint is unchanged by the chart transport. -/
theorem regularGeneralMetricC2LorentzChart_frameMetricC2Adjoint_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricC2Adjoint period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularFrameMetricC2Adjoint period hPeriod metric := by
  apply ContinuousLinearMap.ext
  intro matrix
  rw [regularFrameMetricC2Adjoint_apply,
    regularFrameMetricC2Adjoint_apply,
    regularGeneralMetricC2LorentzChart_frameMetricC2Matrix_eq
      period hPeriod metric tensor hVariation,
    regularGeneralMetricC2LorentzChart_frameMetricInverseC2Matrix_eq
      period hPeriod metric tensor hVariation]

/-- Therefore the admissible self-adjoint root domain can be read in the fixed
base Gram matrix. -/
theorem regularGeneralMetricC2LorentzChart_selfAdjointRootDomain_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularGeneralMetricC2SelfAdjointRootDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric := by
  unfold regularGeneralMetricC2SelfAdjointRootDomain
  rw [regularGeneralMetricC2LorentzChart_frameMetricC2Adjoint_eq
    period hPeriod metric tensor hVariation]

/-- Gate marker for exact Gram, adjoint, and root-domain transport. -/
theorem regular_general_metric_c2_lorentz_chart_gram_transport_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularFrameMetricC2Matrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            metric tensor hVariation) =
        regularFrameMetricC2Matrix period hPeriod metric ∧
      regularFrameMetricC2Adjoint period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            metric tensor hVariation) =
        regularFrameMetricC2Adjoint period hPeriod metric ∧
      regularGeneralMetricC2SelfAdjointRootDomain period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            metric tensor hVariation) =
        regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric := by
  exact ⟨regularGeneralMetricC2LorentzChart_frameMetricC2Matrix_eq
      period hPeriod metric tensor hVariation,
    regularGeneralMetricC2LorentzChart_frameMetricC2Adjoint_eq
      period hPeriod metric tensor hVariation,
    regularGeneralMetricC2LorentzChart_selfAdjointRootDomain_eq
      period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGramTransport4D
end JanusFormal
