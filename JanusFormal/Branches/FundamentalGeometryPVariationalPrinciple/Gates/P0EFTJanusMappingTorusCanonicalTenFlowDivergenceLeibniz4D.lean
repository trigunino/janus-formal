import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

/-! # Leibniz rule for the canonical ten-flow divergence -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise multiplication of a smooth tangent field by a smooth scalar. -/
def smoothScalarSMulTangentField
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod) :
    SmoothTangentField period hPeriod where
  toFun := fun point => scalar point • vector point
  contMDiff_toFun := scalar.contMDiff_toFun.smul_section vector.contMDiff

@[simp]
theorem smoothScalarSMulTangentField_apply
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothScalarSMulTangentField period hPeriod scalar vector point =
      scalar point • vector point :=
  rfl

/-- The redundant smooth dual is pointwise linear in the tangent current. -/
theorem canonicalTenFlowDualCoefficient_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod) (index : Fin 10) :
    canonicalTenFlowDualCoefficient period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) index =
      smoothScalarFieldMul period hPeriod scalar
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    generalMetricFiniteFrameCoefficientAt period hPeriod
        (canonicalTenFlowFrame period hPeriod) metric.metric point index
          (scalar point • vector point) =
      scalar point *
        generalMetricFiniteFrameCoefficientAt period hPeriod
          (canonicalTenFlowFrame period hPeriod) metric.metric point index
            (vector point)
  rw [map_smul]
  rfl

/-- Exact pointwise Leibniz rule for the canonical-volume divergence. -/
theorem canonicalTenFlowDivergence_smul_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          canonicalTenFlowDivergence period hPeriod metric vector point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) := by
  rw [canonicalTenFlowDivergence_apply,
    canonicalTenFlowDivergence_apply,
    canonicalTenFlowDirectionalDerivative_reconstructs period hPeriod metric
      vector scalar point]
  simp_rw [canonicalTenFlowDualCoefficient_smul period hPeriod metric scalar
    vector]
  simp_rw [congrFun (congrFun
    (frameDerivative_mul period hPeriod
      (canonicalTenFlowFrame period hPeriod) scalar
        (canonicalTenFlowDualCoefficient period hPeriod metric vector _)) point) _]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Gate marker: canonical Stokes now comes with its pointwise product rule. -/
theorem canonical_ten_flow_divergence_leibniz_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          canonicalTenFlowDivergence period hPeriod metric vector point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) :=
  canonicalTenFlowDivergence_smul_apply period hPeriod metric scalar vector point

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
end JanusFormal
