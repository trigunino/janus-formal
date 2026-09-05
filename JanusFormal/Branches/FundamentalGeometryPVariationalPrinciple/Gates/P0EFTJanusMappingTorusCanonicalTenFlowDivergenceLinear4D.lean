import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

/-! # Additivity of the canonical ten-flow divergence -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem canonicalTenFlowDualCoefficient_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 10) :
    canonicalTenFlowDualCoefficient period hPeriod metric
        (0 : SmoothTangentField period hPeriod) index = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (canonicalTenFlowFrame period hPeriod) metric.metric point index 0 = 0
  simp

theorem canonicalTenFlowDualCoefficient_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) (index : Fin 10) :
    canonicalTenFlowDualCoefficient period hPeriod metric (first + second)
        index =
      canonicalTenFlowDualCoefficient period hPeriod metric first index +
        canonicalTenFlowDualCoefficient period hPeriod metric second index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (canonicalTenFlowFrame period hPeriod) metric.metric point index
        (first point + second point) = _
  rw [map_add]
  rfl

@[simp]
theorem canonicalTenFlowDivergence_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (0 : SmoothTangentField period hPeriod) = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change canonicalTenFlowDivergence period hPeriod metric
      (0 : SmoothTangentField period hPeriod) point = 0
  rw [canonicalTenFlowDivergence_apply]
  simp_rw [canonicalTenFlowDualCoefficient_zero period hPeriod metric]
  apply Finset.sum_eq_zero
  intro index _
  rw [frameDerivative_eq_mfderiv]
  change mvfderiv coverModelWithCorners (fun _ => (0 : Real)) point
      ((canonicalTenFlowFrame period hPeriod).vectorAt point index) = 0
  rw [mvfderiv_const]
  simp

theorem canonicalTenFlowDivergence_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric (first + second) =
      canonicalTenFlowDivergence period hPeriod metric first +
        canonicalTenFlowDivergence period hPeriod metric second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change canonicalTenFlowDivergence period hPeriod metric (first + second)
      point =
    canonicalTenFlowDivergence period hPeriod metric first point +
      canonicalTenFlowDivergence period hPeriod metric second point
  rw [canonicalTenFlowDivergence_apply, canonicalTenFlowDivergence_apply,
    canonicalTenFlowDivergence_apply]
  simp_rw [canonicalTenFlowDualCoefficient_add period hPeriod metric first
    second]
  simp_rw [congrFun (congrFun
    (frameDerivative_add period hPeriod Real
      (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric first _)
        (canonicalTenFlowDualCoefficient period hPeriod metric second _)) point)
      _]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]

/-- The canonical divergence as an additive operator on smooth currents. -/
def canonicalTenFlowDivergenceAddMonoidHom
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →+
      SmoothQuotientField period hPeriod Real where
  toFun := canonicalTenFlowDivergence period hPeriod metric
  map_zero' := canonicalTenFlowDivergence_zero period hPeriod metric
  map_add' := canonicalTenFlowDivergence_add period hPeriod metric

theorem canonicalTenFlowDivergence_finset_sum
    {Index : Type*} (metric : RegularGeneralLorentzMetric period hPeriod)
    (indices : Finset Index)
    (vectors : Index → SmoothTangentField period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices,
        canonicalTenFlowDivergence period hPeriod metric (vectors index) := by
  exact map_sum (canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric)
    vectors indices

/-- Gate marker: divergence commutes with all finite current sums. -/
theorem canonical_ten_flow_divergence_linear_gate
    {Index : Type*} (metric : RegularGeneralLorentzMetric period hPeriod)
    (indices : Finset Index)
    (vectors : Index → SmoothTangentField period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices,
        canonicalTenFlowDivergence period hPeriod metric (vectors index) :=
  canonicalTenFlowDivergence_finset_sum period hPeriod metric indices vectors

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
end JanusFormal
