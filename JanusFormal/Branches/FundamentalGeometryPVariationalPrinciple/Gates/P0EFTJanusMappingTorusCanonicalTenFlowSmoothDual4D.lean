import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowEuclideanReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

/-! # Smooth global dual of the canonical ten-flow frame -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Smooth redundant-dual coefficient of a tangent current in one canonical
flow direction. -/
def canonicalTenFlowDualCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Fin 10) : SmoothQuotientField period hPeriod Real :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (canonicalTenFlowFrame period hPeriod) metric.metric vector index

@[simp]
theorem canonicalTenFlowDualCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Fin 10) (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDualCoefficient period hPeriod metric vector index point =
      generalMetricFiniteFrameCoefficientAt period hPeriod
        (canonicalTenFlowFrame period hPeriod) metric.metric point index
          (vector point) :=
  rfl

/-- The smooth dual coefficients reconstruct the current pointwise. -/
theorem canonicalTenFlowDual_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    vector point =
      ∑ index : Fin 10,
        canonicalTenFlowDualCoefficient period hPeriod metric vector index
            point •
          canonicalTenFlowGeneratorAt period hPeriod point
            ((canonicalFlowIndexEquivFinTen).symm index) := by
  exact generalMetricFiniteFrame_reconstructs period hPeriod
    (canonicalTenFlowFrame period hPeriod) metric.metric vector point

/-- Gate marker: every smooth tangent current has ten globally smooth
coefficients and is reconstructed exactly by the volume-preserving flows. -/
theorem canonical_ten_flow_smooth_dual_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    (∀ index : Fin 10,
      ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)) ∧
      ∀ point : EffectiveQuotient period hPeriod,
        vector point =
          ∑ index : Fin 10,
            canonicalTenFlowDualCoefficient period hPeriod metric vector index
                point •
              canonicalTenFlowGeneratorAt period hPeriod point
                ((canonicalFlowIndexEquivFinTen).symm index) := by
  exact ⟨fun index =>
      (canonicalTenFlowDualCoefficient period hPeriod metric vector index
        ).contMDiff_toFun,
    canonicalTenFlowDual_reconstructs period hPeriod metric vector⟩

end
end P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
end JanusFormal
