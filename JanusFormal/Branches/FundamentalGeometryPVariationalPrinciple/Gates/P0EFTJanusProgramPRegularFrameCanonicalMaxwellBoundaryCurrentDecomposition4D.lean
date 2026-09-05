import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D

/-! # Canonical decomposition of the global Maxwell boundary current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellBoundaryCurrentDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One regular-frame summand of the densitized Maxwell boundary current. -/
def regularFrameCanonicalMaxwellBoundarySummand
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) : SmoothTangentField period hPeriod :=
  smoothScalarSMulTangentField period hPeriod
    (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
      potential variation first)
    (metric.frame first)

@[simp]
theorem regularFrameCanonicalMaxwellBoundarySummand_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellBoundarySummand period hPeriod metric potential
        variation first point =
      regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
          potential variation first point • metric.frame first point :=
  rfl

/-- The concrete Maxwell current is the sum of its four regular-frame
summands. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric potential
        variation =
      ∑ first : Fin 4,
        regularFrameCanonicalMaxwellBoundarySummand period hPeriod metric
          potential variation first := by
  apply ContMDiffSection.ext
  intro point
  rw [regularFrameCanonicalMaxwellBoundaryCurrent_apply]
  rfl

/-- Exact divergence expansion of the actual Maxwell current. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_divergence_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
          potential variation) point =
      ∑ first : Fin 4,
        (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
              potential variation first point *
            canonicalTenFlowDivergence period hPeriod metric
              (metric.frame first) point +
          mvfderiv coverModelWithCorners
            (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod
              metric potential variation first).toFun point
            (metric.frame first point)) := by
  rw [regularFrameCanonicalMaxwellBoundaryCurrent_eq_sum]
  rw [canonicalTenFlowDivergence_finset_sum period hPeriod metric Finset.univ]
  change
    (∑ first : Fin 4,
      canonicalTenFlowDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod
          (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod
            metric potential variation first)
          (metric.frame first)) point) = _
  apply Finset.sum_congr rfl
  intro first _
  exact canonicalTenFlowDivergence_smul_apply period hPeriod metric
    (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
      potential variation first) (metric.frame first) point

/-- Gate marker: the global Maxwell boundary divergence is now reduced to
four explicit scalar-vector Leibniz terms. -/
theorem regular_frame_canonical_maxwell_boundary_current_decomposition_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
          potential variation) point =
      ∑ first : Fin 4,
        (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
              potential variation first point *
            canonicalTenFlowDivergence period hPeriod metric
              (metric.frame first) point +
          mvfderiv coverModelWithCorners
            (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod
              metric potential variation first).toFun point
            (metric.frame first point)) :=
  regularFrameCanonicalMaxwellBoundaryCurrent_divergence_apply period hPeriod
    metric potential variation point

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellBoundaryCurrentDecomposition4D
end JanusFormal
