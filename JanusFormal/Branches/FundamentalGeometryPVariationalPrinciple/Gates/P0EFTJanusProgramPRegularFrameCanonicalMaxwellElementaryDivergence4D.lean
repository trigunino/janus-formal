import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D

/-! # Elementary divergence split for the global Maxwell current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellBoundaryCurrentDecomposition4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Algebraic Euler part of the divergence of the Maxwell current. -/
def regularFrameCanonicalMaxwellFluxEulerPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ first : Fin 4, ∑ component : Fin 2, ∑ second : Fin 4,
    regularFrameGaugeVariationCoefficient period hPeriod metric variation
        component second point *
      canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellFluxVector period hPeriod metric potential
          component first second) point

/-- Part of the current divergence containing derivatives of the arbitrary
gauge variation. -/
def regularFrameCanonicalMaxwellVariationDerivativePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ first : Fin 4, ∑ component : Fin 2, ∑ second : Fin 4,
    mvfderiv coverModelWithCorners
      (regularFrameGaugeVariationCoefficient period hPeriod metric variation
        component second).toFun point
      (regularFrameCanonicalMaxwellFluxVector period hPeriod metric potential
        component first second point)

/-- Full pointwise elementary expansion of the actual global current
divergence. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_divergence_eq_elementary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
          potential variation) point =
      ∑ first : Fin 4, ∑ component : Fin 2, ∑ second : Fin 4,
        (regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component second point *
            canonicalTenFlowDivergence period hPeriod metric
              (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
                potential component first second) point +
          mvfderiv coverModelWithCorners
            (regularFrameGaugeVariationCoefficient period hPeriod metric
              variation component second).toFun point
            (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
              potential component first second point)) := by
  rw [regularFrameCanonicalMaxwellBoundaryCurrent_eq_sum]
  rw [canonicalTenFlowDivergence_finset_sum period hPeriod metric Finset.univ]
  change (∑ first : Fin 4,
    canonicalTenFlowDivergence period hPeriod metric
      (regularFrameCanonicalMaxwellBoundarySummand period hPeriod metric
        potential variation first) point) = _
  apply Finset.sum_congr rfl
  intro first _
  exact regularFrameCanonicalMaxwellBoundarySummand_divergence_apply period
    hPeriod metric potential variation first point

/-- Canonical product rule for the complete global Maxwell current. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_divergence_split
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
          potential variation) point =
      regularFrameCanonicalMaxwellFluxEulerPairing period hPeriod metric
          potential variation point +
        regularFrameCanonicalMaxwellVariationDerivativePairing period hPeriod
          metric potential variation point := by
  rw [regularFrameCanonicalMaxwellBoundaryCurrent_divergence_eq_elementary]
  unfold regularFrameCanonicalMaxwellFluxEulerPairing
    regularFrameCanonicalMaxwellVariationDerivativePairing
  simp only [Finset.sum_add_distrib]

/-- Gate marker: the boundary divergence is separated into its Euler and
variation-derivative parts without an abstract Stokes contract. -/
theorem regular_frame_canonical_maxwell_elementary_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
          potential variation) point =
      regularFrameCanonicalMaxwellFluxEulerPairing period hPeriod metric
          potential variation point +
        regularFrameCanonicalMaxwellVariationDerivativePairing period hPeriod
          metric potential variation point :=
  regularFrameCanonicalMaxwellBoundaryCurrent_divergence_split period hPeriod
    metric potential variation point

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D
end JanusFormal
