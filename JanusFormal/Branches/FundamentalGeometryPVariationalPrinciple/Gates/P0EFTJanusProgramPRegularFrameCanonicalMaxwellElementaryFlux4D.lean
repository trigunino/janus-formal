import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellBoundaryCurrentDecomposition4D

/-! # Elementary regular-frame Maxwell fluxes -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellBoundaryCurrentDecomposition4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One densitized raised-curvature coefficient, before multiplication by the
gauge variation. -/
def regularFrameCanonicalMaxwellFluxCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothQuotientField period hPeriod Real :=
  smoothScalarFieldMul period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient period hPeriod
      metric potential component first second)

@[simp]
theorem regularFrameCanonicalMaxwellFluxCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component first second point =
      globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient period
          hPeriod metric potential component first second point :=
  rfl

/-- The elementary tangent flux in one gauge and two frame indices. -/
def regularFrameCanonicalMaxwellFluxVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothTangentField period hPeriod :=
  smoothScalarSMulTangentField period hPeriod
    (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
      potential component first second)
    (metric.frame first)

/-- Elementary boundary current obtained by multiplying a flux by one gauge
variation coefficient. -/
def regularFrameCanonicalMaxwellElementaryCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothTangentField period hPeriod :=
  smoothScalarSMulTangentField period hPeriod
    (regularFrameGaugeVariationCoefficient period hPeriod metric variation
      component second)
    (regularFrameCanonicalMaxwellFluxVector period hPeriod metric potential
      component first second)

/-- Each frame coefficient of the Maxwell current splits into its eight
gauge-component/frame-component products. -/
theorem regularFrameCanonicalMaxwellBoundaryCoefficient_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) :
    regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
        potential variation first =
      ∑ component : Fin 2, ∑ second : Fin 4,
        smoothScalarFieldMul period hPeriod
          (regularFrameGaugeVariationCoefficient period hPeriod metric
            variation component second)
          (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameCanonicalMaxwellBoundaryCoefficient_apply]
  change
    globalMetricVolumeRatio period hPeriod metric.metric point *
        (∑ component : Fin 2, ∑ second : Fin 4,
          regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient period
                hPeriod metric potential component first second point *
            regularFrameGaugeVariationCoefficient period hPeriod metric
              variation component second point) =
      ∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component second point *
          (globalMetricVolumeRatio period hPeriod metric.metric point *
            regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient period
              hPeriod metric potential component first second point)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- One regular-frame summand is exactly the sum of its elementary variation
currents. -/
theorem regularFrameCanonicalMaxwellBoundarySummand_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) :
    regularFrameCanonicalMaxwellBoundarySummand period hPeriod metric potential
        variation first =
      ∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellElementaryCurrent period hPeriod metric
          potential variation component first second := by
  apply ContMDiffSection.ext
  intro point
  rw [regularFrameCanonicalMaxwellBoundarySummand_apply,
    regularFrameCanonicalMaxwellBoundaryCoefficient_eq_sum]
  change
    ((∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component second point *
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point) • metric.frame first point) =
      ∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component second point •
          (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point •
            metric.frame first point)
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro component _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro second _
  rw [smul_smul]

/-- The complete boundary current is a finite sum of elementary Maxwell
variation fluxes. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_eq_elementary_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric potential
        variation =
      ∑ first : Fin 4, ∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellElementaryCurrent period hPeriod metric
          potential variation component first second := by
  rw [regularFrameCanonicalMaxwellBoundaryCurrent_eq_sum]
  apply Finset.sum_congr rfl
  intro first _
  exact regularFrameCanonicalMaxwellBoundarySummand_eq_sum period hPeriod
    metric potential variation first

/-- Divergence of one frame summand, with every variation derivative exposed
by the canonical Leibniz rule. -/
theorem regularFrameCanonicalMaxwellBoundarySummand_divergence_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric
        (regularFrameCanonicalMaxwellBoundarySummand period hPeriod metric
          potential variation first) point =
      ∑ component : Fin 2, ∑ second : Fin 4,
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
  rw [regularFrameCanonicalMaxwellBoundarySummand_eq_sum]
  rw [canonicalTenFlowDivergence_finset_sum period hPeriod metric Finset.univ]
  change (∑ component : Fin 2,
    canonicalTenFlowDivergence period hPeriod metric
      (∑ second : Fin 4,
        regularFrameCanonicalMaxwellElementaryCurrent period hPeriod metric
          potential variation component first second) point) = _
  apply Finset.sum_congr rfl
  intro component _
  rw [canonicalTenFlowDivergence_finset_sum period hPeriod metric Finset.univ]
  change (∑ second : Fin 4,
    canonicalTenFlowDivergence period hPeriod metric
      (regularFrameCanonicalMaxwellElementaryCurrent period hPeriod metric
        potential variation component first second) point) = _
  apply Finset.sum_congr rfl
  intro second _
  exact canonicalTenFlowDivergence_smul_apply period hPeriod metric
    (regularFrameGaugeVariationCoefficient period hPeriod metric variation
      component second)
    (regularFrameCanonicalMaxwellFluxVector period hPeriod metric potential
      component first second) point

/-- Gate marker: the actual Maxwell current has been split into elementary
fluxes and all derivatives of the arbitrary gauge variation are explicit. -/
theorem regular_frame_canonical_maxwell_elementary_flux_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric potential
        variation =
      ∑ first : Fin 4, ∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellElementaryCurrent period hPeriod metric
          potential variation component first second :=
  regularFrameCanonicalMaxwellBoundaryCurrent_eq_elementary_sum period hPeriod
    metric potential variation

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D
end JanusFormal
