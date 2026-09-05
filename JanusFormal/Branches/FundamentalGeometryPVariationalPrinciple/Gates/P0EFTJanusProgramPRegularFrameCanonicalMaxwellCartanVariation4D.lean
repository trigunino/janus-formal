import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellFirstVariationCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

/-! # Cartan split of the canonical Maxwell first variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellCartanVariation4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellFirstVariationCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Chart-free version of the authentic curvature-contraction formula. -/
theorem regularMaxwellFirstVariationField_eq_flux_curvature_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point =
      -(1 / 2 : Real) *
        ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point *
            regularFrameGaugeCurvatureCoefficient period hPeriod metric
              variation component first second point := by
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  have hVariation := regularMaxwellFirstVariationField_eq_flux_curvature period
    hPeriod metric potential variation witness.patch witness.coordinate
  rw [witness.coordinate_eq] at hVariation
  exact hVariation

@[simp]
theorem regularFrameGaugeCurvatureCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameGaugeCurvatureCoefficient period hPeriod metric variation
        component first second point =
      regularFramePotentialDerivative period hPeriod metric variation component
          first second point -
        regularFramePotentialDerivative period hPeriod metric variation
          component second first point -
        regularFrameBracketPotentialCoefficient period hPeriod metric variation
          component first second point :=
  rfl

theorem regularFramePotentialDerivative_apply_eq_mvfderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (direction index : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFramePotentialDerivative period hPeriod metric variation component
        direction index point =
      mvfderiv coverModelWithCorners
        (regularFrameGaugeVariationCoefficient period hPeriod metric variation
          component index).toFun point (metric.frame direction point) := by
  change frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFramePotentialCoefficient period hPeriod metric variation
        component index) point direction = _
  rw [frameDerivative_eq_mfderiv]
  rfl

/-- Frame form of the derivative part exposed by the current Leibniz rule. -/
def regularFrameCanonicalMaxwellFrameDerivativePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
          component first second point *
      regularFramePotentialDerivative period hPeriod metric variation component
        first second point

/-- Exact anholonomy correction from Cartan's bracket term. -/
def regularFrameCanonicalMaxwellAnholonomyPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) *
    ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
      regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point *
        regularFrameBracketPotentialCoefficient period hPeriod metric variation
          component first second point

theorem regularFrameCanonicalMaxwellVariationDerivativePairing_eq_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellVariationDerivativePairing period hPeriod metric
        potential variation point =
      regularFrameCanonicalMaxwellFrameDerivativePairing period hPeriod metric
        potential variation point := by
  unfold regularFrameCanonicalMaxwellVariationDerivativePairing
    regularFrameCanonicalMaxwellFrameDerivativePairing
  have hTerm (first : Fin 4) (component : Fin 2) (second : Fin 4) :
      mvfderiv coverModelWithCorners
          (regularFrameGaugeVariationCoefficient period hPeriod metric variation
            component second).toFun point
          (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
            potential component first second point) =
        regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
              potential component first second point *
          regularFramePotentialDerivative period hPeriod metric variation
            component first second point := by
    change mvfderiv coverModelWithCorners
        (regularFrameGaugeVariationCoefficient period hPeriod metric variation
          component second).toFun point
        (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point • metric.frame first point) = _
    rw [map_smul]
    rw [regularFramePotentialDerivative_apply_eq_mvfderiv]
    rfl
  simp_rw [hTerm]
  exact Finset.sum_comm

theorem regularFrameCanonicalMaxwellFlux_swappedDerivative_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point *
        regularFramePotentialDerivative period hPeriod metric variation
          component second first point) =
      -∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
              potential component first second point *
          regularFramePotentialDerivative period hPeriod metric variation
            component first second point := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro second _
  have hSwap := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    (regularFrameCanonicalMaxwellFluxCoefficient_swap period hPeriod metric
      potential component first second)
  change
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component second first point =
      -regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
        potential component first second point at hSwap
  rw [hSwap]
  ring

/-- Antisymmetry reduces the Cartan curvature contraction to twice the frame
derivative minus the bracket correction. -/
theorem regularFrameCanonicalMaxwellFluxCurvature_contraction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
      regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point *
        regularFrameGaugeCurvatureCoefficient period hPeriod metric variation
          component first second point) =
      2 * regularFrameCanonicalMaxwellFrameDerivativePairing period hPeriod
          metric potential variation point -
        ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point *
            regularFrameBracketPotentialCoefficient period hPeriod metric
              variation component first second point := by
  simp_rw [regularFrameGaugeCurvatureCoefficient_apply, mul_sub]
  simp only [Finset.sum_sub_distrib]
  have hSwap :
      (∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
              potential component first second point *
          regularFramePotentialDerivative period hPeriod metric variation
            component second first point) =
        -∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point *
            regularFramePotentialDerivative period hPeriod metric variation
              component first second point := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro component _
    exact regularFrameCanonicalMaxwellFlux_swappedDerivative_sum period hPeriod
      metric potential variation component point
  rw [hSwap]
  unfold regularFrameCanonicalMaxwellFrameDerivativePairing
  ring

/-- Authentic pointwise Maxwell variation: derivative part plus the exact
anholonomy correction. -/
theorem regularMaxwellFirstVariationField_eq_neg_derivative_add_anholonomy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point =
      -regularFrameCanonicalMaxwellVariationDerivativePairing period hPeriod
          metric potential variation point +
        regularFrameCanonicalMaxwellAnholonomyPairing period hPeriod metric
          potential variation point := by
  rw [regularMaxwellFirstVariationField_eq_flux_curvature_global]
  rw [regularFrameCanonicalMaxwellFluxCurvature_contraction]
  rw [regularFrameCanonicalMaxwellVariationDerivativePairing_eq_frame]
  unfold regularFrameCanonicalMaxwellAnholonomyPairing
  ring

/-- Gate marker: Cartan anholonomy is explicit in the authentic Maxwell
variation and no boundary hypothesis is hidden. -/
theorem regular_frame_canonical_maxwell_cartan_variation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point =
      -regularFrameCanonicalMaxwellVariationDerivativePairing period hPeriod
          metric potential variation point +
        regularFrameCanonicalMaxwellAnholonomyPairing period hPeriod metric
          potential variation point :=
  regularMaxwellFirstVariationField_eq_neg_derivative_add_anholonomy period
    hPeriod metric potential variation point

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellCartanVariation4D
end JanusFormal
