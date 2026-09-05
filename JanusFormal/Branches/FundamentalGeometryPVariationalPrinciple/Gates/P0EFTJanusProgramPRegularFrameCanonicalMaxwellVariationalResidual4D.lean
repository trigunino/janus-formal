import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

/-! # Smooth coefficient residual selected by the Maxwell variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellCartanVariation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Every intrinsic gauge variation evaluates the frame bracket through its
smooth structure coefficients. -/
theorem regularFrameBracketPotentialCoefficient_eq_structure_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameBracketPotentialCoefficient period hPeriod metric variation
        component first second =
      ∑ upper : Fin 4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric first second
            upper)
          (regularFrameGaugeVariationCoefficient period hPeriod metric
            variation component upper) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hBracket := regularFrameStructureCoefficient_reconstructs period hPeriod
    metric first second point
  have hApplied := congrArg
    (fun vector => variation.toFun component point vector) hBracket
  change variation.toFun component point
      (regularFrameLieBracket period hPeriod metric first second point) =
    ∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
          upper point *
        variation.toFun component point (metric.frame upper point)
  simpa only [map_sum, map_smul, smul_eq_mul] using hApplied

@[simp]
theorem regularFrameBracketPotentialCoefficient_apply_eq_structure_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameBracketPotentialCoefficient period hPeriod metric variation
        component first second point =
      ∑ upper : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
            upper point *
          regularFrameGaugeVariationCoefficient period hPeriod metric variation
            component upper point := by
  have hBracket := regularFrameStructureCoefficient_reconstructs period hPeriod
    metric first second point
  have hApplied := congrArg
    (fun vector => variation.toFun component point vector) hBracket
  change variation.toFun component point
      (regularFrameLieBracket period hPeriod metric first second point) =
    ∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
          upper point *
        variation.toFun component point (metric.frame upper point)
  simpa only [map_sum, map_smul, smul_eq_mul] using hApplied

/-- Divergence part of one Euler coefficient. -/
def regularFrameCanonicalMaxwellVariationalFluxCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2) :
    SmoothScalarField period hPeriod :=
  ∑ first : Fin 4,
    canonicalTenFlowDivergence period hPeriod metric
      (regularFrameCanonicalMaxwellFluxVector period hPeriod metric potential
        component first upper)

@[simp]
theorem regularFrameCanonicalMaxwellVariationalFluxCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellVariationalFluxCoefficient period hPeriod metric
        potential upper component point =
      ∑ first : Fin 4,
        canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
            potential component first upper) point := by
  rfl

/-- Anholonomy part of one Euler coefficient. -/
def regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2) :
    SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    ∑ first : Fin 4, ∑ second : Fin 4,
      smoothScalarFieldMul period hPeriod
        (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
          potential component first second)
        (regularFrameStructureCoefficient period hPeriod metric first second
          upper)

@[simp]
theorem regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient period hPeriod
        metric potential upper component point =
      (1 / 2 : Real) *
        ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point *
            regularFrameStructureCoefficient period hPeriod metric first second
              upper point := by
  rfl

/-- Complete smooth coefficient selected by the authentic variation. -/
def regularFrameCanonicalMaxwellVariationalResidualCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2) :
    SmoothScalarField period hPeriod :=
  regularFrameCanonicalMaxwellVariationalFluxCoefficient period hPeriod metric
      potential upper component +
    regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient period hPeriod
      metric potential upper component

@[simp]
theorem regularFrameCanonicalMaxwellVariationalResidualCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (upper : Fin 4) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
        metric potential upper component point =
      (∑ first : Fin 4,
        canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
            potential component first upper) point) +
      (1 / 2 : Real) *
        ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second point *
            regularFrameStructureCoefficient period hPeriod metric first second
              upper point := by
  rfl

/-- The eight smooth Euler coefficients as one `GaugeFiber` field. -/
def regularFrameCanonicalMaxwellVariationalResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm (fun index =>
      regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
        metric potential index.1 index.2 point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact (regularFrameCanonicalMaxwellVariationalResidualCoefficient period
      hPeriod metric potential index.1 index.2).contMDiff_toFun

@[simp]
theorem regularFrameCanonicalMaxwellVariationalResidual_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (upper : Fin 4) (component : Fin 2) :
    regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
        potential point (upper, component) =
      regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
        metric potential upper component point :=
  rfl

private theorem fluxEulerPairing_eq_coefficient_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellFluxEulerPairing period hPeriod metric potential
        variation point =
      ∑ upper : Fin 4, ∑ component : Fin 2,
        regularFrameCanonicalMaxwellVariationalFluxCoefficient period hPeriod
              metric potential upper component point *
          regularFrameGaugeVariationCoefficient period hPeriod metric variation
            component upper point := by
  unfold regularFrameCanonicalMaxwellFluxEulerPairing
  calc
    _ = ∑ component : Fin 2, ∑ first : Fin 4, ∑ upper : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component upper point *
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
              potential component first upper) point := by
      rw [Finset.sum_comm]
    _ = ∑ component : Fin 2, ∑ upper : Fin 4, ∑ first : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component upper point *
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
              potential component first upper) point := by
      apply Finset.sum_congr rfl
      intro component _
      rw [Finset.sum_comm]
    _ = ∑ upper : Fin 4, ∑ component : Fin 2, ∑ first : Fin 4,
        regularFrameGaugeVariationCoefficient period hPeriod metric variation
              component upper point *
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellFluxVector period hPeriod metric
              potential component first upper) point := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro component _
      rw [regularFrameCanonicalMaxwellVariationalFluxCoefficient_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      ring

private theorem anholonomyPairing_eq_coefficient_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellAnholonomyPairing period hPeriod metric
        potential variation point =
      ∑ upper : Fin 4, ∑ component : Fin 2,
        regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient period
              hPeriod metric potential upper component point *
          regularFrameGaugeVariationCoefficient period hPeriod metric variation
            component upper point := by
  unfold regularFrameCanonicalMaxwellAnholonomyPairing
  simp_rw [regularFrameBracketPotentialCoefficient_apply_eq_structure_sum
    period hPeriod metric variation]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ component : Fin 2, ∑ first : Fin 4, ∑ upper : Fin 4,
        ∑ second : Fin 4,
          (1 / 2 : Real) *
              (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod
                    metric potential component first second point *
                regularFrameStructureCoefficient period hPeriod metric first
                  second upper point) *
            regularFrameGaugeVariationCoefficient period hPeriod metric
              variation component upper point := by
      apply Finset.sum_congr rfl
      intro component _
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ = ∑ component : Fin 2, ∑ upper : Fin 4, ∑ first : Fin 4,
        ∑ second : Fin 4,
          (1 / 2 : Real) *
              (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod
                    metric potential component first second point *
                regularFrameStructureCoefficient period hPeriod metric first
                  second upper point) *
            regularFrameGaugeVariationCoefficient period hPeriod metric
              variation component upper point := by
      apply Finset.sum_congr rfl
      intro component _
      rw [Finset.sum_comm]
    _ = ∑ upper : Fin 4, ∑ component : Fin 2, ∑ first : Fin 4,
        ∑ second : Fin 4,
          (1 / 2 : Real) *
              (regularFrameCanonicalMaxwellFluxCoefficient period hPeriod
                    metric potential component first second point *
                regularFrameStructureCoefficient period hPeriod metric first
                  second upper point) *
            regularFrameGaugeVariationCoefficient period hPeriod metric
              variation component upper point := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro component _
      rw [regularFrameCanonicalMaxwellVariationalAnholonomyCoefficient_apply]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Pointwise Euler pairing represented by the smooth eight-component
variational residual. -/
theorem regularFrameCanonicalMaxwellVariationalEulerPairing_eq_residual_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
        potential variation point =
      ∑ upper : Fin 4, ∑ component : Fin 2,
        regularFrameCanonicalMaxwellVariationalResidualCoefficient period
              hPeriod metric potential upper component point *
          regularFrameGaugeVariationCoefficient period hPeriod metric variation
            component upper point := by
  unfold regularFrameCanonicalMaxwellVariationalEulerPairing
    regularFrameCanonicalMaxwellVariationalResidualCoefficient
  rw [fluxEulerPairing_eq_coefficient_sum,
    anholonomyPairing_eq_coefficient_sum]
  simp only [smoothScalarFieldAdd_apply, add_mul, Finset.sum_add_distrib]

/-- The Euclidean coefficient pairing is exactly the authentic Maxwell Euler
density. -/
theorem inner_variationalMaxwellResidual_frameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    inner Real
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
          potential point)
        (gaugePotentialFrameCoefficients period hPeriod metric variation point) =
      regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
        potential variation point := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  rw [regularFrameCanonicalMaxwellVariationalEulerPairing_eq_residual_sum]
  apply Finset.sum_congr rfl
  intro upper _
  apply Finset.sum_congr rfl
  intro component _
  rw [Real.inner_apply,
    regularFrameCanonicalMaxwellVariationalResidual_apply,
    gaugePotentialFrameCoefficients_apply]
  rfl

/-- Gate marker: the Euler density extracted in Gate534 is now represented by
a concrete smooth residual separated by genuine intrinsic gauge tests. -/
theorem regular_frame_canonical_maxwell_variational_residual_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    inner Real
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
          potential point)
        (gaugePotentialFrameCoefficients period hPeriod metric variation point) =
      regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
        potential variation point :=
  inner_variationalMaxwellResidual_frameCoefficients period hPeriod metric
    potential variation point

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
end JanusFormal
