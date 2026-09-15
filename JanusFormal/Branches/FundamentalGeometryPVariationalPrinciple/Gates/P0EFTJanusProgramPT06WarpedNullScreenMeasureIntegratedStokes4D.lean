import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D

/-!
# Warped-null screen measure and integrated Stokes identity

This gate equips the explicit null source with its coordinate volume and with
the screen measure whose Radon--Nikodym density is `exp u`.  Bochner integration
against that measure is exactly coordinate integration weighted by the screen
area.  Under a named differentiability and integrability contract, Gate 1043's
fiber identity integrates over the full null source and both sides are genuine
integrable functions.

No compactly supported density is constructed here.  The result still belongs
to the explicit chart and does not identify its measure with a mapping-torus
hypersurface measure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped ENNReal
open MeasureTheory
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D

/-- Lebesgue/Haar coordinate measure on `(u,x,y)`. -/
def programPT06WarpedNullCoordinateSourceMeasure :
    Measure ProgramPT06NullFaceSource3 :=
  volume

/-- The positive screen-area density as an extended nonnegative real. -/
def programPT06WarpedNullScreenMeasureWeight
    (source : ProgramPT06NullFaceSource3) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp source.1)

theorem programPT06WarpedNullScreenMeasureWeight_measurable :
    Measurable programPT06WarpedNullScreenMeasureWeight := by
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp measurable_fst)

@[simp] theorem programPT06WarpedNullScreenMeasureWeight_toReal
    (source : ProgramPT06NullFaceSource3) :
    (programPT06WarpedNullScreenMeasureWeight source).toReal =
      Real.exp source.1 := by
  simp [programPT06WarpedNullScreenMeasureWeight, Real.exp_nonneg]

theorem programPT06WarpedNullScreenMeasureWeight_lt_top
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullScreenMeasureWeight source < ∞ := by
  simp [programPT06WarpedNullScreenMeasureWeight]

/-- Screen measure `exp(u) du dx dy` on the explicit null-source chart. -/
def programPT06WarpedNullScreenMeasure :
    Measure ProgramPT06NullFaceSource3 :=
  programPT06WarpedNullCoordinateSourceMeasure.withDensity
    programPT06WarpedNullScreenMeasureWeight

/-- Integration against the screen measure is weighted coordinate
integration. -/
theorem programPT06WarpedNullScreenMeasure_integral_eq
    (function : ProgramPT06NullFaceSource3 → Real) :
    ∫ source, function source ∂programPT06WarpedNullScreenMeasure =
      ∫ source, Real.exp source.1 * function source
        ∂programPT06WarpedNullCoordinateSourceMeasure := by
  unfold programPT06WarpedNullScreenMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    programPT06WarpedNullScreenMeasureWeight_measurable
    (Filter.Eventually.of_forall
      programPT06WarpedNullScreenMeasureWeight_lt_top)]
  simp only [programPT06WarpedNullScreenMeasureWeight_toReal, smul_eq_mul]

/-- The corresponding exact integrability criterion. -/
theorem programPT06WarpedNullScreenMeasure_integrable_iff
    (function : ProgramPT06NullFaceSource3 → Real) :
    Integrable function programPT06WarpedNullScreenMeasure ↔
      Integrable (fun source => Real.exp source.1 * function source)
        programPT06WarpedNullCoordinateSourceMeasure := by
  unfold programPT06WarpedNullScreenMeasure
  simpa [mul_comm] using
    (integrable_withDensity_iff
      (μ := programPT06WarpedNullCoordinateSourceMeasure)
      programPT06WarpedNullScreenMeasureWeight_measurable
      (Filter.Eventually.of_forall
        programPT06WarpedNullScreenMeasureWeight_lt_top)
      (g := function))

/-- Analytic hypotheses needed to integrate the chart-level fiber identity over
the noncompact null source. -/
structure ProgramPT06WarpedNullIntegratedStokesContract
    (density : ProgramPT06WarpedNullHyperplaneDensity) : Prop where
  differentiable : ∀ source, DifferentiableAt Real density source
  screenWeighted_integrable :
    Integrable (programPT06WarpedNullScreenWeightedDensity density)
      programPT06WarpedNullCoordinateSourceMeasure

/-- Metric-volume divergence integrated along one collar fiber. -/
def programPT06WarpedNullMetricFiberBulkIntegral
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) : Real :=
  ∫ radius in (0 : Real)..1,
    programPT06WarpedNullAmbientMetricVolumeDensity
        (programPT06WarpedNullCollarEquiv (source, radius)) *
      programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarAffineFluxExtension density)
        (programPT06WarpedNullCollarEquiv (source, radius))

/-- Boundary flux of the same affine current. -/
def programPT06WarpedNullAffineBoundaryFlux
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06WarpedNullHyperplaneDensity :=
  programPT06WarpedNullHyperplaneFluxRestriction
    (programPT06WarpedNullCollarAffineFluxExtension density)

/-- Pointwise fiber integration produces the screen-weighted face density. -/
theorem programPT06WarpedNullMetricFiberBulkIntegral_eq_weightedDensity
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (source : ProgramPT06NullFaceSource3)
    (hDensity : DifferentiableAt Real density source) :
    programPT06WarpedNullMetricFiberBulkIntegral density source =
      programPT06WarpedNullScreenWeightedDensity density source := by
  unfold programPT06WarpedNullMetricFiberBulkIntegral
  rw [programPT06WarpedNullMetricVolume_fiberwise_stokes source hDensity,
    programPT06WarpedNullCollarAffineFluxExtension_rightInverse]
  simp [programPT06WarpedNullScreenWeightedDensity]

theorem ProgramPT06WarpedNullIntegratedStokesContract.bulk_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06WarpedNullIntegratedStokesContract density) :
    Integrable (programPT06WarpedNullMetricFiberBulkIntegral density)
      programPT06WarpedNullCoordinateSourceMeasure := by
  apply contract.screenWeighted_integrable.congr
  filter_upwards with source
  exact (programPT06WarpedNullMetricFiberBulkIntegral_eq_weightedDensity
    source (contract.differentiable source)).symm

theorem ProgramPT06WarpedNullIntegratedStokesContract.boundary_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06WarpedNullIntegratedStokesContract density) :
    Integrable (programPT06WarpedNullAffineBoundaryFlux density)
      programPT06WarpedNullScreenMeasure := by
  rw [programPT06WarpedNullScreenMeasure_integrable_iff]
  have hFlux : programPT06WarpedNullAffineBoundaryFlux density = density :=
    programPT06WarpedNullCollarAffineFluxExtension_rightInverse density
  rw [hFlux]
  exact contract.screenWeighted_integrable

/-- Source-integrated metric-volume Stokes law for the explicit collar. -/
theorem programPT06WarpedNullMetricVolume_integrated_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06WarpedNullIntegratedStokesContract density) :
    ∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
        ∂programPT06WarpedNullCoordinateSourceMeasure =
      ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
        ∂programPT06WarpedNullScreenMeasure := by
  rw [programPT06WarpedNullScreenMeasure_integral_eq]
  apply integral_congr_ae
  filter_upwards with source
  rw [programPT06WarpedNullMetricFiberBulkIntegral_eq_weightedDensity source
    (contract.differentiable source)]
  change Real.exp source.1 * density source =
    Real.exp source.1 * programPT06WarpedNullAffineBoundaryFlux density source
  rw [programPT06WarpedNullAffineBoundaryFlux,
    programPT06WarpedNullCollarAffineFluxExtension_rightInverse]

/-- Gate bundle: both source integrals exist and obey the integrated Stokes
identity. -/
theorem programPT06WarpedNullMetricVolume_integrable_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06WarpedNullIntegratedStokesContract density) :
    Integrable (programPT06WarpedNullMetricFiberBulkIntegral density)
        programPT06WarpedNullCoordinateSourceMeasure ∧
      Integrable (programPT06WarpedNullAffineBoundaryFlux density)
        programPT06WarpedNullScreenMeasure ∧
      (∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
          ∂programPT06WarpedNullCoordinateSourceMeasure) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
          ∂programPT06WarpedNullScreenMeasure :=
  ⟨contract.bulk_integrable, contract.boundary_integrable,
    programPT06WarpedNullMetricVolume_integrated_stokes contract⟩

end
end P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
end JanusFormal
