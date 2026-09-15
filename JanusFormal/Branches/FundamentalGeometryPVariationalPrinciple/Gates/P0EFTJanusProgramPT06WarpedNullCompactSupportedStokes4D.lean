import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.CompactlySupported
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

/-!
# Compactly supported warped-null Stokes data

Compact support on the null source makes Gate 1044's weighted integrability
hypothesis automatic: multiplication by the smooth factor `exp u` preserves
compact support.  This gate also constructs a nonzero smooth bump density and
instantiates the integrated Stokes theorem for it.

The affine current restricted to Gate 1045's closed half-collar has compact
support whenever its source density does.  This remains an explicit chart
statement; no mapping-torus transport is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCompactSupportedStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open MeasureTheory
open scoped ContDiff
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

theorem programPT06WarpedNullScreenWeightedDensity_continuous
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hDensity : Continuous density) :
    Continuous (programPT06WarpedNullScreenWeightedDensity density) := by
  exact (Real.continuous_exp.comp continuous_fst).mul hDensity

theorem programPT06WarpedNullScreenWeightedDensity_hasCompactSupport
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hCompact : HasCompactSupport density) :
    HasCompactSupport
      (programPT06WarpedNullScreenWeightedDensity density) := by
  refine HasCompactSupport.intro' hCompact (isClosed_tsupport density) ?_
  intro source hSource
  simp [programPT06WarpedNullScreenWeightedDensity,
    image_eq_zero_of_notMem_tsupport hSource]

/-- A differentiable compactly supported density automatically satisfies the
analytic contract used by Gate 1044. -/
theorem programPT06WarpedNullIntegratedStokesContract_of_compactSupport
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hDensity : Differentiable Real density)
    (hCompact : HasCompactSupport density) :
    ProgramPT06WarpedNullIntegratedStokesContract density := by
  refine ⟨fun _ => hDensity.differentiableAt, ?_⟩
  unfold programPT06WarpedNullCoordinateSourceMeasure
  exact (programPT06WarpedNullScreenWeightedDensity_continuous
      hDensity.continuous).integrable_of_hasCompactSupport
    (programPT06WarpedNullScreenWeightedDensity_hasCompactSupport hCompact)

/-- Integrated metric-volume Stokes with compact support replacing Gate
1044's explicit integrability hypothesis. -/
theorem programPT06WarpedNullMetricVolume_integrable_stokes_of_compactSupport
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hDensity : Differentiable Real density)
    (hCompact : HasCompactSupport density) :
    Integrable (programPT06WarpedNullMetricFiberBulkIntegral density)
        programPT06WarpedNullCoordinateSourceMeasure ∧
      Integrable (programPT06WarpedNullAffineBoundaryFlux density)
        programPT06WarpedNullScreenMeasure ∧
      (∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
          ∂programPT06WarpedNullCoordinateSourceMeasure) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
          ∂programPT06WarpedNullScreenMeasure :=
  programPT06WarpedNullMetricVolume_integrable_stokes
    (programPT06WarpedNullIntegratedStokesContract_of_compactSupport
      hDensity hCompact)

/-- Compact source support remains compact after extending across the compact
normal interval. -/
theorem programPT06WarpedNullClosedHalfCollarAffineCurrent_hasCompactSupport
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hCompact : HasCompactSupport density) :
    HasCompactSupport
      (programPT06WarpedNullClosedHalfCollarAffineCurrent density) := by
  refine HasCompactSupport.intro'
    (hCompact.prod isCompact_univ)
    ((isClosed_tsupport density).prod isClosed_univ) ?_
  intro point hPoint
  have hSource : point.1 ∉ tsupport density := by
    intro hSource
    exact hPoint ⟨hSource, mem_univ point.2⟩
  have hDensityZero : density point.1 = 0 :=
    image_eq_zero_of_notMem_tsupport hSource
  rw [programPT06WarpedNullClosedHalfCollarAffineCurrent,
    programPT06WarpedNullClosedHalfCollarEmbedding,
    P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D.programPT06WarpedNullCollarAffineFluxExtension_on_collar]
  simp [programPT06WarpedNullClosedHalfCollarCoordinate, hDensityZero]

/-- Fixed nonzero bump centered at the origin, equal to one on the unit ball
and supported in the ball of radius two. -/
def programPT06WarpedNullCompactBump :
    ContDiffBump (0 : ProgramPT06NullFaceSource3) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def programPT06WarpedNullCompactDensity :
    ProgramPT06WarpedNullHyperplaneDensity :=
  programPT06WarpedNullCompactBump

theorem programPT06WarpedNullCompactDensity_contDiff :
    ContDiff Real ∞ programPT06WarpedNullCompactDensity := by
  exact ContDiffBump.contDiff programPT06WarpedNullCompactBump

theorem programPT06WarpedNullCompactDensity_hasCompactSupport :
    HasCompactSupport programPT06WarpedNullCompactDensity := by
  exact ContDiffBump.hasCompactSupport programPT06WarpedNullCompactBump

theorem programPT06WarpedNullCompactDensity_tsupport :
    tsupport programPT06WarpedNullCompactDensity =
      Metric.closedBall (0 : ProgramPT06NullFaceSource3) 2 := by
  exact ContDiffBump.tsupport_eq programPT06WarpedNullCompactBump

@[simp] theorem programPT06WarpedNullCompactDensity_zero :
    programPT06WarpedNullCompactDensity 0 = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp [programPT06WarpedNullCompactBump]

theorem programPT06WarpedNullCompactDensity_ne_zero :
    programPT06WarpedNullCompactDensity ≠ 0 := by
  intro hZero
  have hAtZero := congrFun hZero (0 : ProgramPT06NullFaceSource3)
  simp at hAtZero

theorem programPT06WarpedNullCompactDensity_integratedStokesContract :
    ProgramPT06WarpedNullIntegratedStokesContract
      programPT06WarpedNullCompactDensity :=
  programPT06WarpedNullIntegratedStokesContract_of_compactSupport
    (programPT06WarpedNullCompactDensity_contDiff.differentiable (by simp))
    programPT06WarpedNullCompactDensity_hasCompactSupport

theorem programPT06WarpedNullCompactDensity_halfCollarCurrent_hasCompactSupport :
    HasCompactSupport
      (programPT06WarpedNullClosedHalfCollarAffineCurrent
        programPT06WarpedNullCompactDensity) :=
  programPT06WarpedNullClosedHalfCollarAffineCurrent_hasCompactSupport
    programPT06WarpedNullCompactDensity_hasCompactSupport

/-- Concrete nonzero compactly supported instance of the source-integrated
metric-volume Stokes law. -/
theorem programPT06WarpedNullCompactDensity_integrable_stokes :
    Integrable
        (programPT06WarpedNullMetricFiberBulkIntegral
          programPT06WarpedNullCompactDensity)
        programPT06WarpedNullCoordinateSourceMeasure ∧
      Integrable
        (programPT06WarpedNullAffineBoundaryFlux
          programPT06WarpedNullCompactDensity)
        programPT06WarpedNullScreenMeasure ∧
      (∫ source, programPT06WarpedNullMetricFiberBulkIntegral
          programPT06WarpedNullCompactDensity source
          ∂programPT06WarpedNullCoordinateSourceMeasure) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux
          programPT06WarpedNullCompactDensity source
          ∂programPT06WarpedNullScreenMeasure :=
  programPT06WarpedNullMetricVolume_integrable_stokes_of_compactSupport
    (programPT06WarpedNullCompactDensity_contDiff.differentiable (by simp))
    programPT06WarpedNullCompactDensity_hasCompactSupport

/-- Gate bundle: the explicit density is smooth, nonzero and compactly
supported; its half-collar current is compactly supported and its two source
integrals obey Stokes. -/
theorem programPT06WarpedNullCompactSupportedStokes_bundle :
    ContDiff Real ∞ programPT06WarpedNullCompactDensity ∧
      programPT06WarpedNullCompactDensity ≠ 0 ∧
      HasCompactSupport programPT06WarpedNullCompactDensity ∧
      HasCompactSupport
        (programPT06WarpedNullClosedHalfCollarAffineCurrent
          programPT06WarpedNullCompactDensity) ∧
      Integrable
          (programPT06WarpedNullMetricFiberBulkIntegral
            programPT06WarpedNullCompactDensity)
          programPT06WarpedNullCoordinateSourceMeasure ∧
      Integrable
          (programPT06WarpedNullAffineBoundaryFlux
            programPT06WarpedNullCompactDensity)
          programPT06WarpedNullScreenMeasure ∧
      (∫ source, programPT06WarpedNullMetricFiberBulkIntegral
          programPT06WarpedNullCompactDensity source
          ∂programPT06WarpedNullCoordinateSourceMeasure) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux
          programPT06WarpedNullCompactDensity source
          ∂programPT06WarpedNullScreenMeasure := by
  rcases programPT06WarpedNullCompactDensity_integrable_stokes with
    ⟨hBulk, hBoundary, hStokes⟩
  exact ⟨programPT06WarpedNullCompactDensity_contDiff,
    programPT06WarpedNullCompactDensity_ne_zero,
    programPT06WarpedNullCompactDensity_hasCompactSupport,
    programPT06WarpedNullCompactDensity_halfCollarCurrent_hasCompactSupport,
    hBulk, hBoundary, hStokes⟩

end
end P0EFTJanusProgramPT06WarpedNullCompactSupportedStokes4D
end JanusFormal
