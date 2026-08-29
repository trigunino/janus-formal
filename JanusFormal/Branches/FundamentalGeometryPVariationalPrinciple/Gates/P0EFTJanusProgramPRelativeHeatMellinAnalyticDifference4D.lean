import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Congr
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Analytic Mellin continuation of a difference of heat traces

The Gamma-normalized Mellin transform is linear in the heat trace.  For

```text
h_rel(t) = h_actual(t) - h_reference(t)
```

one therefore has, on the common convergence half-plane,

```text
zeta_rel(s) = zeta_actual(s) - zeta_reference(s).
```

If all three continuations are analytic on one common open preconnected domain
joining that half-plane to zero, the identity theorem extends this equality to
the whole domain.  In particular,

```text
zeta'_rel(0) = zeta'_actual(0) - zeta'_reference(0).
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- Pointwise difference of two positive-time heat traces. -/
def heatTraceDifference
    (actual reference : HeatTime → Real) : HeatTime → Real :=
  fun time => actual time - reference time

/-- Positive-time extension is linear under subtraction. -/
theorem positiveTimeTraceExtension_difference
    (actual reference : HeatTime → Real) (time : Real) :
    positiveTimeTraceExtension (heatTraceDifference actual reference) time =
      positiveTimeTraceExtension actual time -
        positiveTimeTraceExtension reference time := by
  by_cases hTime : 0 < time
  · simp [positiveTimeTraceExtension, heatTraceDifference, hTime]
  · simp [positiveTimeTraceExtension, heatTraceDifference, hTime]

/-- The Mellin kernel is linear under subtraction of heat traces. -/
theorem relativeHeatMellinKernel_difference
    (actual reference : HeatTime → Real)
    (spectral : Complex) (time : Real) :
    relativeHeatMellinKernel (heatTraceDifference actual reference) spectral time =
      relativeHeatMellinKernel actual spectral time -
        relativeHeatMellinKernel reference spectral time := by
  unfold relativeHeatMellinKernel
  rw [positiveTimeTraceExtension_difference]
  push_cast
  ring

/-- The unnormalized Mellin integral is linear on the common integrability
domain. -/
theorem relativeHeatMellinIntegral_difference
    (actual reference : HeatTime → Real)
    (spectral : Complex)
    (hActual : IntegrableOn
      (relativeHeatMellinKernel actual spectral) (Set.Ioi (0 : Real)))
    (hReference : IntegrableOn
      (relativeHeatMellinKernel reference spectral) (Set.Ioi (0 : Real))) :
    relativeHeatMellinIntegral (heatTraceDifference actual reference) spectral =
      relativeHeatMellinIntegral actual spectral -
        relativeHeatMellinIntegral reference spectral := by
  unfold relativeHeatMellinIntegral
  have hKernel :
      relativeHeatMellinKernel (heatTraceDifference actual reference) spectral =
        fun time => relativeHeatMellinKernel actual spectral time -
          relativeHeatMellinKernel reference spectral time := by
    funext time
    exact relativeHeatMellinKernel_difference actual reference spectral time
  rw [hKernel]
  exact integral_sub hActual hReference

/-- Gamma-normalized Mellin candidates are linear under subtraction. -/
theorem relativeHeatMellinZetaCandidate_difference
    (actual reference : HeatTime → Real)
    (spectral : Complex)
    (hActual : IntegrableOn
      (relativeHeatMellinKernel actual spectral) (Set.Ioi (0 : Real)))
    (hReference : IntegrableOn
      (relativeHeatMellinKernel reference spectral) (Set.Ioi (0 : Real))) :
    relativeHeatMellinZetaCandidate (heatTraceDifference actual reference)
        spectral =
      relativeHeatMellinZetaCandidate actual spectral -
        relativeHeatMellinZetaCandidate reference spectral := by
  unfold relativeHeatMellinZetaCandidate
  rw [relativeHeatMellinIntegral_difference actual reference spectral hActual
    hReference]
  ring

/-- Common analytic domain for a relative continuation and its actual/reference
components. -/
structure RelativeHeatMellinAnalyticDifferenceData
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    (relative : RelativeHeatMellinZetaContinuationData relativeFinitePart)
    (actual : RelativeHeatMellinZetaContinuationData actualFinitePart)
    (reference : RelativeHeatMellinZetaContinuationData referenceFinitePart) where
  domain : Set Complex
  isOpen_domain : IsOpen domain
  isPreconnected_domain : IsPreconnected domain
  zero_mem_domain : (0 : Complex) ∈ domain
  seed : Complex
  seed_mem_domain : seed ∈ domain
  seed_mem_commonMellinHalfPlane :
    max relative.convergenceAbscissa
      (max actual.convergenceAbscissa reference.convergenceAbscissa) < seed.re
  relative_analytic : AnalyticOnNhd Complex relative.zeta domain
  difference_analytic : AnalyticOnNhd Complex
    (fun spectral => actual.zeta spectral - reference.zeta spectral) domain

namespace RelativeHeatMellinAnalyticDifferenceData

/-- The three continuations agree with the Mellin subtraction formula near the
common seed. -/
theorem eventuallyEq_relative_difference_at_seed
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    {relative : RelativeHeatMellinZetaContinuationData relativeFinitePart}
    {actual : RelativeHeatMellinZetaContinuationData actualFinitePart}
    {reference : RelativeHeatMellinZetaContinuationData referenceFinitePart}
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    relative.zeta =ᶠ[𝓝 data.seed]
      (fun spectral => actual.zeta spectral - reference.zeta spectral) := by
  let commonAbscissa :=
    max relative.convergenceAbscissa
      (max actual.convergenceAbscissa reference.convergenceAbscissa)
  have hOpen : IsOpen {spectral : Complex | commonAbscissa < spectral.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hNeighborhood :
      {spectral : Complex | commonAbscissa < spectral.re} ∈ 𝓝 data.seed :=
    hOpen.mem_nhds data.seed_mem_commonMellinHalfPlane
  filter_upwards [hNeighborhood] with spectral hSpectral
  have hRelative : relative.convergenceAbscissa < spectral.re :=
    lt_of_le_of_lt (le_max_left _ _) hSpectral
  have hActual : actual.convergenceAbscissa < spectral.re :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hSpectral
  have hReference : reference.convergenceAbscissa < spectral.re :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_max_right _ _)) hSpectral
  calc
    relative.zeta spectral =
        relativeHeatMellinZetaCandidate
          (heatTraceDifference actualTrace referenceTrace) spectral :=
      relative.zeta_eq_mellin spectral hRelative
    _ = relativeHeatMellinZetaCandidate actualTrace spectral -
        relativeHeatMellinZetaCandidate referenceTrace spectral :=
      relativeHeatMellinZetaCandidate_difference actualTrace referenceTrace
        spectral (actual.mellin_integrable spectral hActual)
          (reference.mellin_integrable spectral hReference)
    _ = actual.zeta spectral - reference.zeta spectral := by
      rw [actual.zeta_eq_mellin spectral hActual,
        reference.zeta_eq_mellin spectral hReference]

/-- Identity theorem on the common analytic domain. -/
theorem zeta_eq_difference_on_domain
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    {relative : RelativeHeatMellinZetaContinuationData relativeFinitePart}
    {actual : RelativeHeatMellinZetaContinuationData actualFinitePart}
    {reference : RelativeHeatMellinZetaContinuationData referenceFinitePart}
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    Set.EqOn relative.zeta
      (fun spectral => actual.zeta spectral - reference.zeta spectral)
      data.domain :=
  data.relative_analytic.eqOn_of_preconnected_of_eventuallyEq
    data.difference_analytic data.isPreconnected_domain data.seed_mem_domain
      data.eventuallyEq_relative_difference_at_seed

/-- The subtraction identity holds on a neighborhood of zero. -/
theorem eventuallyEq_relative_difference_at_zero
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    {relative : RelativeHeatMellinZetaContinuationData relativeFinitePart}
    {actual : RelativeHeatMellinZetaContinuationData actualFinitePart}
    {reference : RelativeHeatMellinZetaContinuationData referenceFinitePart}
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    relative.zeta =ᶠ[𝓝 (0 : Complex)]
      (fun spectral => actual.zeta spectral - reference.zeta spectral) := by
  have hDomain : data.domain ∈ 𝓝 (0 : Complex) :=
    data.isOpen_domain.mem_nhds data.zero_mem_domain
  filter_upwards [hDomain] with spectral hSpectral
  exact data.zeta_eq_difference_on_domain hSpectral

/-- Derivative at zero is additive under the analytically continued difference. -/
theorem derivativeAtZero_eq_difference
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    {relative : RelativeHeatMellinZetaContinuationData relativeFinitePart}
    {actual : RelativeHeatMellinZetaContinuationData actualFinitePart}
    {reference : RelativeHeatMellinZetaContinuationData referenceFinitePart}
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    relative.derivativeAtZero =
      actual.derivativeAtZero - reference.derivativeAtZero := by
  have hDifference :
      HasDerivAt
        (fun spectral => actual.zeta spectral - reference.zeta spectral)
        (actual.derivativeAtZero - reference.derivativeAtZero) 0 :=
    actual.hasDerivAt_zero.sub reference.hasDerivAt_zero
  have hDifferenceAsRelative :
      HasDerivAt relative.zeta
        (actual.derivativeAtZero - reference.derivativeAtZero) 0 :=
    hDifference.congr_of_eventuallyEq
      data.eventuallyEq_relative_difference_at_zero
  exact relative.hasDerivAt_zero.unique hDifferenceAsRelative

/-- The finite-part logarithm of the relative trace is the difference of the
actual and reference finite-part logarithms. -/
theorem finitePartLogDeterminant_eq_difference
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    {relative : RelativeHeatMellinZetaContinuationData relativeFinitePart}
    {actual : RelativeHeatMellinZetaContinuationData actualFinitePart}
    {reference : RelativeHeatMellinZetaContinuationData referenceFinitePart}
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    relativeHeatFinitePartLogDeterminant relativeFinitePart =
      relativeHeatFinitePartLogDeterminant actualFinitePart -
        relativeHeatFinitePartLogDeterminant referenceFinitePart := by
  calc
    relativeHeatFinitePartLogDeterminant relativeFinitePart =
        -relative.derivativeAtZero.re := relative.finitePart_realPart
    _ = -(actual.derivativeAtZero - reference.derivativeAtZero).re := by
      rw [data.derivativeAtZero_eq_difference]
    _ = -actual.derivativeAtZero.re + reference.derivativeAtZero.re := by
      rw [Complex.sub_re]
      ring
    _ = relativeHeatFinitePartLogDeterminant actualFinitePart -
        relativeHeatFinitePartLogDeterminant referenceFinitePart := by
      rw [actual.finitePart_realPart, reference.finitePart_realPart]
      ring

/-- Public analytic-difference checkpoint. -/
theorem relative_heat_mellin_analytic_difference_gate
    {actualTrace referenceTrace : HeatTime → Real}
    {relativeFinitePart : RelativeHeatFinitePartData
      (heatTraceDifference actualTrace referenceTrace)}
    {actualFinitePart : RelativeHeatFinitePartData actualTrace}
    {referenceFinitePart : RelativeHeatFinitePartData referenceTrace}
    (relative : RelativeHeatMellinZetaContinuationData relativeFinitePart)
    (actual : RelativeHeatMellinZetaContinuationData actualFinitePart)
    (reference : RelativeHeatMellinZetaContinuationData referenceFinitePart)
    (data : RelativeHeatMellinAnalyticDifferenceData relative actual reference) :
    Set.EqOn relative.zeta
      (fun spectral => actual.zeta spectral - reference.zeta spectral)
      data.domain ∧
    relative.derivativeAtZero =
      actual.derivativeAtZero - reference.derivativeAtZero ∧
    relativeHeatFinitePartLogDeterminant relativeFinitePart =
      relativeHeatFinitePartLogDeterminant actualFinitePart -
        relativeHeatFinitePartLogDeterminant referenceFinitePart :=
  ⟨data.zeta_eq_difference_on_domain,
    data.derivativeAtZero_eq_difference,
    data.finitePartLogDeterminant_eq_difference⟩

end RelativeHeatMellinAnalyticDifferenceData

end
end P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D
end JanusFormal
