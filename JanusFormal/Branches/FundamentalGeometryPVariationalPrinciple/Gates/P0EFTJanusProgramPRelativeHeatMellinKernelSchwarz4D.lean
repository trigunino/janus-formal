import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D

/-!
# Pointwise Schwarz symmetry of the relative heat Mellin kernel

For a real heat trace, complex conjugation of the Mellin kernel is entirely
pointwise:

```text
kernel(s,t) = conj (kernel(conj s,t)).
```

The real trace factor is fixed by conjugation, while complex powers satisfy the
usual conjugation law.  Consequently the only remaining integration-level
input is that conjugation commutes with the Bochner integral of the conjugated
kernel.

This file records that map-integral statement and derives Schwarz symmetry of
the unnormalized Mellin integral, then of the Gamma-normalized candidate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D

/-- Pointwise conjugation symmetry of the Mellin heat kernel. -/
theorem relativeHeatMellinKernel_schwarz
    (heatTrace : HeatTime → Real)
    (spectral : Complex) (time : Real) :
    relativeHeatMellinKernel heatTrace spectral time =
      conj
        (relativeHeatMellinKernel heatTrace (conj spectral) time) := by
  by_cases hTime : 0 < time
  · have hArg : (time : Complex).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hTime.le]
      exact ne_of_lt Real.pi_pos
    have hPow :
        (time : Complex) ^ (spectral - 1) =
          conj ((time : Complex) ^ (conj spectral - 1)) := by
      simpa using
        (Complex.cpow_conj (time : Complex) (conj spectral - 1) hArg)
    rw [relativeHeatMellinKernel, relativeHeatMellinKernel, hPow]
    simp
  · unfold relativeHeatMellinKernel
    rw [positiveTimeTraceExtension_of_nonpos heatTrace (le_of_not_gt hTime)]
    simp

/-- Conjugation can be moved through the unnormalized Mellin integral.  This is
the remaining Bochner integration statement after pointwise kernel symmetry has
been proved. -/
structure RelativeHeatMellinKernelSchwarzData
    (heatTrace : HeatTime → Real) where
  conjugate_integral : ∀ spectral : Complex,
    (∫ time in Set.Ioi (0 : Real),
      conj
        (relativeHeatMellinKernel heatTrace
          (conj spectral) time)) =
      conj
        (∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace
            (conj spectral) time)

namespace RelativeHeatMellinKernelSchwarzData

/-- Pointwise kernel conjugation plus map-integral compatibility gives
Schwarz symmetry of the unnormalized Mellin transform. -/
theorem mellinIntegral_schwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinKernelSchwarzData heatTrace)
    (spectral : Complex) :
    relativeHeatMellinIntegral heatTrace spectral =
      conj
        (relativeHeatMellinIntegral heatTrace (conj spectral)) := by
  calc
    relativeHeatMellinIntegral heatTrace spectral =
        ∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace spectral time := rfl
    _ = ∫ time in Set.Ioi (0 : Real),
        conj
          (relativeHeatMellinKernel heatTrace
            (conj spectral) time) := by
      apply integral_congr_ae
      filter_upwards [] with time
      exact relativeHeatMellinKernel_schwarz heatTrace spectral time
    _ = conj
        (∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace
            (conj spectral) time) :=
      data.conjugate_integral spectral
    _ = conj
        (relativeHeatMellinIntegral heatTrace (conj spectral)) := rfl

/-- Convert the kernel-level packet to unnormalized Mellin symmetry. -/
def toMellinIntegralSchwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinKernelSchwarzData heatTrace) :
    RelativeHeatMellinIntegralSchwarzData heatTrace where
  mellinIntegral_schwarz := data.mellinIntegral_schwarz

/-- Gamma-normalized candidate symmetry follows automatically. -/
theorem candidate_schwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinKernelSchwarzData heatTrace)
    (spectral : Complex) :
    relativeHeatMellinZetaCandidate heatTrace spectral =
      conj
        (relativeHeatMellinZetaCandidate heatTrace
          (conj spectral)) :=
  data.toMellinIntegralSchwarz.candidate_schwarz spectral

/-- Public kernel-level Mellin Schwarz checkpoint. -/
theorem relative_heat_mellin_kernel_schwarz_gate
    (heatTrace : HeatTime → Real)
    (data : RelativeHeatMellinKernelSchwarzData heatTrace) :
    (∀ spectral time,
      relativeHeatMellinKernel heatTrace spectral time =
        conj
          (relativeHeatMellinKernel heatTrace
            (conj spectral) time)) ∧
    (∀ spectral,
      relativeHeatMellinIntegral heatTrace spectral =
        conj
          (relativeHeatMellinIntegral heatTrace
            (conj spectral))) ∧
    (∀ spectral,
      relativeHeatMellinZetaCandidate heatTrace spectral =
        conj
          (relativeHeatMellinZetaCandidate heatTrace
            (conj spectral))) :=
  ⟨relativeHeatMellinKernel_schwarz heatTrace,
    data.mellinIntegral_schwarz,
    data.candidate_schwarz⟩

end RelativeHeatMellinKernelSchwarzData

end
end P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D
end JanusFormal
