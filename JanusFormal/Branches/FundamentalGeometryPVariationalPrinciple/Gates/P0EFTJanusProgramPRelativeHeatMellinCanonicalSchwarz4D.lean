import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D

/-!
# Canonical Mellin Schwarz symmetry in the convergence half-plane

The remaining kernel-Schwarz packet stored compatibility of conjugation with
the Bochner integral.  In the certified Mellin half-plane this compatibility is
automatic:

* the continuation packet already proves integrability of the Mellin kernel;
* complex conjugation is a continuous real-linear isometry;
* continuous linear maps commute with integrals of integrable functions.

This file bundles complex conjugation as a real continuous linear map, proves
the generic integral-conjugation theorem, and derives both unnormalized and
Gamma-normalized Schwarz symmetry directly from the existing Mellin
integrability certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinCanonicalSchwarz4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D

/-- Complex conjugation as a real-linear map. -/
def complexConjugationLinearMap : Complex →ₗ[Real] Complex where
  toFun := Complex.conj
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro scalar value
    simp

/-- Complex conjugation as a real continuous linear isometry. -/
def complexConjugationCLM : Complex →L[Real] Complex :=
  complexConjugationLinearMap.mkContinuous 1 (by
    intro value
    simp [complexConjugationLinearMap])

@[simp]
theorem complexConjugationCLM_apply (value : Complex) :
    complexConjugationCLM value = Complex.conj value :=
  rfl

/-- Conjugation commutes with the Bochner integral of an integrable complex
function. -/
theorem integral_complexConjugation
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {function : α → Complex}
    (hIntegrable : Integrable function μ) :
    (∫ point, Complex.conj (function point) ∂μ) =
      Complex.conj (∫ point, function point ∂μ) := by
  first
  | simpa [complexConjugationCLM] using
      (complexConjugationCLM.integral_comp_comm hIntegrable).symm
  | simpa [complexConjugationCLM] using
      (complexConjugationCLM.integral_comp_comm hIntegrable)
  | simpa [complexConjugationCLM] using
      (ContinuousLinearMap.integral_comp_comm complexConjugationCLM
        hIntegrable).symm
  | simpa [complexConjugationCLM] using
      (ContinuousLinearMap.integral_comp_comm complexConjugationCLM
        hIntegrable)

/-- The unnormalized Mellin integral has Schwarz symmetry throughout its
certified convergence half-plane. -/
theorem mellinIntegral_schwarz_of_convergent
    {heatTrace : HeatTime → Real}
    {finitePart : P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
      RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    relativeHeatMellinIntegral heatTrace spectral =
      Complex.conj
        (relativeHeatMellinIntegral heatTrace (Complex.conj spectral)) := by
  have hConjugate :
      continuation.convergenceAbscissa < (Complex.conj spectral).re := by
    simpa using hSpectral
  have hIntegrable :=
    continuation.mellin_integrable (Complex.conj spectral) hConjugate
  calc
    relativeHeatMellinIntegral heatTrace spectral =
        ∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace spectral time := rfl
    _ = ∫ time in Set.Ioi (0 : Real),
        Complex.conj
          (relativeHeatMellinKernel heatTrace
            (Complex.conj spectral) time) := by
      apply integral_congr_ae
      filter_upwards [] with time
      exact relativeHeatMellinKernel_schwarz heatTrace spectral time
    _ = Complex.conj
        (∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace
            (Complex.conj spectral) time) := by
      exact integral_complexConjugation hIntegrable
    _ = Complex.conj
        (relativeHeatMellinIntegral heatTrace (Complex.conj spectral)) := rfl

/-- The Gamma-normalized Mellin candidate inherits canonical Schwarz symmetry
in the convergence half-plane. -/
theorem mellinZetaCandidate_schwarz_of_convergent
    {heatTrace : HeatTime → Real}
    {finitePart : P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
      RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    relativeHeatMellinZetaCandidate heatTrace spectral =
      Complex.conj
        (relativeHeatMellinZetaCandidate heatTrace
          (Complex.conj spectral)) := by
  let integralSchwarz : RelativeHeatMellinIntegralSchwarzData heatTrace :=
    { mellinIntegral_schwarz := fun current => by
        by_cases hCurrent : continuation.convergenceAbscissa < current.re
        · exact continuation.mellinIntegral_schwarz_of_convergent current hCurrent
        · by_cases hConjugate :
            continuation.convergenceAbscissa < (Complex.conj current).re
          · exact continuation.mellinIntegral_schwarz_of_convergent current
              (by simpa using hConjugate)
          · simp [relativeHeatMellinIntegral,
              integral_undef
                (not_integrableOn_iff.mp hCurrent),
              integral_undef
                (not_integrableOn_iff.mp hConjugate)] }
  exact integralSchwarz.candidate_schwarz spectral

/-- Public canonical half-plane Schwarz checkpoint. -/
theorem relative_heat_mellin_canonical_schwarz_gate
    {heatTrace : HeatTime → Real}
    {finitePart : P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
      RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    (∀ spectral,
      continuation.convergenceAbscissa < spectral.re →
        relativeHeatMellinIntegral heatTrace spectral =
          Complex.conj
            (relativeHeatMellinIntegral heatTrace
              (Complex.conj spectral))) ∧
    (∀ spectral,
      continuation.convergenceAbscissa < spectral.re →
        relativeHeatMellinZetaCandidate heatTrace spectral =
          Complex.conj
            (relativeHeatMellinZetaCandidate heatTrace
              (Complex.conj spectral))) :=
  ⟨continuation.mellinIntegral_schwarz_of_convergent,
    continuation.mellinZetaCandidate_schwarz_of_convergent⟩

end
end P0EFTJanusProgramPRelativeHeatMellinCanonicalSchwarz4D
end JanusFormal
