import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaComparison4D

/-!
# Mellin continuation of the intrinsic relative heat trace

The earlier zeta-comparison packet accepted a complex function regular at zero.
This file records the missing analytic origin of that function.  In a right
half-plane it must be the Gamma-normalized Mellin transform of the intrinsic
relative heat trace; the same function is then continued differentiably to
zero and compared with the finite-part logarithm.

Thus a caller can no longer provide an unrelated holomorphic germ merely
having the correct real derivative.  The right-half-plane heat representation
is part of the certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaComparison4D

/-- Complex Mellin kernel of a positive-time relative heat trace. -/
def relativeHeatMellinKernel
    (heatTrace : HeatTime → Real) (spectral : Complex) (time : Real) : Complex :=
  (time : Complex) ^ (spectral - 1) *
    (positiveTimeTraceExtension heatTrace time : Complex)

/-- Unnormalized Mellin transform on every half-plane where the Bochner
integral converges. -/
def relativeHeatMellinIntegral
    (heatTrace : HeatTime → Real) (spectral : Complex) : Complex :=
  ∫ time in Set.Ioi (0 : Real),
    relativeHeatMellinKernel heatTrace spectral time

/-- Gamma-normalized heat-zeta candidate.  The expression is used only in the
certified right half-plane; its continuation to zero is a separate field of
the packet below. -/
def relativeHeatMellinZetaCandidate
    (heatTrace : HeatTime → Real) (spectral : Complex) : Complex :=
  (Complex.Gamma spectral)⁻¹ *
    relativeHeatMellinIntegral heatTrace spectral

/-- Honest Mellin-to-zeta continuation data. -/
structure RelativeHeatMellinZetaContinuationData
    {heatTrace : HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace) where
  convergenceAbscissa : Real
  zeta : Complex → Complex
  derivativeAtZero : Complex
  mellin_integrable : ∀ spectral : Complex,
    convergenceAbscissa < spectral.re →
      IntegrableOn
        (relativeHeatMellinKernel heatTrace spectral)
        (Set.Ioi (0 : Real))
  zeta_eq_mellin : ∀ spectral : Complex,
    convergenceAbscissa < spectral.re →
      zeta spectral = relativeHeatMellinZetaCandidate heatTrace spectral
  hasDerivAt_zero : HasDerivAt zeta derivativeAtZero 0
  finitePart_realPart :
    relativeHeatFinitePartLogDeterminant finitePart = -derivativeAtZero.re

/-- Forget the explicit half-plane Mellin representation and retain the zeta
comparison consumed by the determinant and Quillen layers. -/
def RelativeHeatMellinZetaContinuationData.toZetaComparison
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    RelativeZetaComparisonData finitePart where
  zeta := continuation.zeta
  derivativeAtZero := continuation.derivativeAtZero
  hasDerivAt_zero := continuation.hasDerivAt_zero
  finitePart_realPart := continuation.finitePart_realPart

/-- The determinant obtained from an honest Mellin continuation. -/
def relativeHeatMellinZetaDeterminant
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) : Complex :=
  relativeZetaDeterminant continuation.toZetaComparison

/-- The Mellin zeta determinant is nonzero and has the finite-part magnitude. -/
theorem relativeHeatMellinZetaDeterminant_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    relativeHeatMellinZetaDeterminant continuation ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant continuation‖ =
        relativeHeatFinitePartDeterminant finitePart :=
  relative_zeta_comparison_gate continuation.toZetaComparison

/-- Public checkpoint displaying both the right-half-plane heat formula and the
regular determinant at zero. -/
theorem relative_heat_mellin_zeta_continuation_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    (∀ spectral : Complex,
      continuation.convergenceAbscissa < spectral.re →
        continuation.zeta spectral =
          relativeHeatMellinZetaCandidate heatTrace spectral) ∧
      relativeHeatMellinZetaDeterminant continuation ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant continuation‖ =
        relativeHeatFinitePartDeterminant finitePart :=
  ⟨continuation.zeta_eq_mellin,
    relativeHeatMellinZetaDeterminant_gate continuation⟩

end
end P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
end JanusFormal
