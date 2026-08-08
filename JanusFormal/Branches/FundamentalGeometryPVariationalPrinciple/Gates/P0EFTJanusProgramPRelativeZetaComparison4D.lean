import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeDeterminantPhase4D

/-!
# Comparison with a complex relative zeta determinant

The finite-part construction provides the determinant magnitude directly from
the intrinsic heat trace.  A Mellin continuation supplies a complex zeta
function regular at zero.  The single comparison required here is that the
real part of minus its derivative agrees with the finite-part logarithm.

The imaginary part then supplies the spectral-asymmetry phase automatically.
The analytic construction of the Mellin continuation is not hidden in this
file; it remains the explicit input `hasDerivAt_zero` together with the
finite-part comparison.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaComparison4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeDeterminantPhase4D

/-- A complex zeta function regular at zero and compatible with one finite-part
heat renormalization. -/
structure RelativeZetaComparisonData
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace) where
  zeta : Complex → Complex
  derivativeAtZero : Complex
  hasDerivAt_zero : HasDerivAt zeta derivativeAtZero 0
  finitePart_realPart :
    relativeHeatFinitePartLogDeterminant finitePart = -derivativeAtZero.re

/-- Complex zeta determinant `exp(-zeta'(0))`. -/
def relativeZetaDeterminant
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) : Complex :=
  Complex.exp (-comparison.derivativeAtZero)

/-- The zeta determinant never vanishes. -/
theorem relativeZetaDeterminant_ne_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    relativeZetaDeterminant comparison ≠ 0 :=
  Complex.exp_ne_zero _

/-- Its norm is exactly the previously constructed finite-part determinant. -/
theorem norm_relativeZetaDeterminant
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    ‖relativeZetaDeterminant comparison‖ =
      relativeHeatFinitePartDeterminant finitePart := by
  rw [relativeZetaDeterminant, Complex.norm_exp]
  change Real.exp (-comparison.derivativeAtZero.re) = _
  rw [← comparison.finitePart_realPart]
  rfl

/-- The normalized zeta determinant is the canonical unitary phase. -/
def relativeZetaPhase
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) : Complex :=
  relativeZetaDeterminant comparison /
    (relativeHeatFinitePartDeterminant finitePart : Complex)

/-- The normalized zeta phase has norm one. -/
theorem relativeZetaPhase_norm_one
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    ‖relativeZetaPhase comparison‖ = 1 := by
  rw [relativeZetaPhase, norm_div,
    norm_relativeZetaDeterminant comparison, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (relativeHeatFinitePartDeterminant_pos finitePart),
    div_self (relativeHeatFinitePartDeterminant_ne_zero finitePart)]

/-- Zeta comparison canonically produces the phase packet used by the Quillen
metric anchor. -/
def RelativeZetaComparisonData.toPhase
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    RelativeDeterminantPhaseData where
  phase := relativeZetaPhase comparison
  phase_norm_one := relativeZetaPhase_norm_one comparison

/-- Recombining the finite-part magnitude with the zeta phase gives exactly the
complex zeta determinant. -/
theorem relativeHeatComplexDeterminant_zetaPhase
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    relativeHeatComplexDeterminant finitePart comparison.toPhase =
      relativeZetaDeterminant comparison := by
  unfold relativeHeatComplexDeterminant RelativeZetaComparisonData.toPhase
    relativeZetaPhase
  have hNonzero :
      (relativeHeatFinitePartDeterminant finitePart : Complex) ≠ 0 := by
    exact_mod_cast relativeHeatFinitePartDeterminant_ne_zero finitePart
  field_simp

/-- Public zeta-comparison checkpoint. -/
theorem relative_zeta_comparison_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (comparison : RelativeZetaComparisonData finitePart) :
    relativeZetaDeterminant comparison ≠ 0 ∧
      ‖relativeZetaDeterminant comparison‖ =
        relativeHeatFinitePartDeterminant finitePart :=
  ⟨relativeZetaDeterminant_ne_zero comparison,
    norm_relativeZetaDeterminant comparison⟩

end
end P0EFTJanusProgramPRelativeZetaComparison4D
end JanusFormal
