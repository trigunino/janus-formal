import Mathlib.Analysis.Complex.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-!
# Unitary phase of a finite-part relative determinant

The heat finite part determines a positive determinant magnitude.  A complex
determinant additionally needs the spectral-asymmetry phase.  This file keeps
that phase as one explicit unit complex number and proves that it does not
change the already constructed magnitude.

In a later eta theorem the phase can be instantiated by the exponentiated eta
invariant.  No eta value is fabricated here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeDeterminantPhase4D

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- One unitary spectral-asymmetry phase. -/
structure RelativeDeterminantPhaseData where
  phase : Complex
  phase_norm_one : ‖phase‖ = 1

/-- Complex determinant obtained from the positive finite-part magnitude and a
unitary phase. -/
def relativeHeatComplexDeterminant
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace)
    (phase : RelativeDeterminantPhaseData) : Complex :=
  (relativeHeatFinitePartDeterminant finitePart : Complex) * phase.phase

/-- The phase leaves the determinant norm unchanged. -/
theorem norm_relativeHeatComplexDeterminant
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace)
    (phase : RelativeDeterminantPhaseData) :
    ‖relativeHeatComplexDeterminant finitePart phase‖ =
      relativeHeatFinitePartDeterminant finitePart := by
  rw [relativeHeatComplexDeterminant, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (relativeHeatFinitePartDeterminant_pos finitePart),
    phase.phase_norm_one, mul_one]

/-- The complex determinant is nonzero. -/
theorem relativeHeatComplexDeterminant_ne_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace)
    (phase : RelativeDeterminantPhaseData) :
    relativeHeatComplexDeterminant finitePart phase ≠ 0 := by
  intro hZero
  have hNorm := congrArg norm hZero
  rw [norm_relativeHeatComplexDeterminant finitePart phase, norm_zero] at hNorm
  exact relativeHeatFinitePartDeterminant_ne_zero finitePart hNorm

/-- Squared complex norm is the square of the positive determinant. -/
theorem normSq_relativeHeatComplexDeterminant
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace)
    (phase : RelativeDeterminantPhaseData) :
    Complex.normSq (relativeHeatComplexDeterminant finitePart phase) =
      (relativeHeatFinitePartDeterminant finitePart) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq,
    norm_relativeHeatComplexDeterminant finitePart phase]

/-- Public determinant-phase checkpoint. -/
theorem relative_determinant_phase_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace)
    (phase : RelativeDeterminantPhaseData) :
    relativeHeatComplexDeterminant finitePart phase ≠ 0 ∧
      ‖relativeHeatComplexDeterminant finitePart phase‖ =
        relativeHeatFinitePartDeterminant finitePart :=
  ⟨relativeHeatComplexDeterminant_ne_zero finitePart phase,
    norm_relativeHeatComplexDeterminant finitePart phase⟩

end
end P0EFTJanusProgramPRelativeDeterminantPhase4D
end JanusFormal
