/-
Serial completion matrix for the two deepest remaining Janus programs.

The alternatives are not substitutes at the final level:

* the nonlinear bimetric program determines the covariant field equations,
  PT charge and junction map;
* the quantum world-volume program generates and normalizes the dimensionful
  LL charge scale.

Absolute no-fit alpha closure requires both plus a compatibility theorem.
-/

import JanusFormal.Branches.WorldvolumeQuantumAlpha
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha
import JanusFormal.Branches.RP4TwistedFourFormAlpha

namespace JanusFormal
namespace JanusAlphaDeepCompletionMatrix

set_option autoImplicit false

structure DeepCompletionStatus where
  nonlinearBimetricJunctionClosed : Prop
  quantumWorldvolumeScaleClosed : Prop
  bulkBoundaryChargeCompatibilityProved : Prop
  sourceNormalizationReconciled : Prop
  lorentzianProjectiveMatchingClosed : Prop
  noObservedScaleImported : Prop
  absoluteAlphaClosed : Prop


def deepCompletionInputsClosed (s : DeepCompletionStatus) : Prop :=
  s.nonlinearBimetricJunctionClosed /\
  s.quantumWorldvolumeScaleClosed /\
  s.bulkBoundaryChargeCompatibilityProved /\
  s.sourceNormalizationReconciled /\
  s.lorentzianProjectiveMatchingClosed /\
  s.noObservedScaleImported


def fullAbsoluteAlphaClosure (s : DeepCompletionStatus) : Prop :=
  deepCompletionInputsClosed s /\ s.absoluteAlphaClosed


theorem missing_bimetric_program_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.nonlinearBimetricJunctionClosed) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  exact hMissing h.1.1


theorem missing_quantum_program_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.quantumWorldvolumeScaleClosed) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  exact hMissing h.1.2.1


theorem missing_bulk_boundary_compatibility_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.bulkBoundaryChargeCompatibilityProved) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  exact hMissing h.1.2.2.1

/-- A policy theorem turning the six derived inputs into the final prediction. -/
theorem both_programs_and_compatibility_transport_to_absolute_alpha
    (s : DeepCompletionStatus)
    (hInputs : deepCompletionInputsClosed s)
    (hTransport : deepCompletionInputsClosed s -> s.absoluteAlphaClosed) :
    fullAbsoluteAlphaClosure s := by
  exact ⟨hInputs, hTransport hInputs⟩

end JanusAlphaDeepCompletionMatrix
end JanusFormal
