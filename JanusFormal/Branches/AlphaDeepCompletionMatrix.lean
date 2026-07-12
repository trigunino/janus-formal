/-
Serial completion matrix for the deepest Janus alpha programs.

The programs are not substitutes at the final level:

* the nonlinear bimetric program determines the covariant field equations,
  positive spin-2 spectrum, PT charge and junction map;
* the quantum world-volume program generates and normalizes the dimensionful
  LL charge scale through the RG-improved MCS sector;
* the bulk/boundary compatibility program transports that normalization and
  tests the Euclidean thermal-circle transgression.

Absolute no-fit alpha closure requires all three plus source normalization and
Lorentzian matching.  The active discrete relation is the corrected MCS law
`K*exp(x_*+X)=2*pi`, not the legacy unit-amplitude cancellation ansatz.
-/

import JanusFormal.Branches.WorldvolumeQuantumAlpha
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha
import JanusFormal.Branches.RP4TwistedFourFormAlpha
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusAbsoluteAlphaSynthesis
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusBulkBoundaryChargeNormalization
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusThermalCircleTransgressionScale
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusCorrectedDiscreteMCSMatching
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusMCSBimetricAbsoluteSynthesis

namespace JanusFormal
namespace JanusAlphaDeepCompletionMatrix

set_option autoImplicit false

structure DeepCompletionStatus where
  nonlinearBimetricJunctionClosed : Prop
  quantumWorldvolumeScaleClosed : Prop
  bulkBoundaryChargeCompatibilityProved : Prop
  thermalCircleRouteAudited : Prop
  correctedDiscreteMCSMatchingDerived : Prop
  sourceNormalizationReconciled : Prop
  lorentzianProjectiveMatchingClosed : Prop
  terminalMCSBimetricSpectrumDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaClosed : Prop


def deepCompletionInputsClosed (s : DeepCompletionStatus) : Prop :=
  s.nonlinearBimetricJunctionClosed /\
  s.quantumWorldvolumeScaleClosed /\
  s.bulkBoundaryChargeCompatibilityProved /\
  s.thermalCircleRouteAudited /\
  s.correctedDiscreteMCSMatchingDerived /\
  s.sourceNormalizationReconciled /\
  s.lorentzianProjectiveMatchingClosed /\
  s.terminalMCSBimetricSpectrumDerived /\
  s.noObservedScaleImported


def fullAbsoluteAlphaClosure (s : DeepCompletionStatus) : Prop :=
  deepCompletionInputsClosed s /\ s.absoluteAlphaClosed


theorem missing_bimetric_program_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.nonlinearBimetricJunctionClosed) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  rcases h with ⟨hInputs, _⟩
  rcases hInputs with ⟨hBimetric, _, _, _, _, _, _, _, _⟩
  exact hMissing hBimetric


theorem missing_quantum_program_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.quantumWorldvolumeScaleClosed) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  rcases h with ⟨hInputs, _⟩
  rcases hInputs with ⟨_, hQuantum, _, _, _, _, _, _, _⟩
  exact hMissing hQuantum


theorem missing_bulk_boundary_compatibility_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.bulkBoundaryChargeCompatibilityProved) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  rcases h with ⟨hInputs, _⟩
  rcases hInputs with ⟨_, _, hBulk, _, _, _, _, _, _⟩
  exact hMissing hBulk


theorem missing_corrected_discrete_matching_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.correctedDiscreteMCSMatchingDerived) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  rcases h with ⟨hInputs, _⟩
  rcases hInputs with ⟨_, _, _, _, hCorrected, _, _, _, _⟩
  exact hMissing hCorrected


theorem missing_terminal_spectrum_blocks_full_closure
    (s : DeepCompletionStatus)
    (hMissing : Not s.terminalMCSBimetricSpectrumDerived) :
    Not (fullAbsoluteAlphaClosure s) := by
  intro h
  rcases h with ⟨hInputs, _⟩
  rcases hInputs with ⟨_, _, _, _, _, _, _, hSpectrum, _⟩
  exact hMissing hSpectrum

/-- A policy theorem turning the nine derived inputs into the final prediction. -/
theorem all_programs_transport_to_absolute_alpha
    (s : DeepCompletionStatus)
    (hInputs : deepCompletionInputsClosed s)
    (hTransport : deepCompletionInputsClosed s -> s.absoluteAlphaClosed) :
    fullAbsoluteAlphaClosure s := by
  exact ⟨hInputs, hTransport hInputs⟩

end JanusAlphaDeepCompletionMatrix
end JanusFormal
