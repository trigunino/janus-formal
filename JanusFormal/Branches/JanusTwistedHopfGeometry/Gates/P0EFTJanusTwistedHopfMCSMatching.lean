import Mathlib
import JanusFormal.Branches.JanusTwistedHopfGeometry.Gates.P0EFTJanusTwistedHopfScaleLaw
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusCorrectedDiscreteMCSMatching

namespace JanusFormal
namespace P0EFTJanusTwistedHopfMCSMatching

set_option autoImplicit false

open P0EFTJanusTwistedHopfScaleLaw
open P0EFTJanusCorrectedDiscreteMCSMatching

/--
Compatibility of the corrected discrete MCS vacuum with the PT-Hopf quotient.
The RG hierarchy exponent is identified with the logarithmic tunnel period, and
the exact-solution length and UV anchor are the same physical quantities.
-/
structure TwistedHopfMCSMatching where
  hopf : TwistedHopfScaleData
  mcs : CorrectedDiscreteMCSMatching
  sameTunnelExponent :
    mcs.levelLocked.hierarchyExponent = hopf.tunnelPeriod
  sameUVLength :
    mcs.levelLocked.uvLength = hopf.uvLength
  sameAlphaLength :
    mcs.quantum.vacuum.alphaSquaredLength =
      hopf.alphaSquaredLength

/--
The corrected MCS equation becomes a direct formula for the quotient
contraction:

`K * exp(x_*) = 2*pi*lambda`.
-/
theorem level_vacuum_amplitude_fixes_hopf_contraction
    (s : TwistedHopfMCSMatching) :
    (s.mcs.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp s.mcs.quantum.vacuum.logRatio =
      2 * Real.pi * s.hopf.contraction := by
  have hCorrected := corrected_exponent_matching s.mcs
  rw [s.sameTunnelExponent] at hCorrected
  have hContraction := s.hopf.contractionPeriodLaw
  have hExpAdd :
      Real.exp
          (s.mcs.quantum.vacuum.logRatio + s.hopf.tunnelPeriod) =
        Real.exp s.mcs.quantum.vacuum.logRatio *
          Real.exp s.hopf.tunnelPeriod :=
    Real.exp_add _ _
  rw [hExpAdd] at hCorrected
  calc
    (s.mcs.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp s.mcs.quantum.vacuum.logRatio =
      s.hopf.contraction *
        ((s.mcs.levelLocked.chernSimonsLevel : ℝ) *
          (Real.exp s.mcs.quantum.vacuum.logRatio *
            Real.exp s.hopf.tunnelPeriod)) := by
              calc
                _ =
                    (s.hopf.contraction *
                      Real.exp s.hopf.tunnelPeriod) *
                      ((s.mcs.levelLocked.chernSimonsLevel : ℝ) *
                        Real.exp s.mcs.quantum.vacuum.logRatio) := by
                          rw [hContraction]
                          ring
                _ = _ := by ring
    _ = s.hopf.contraction * (2 * Real.pi) := by
      rw [hCorrected]
    _ = 2 * Real.pi * s.hopf.contraction := by ring

/--
Combining the geometric hierarchy `2*A*lambda = ell_UV` with the corrected MCS
matching gives the absolute relation

`K * exp(x_*) * A = pi * ell_UV`.
-/
theorem geometric_mcs_alpha_law
    (s : TwistedHopfMCSMatching) :
    (s.mcs.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp s.mcs.quantum.vacuum.logRatio *
        s.hopf.alphaSquaredLength =
      Real.pi * s.hopf.uvLength := by
  have hAmplitude := level_vacuum_amplitude_fixes_hopf_contraction s
  have hHierarchy := two_alpha_times_contraction_eq_uv s.hopf
  calc
    (s.mcs.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp s.mcs.quantum.vacuum.logRatio *
        s.hopf.alphaSquaredLength =
      (2 * Real.pi * s.hopf.contraction) *
        s.hopf.alphaSquaredLength := by rw [hAmplitude]
    _ = Real.pi *
        (2 * s.hopf.alphaSquaredLength * s.hopf.contraction) := by ring
    _ = Real.pi * s.hopf.uvLength := by rw [hHierarchy]

/-- Primitive level turns the contraction into the normalized vacuum amplitude. -/
theorem primitive_level_hopf_contraction
    (s : TwistedHopfMCSMatching)
    (hLevel : s.mcs.levelLocked.chernSimonsLevel = 1) :
    Real.exp s.mcs.quantum.vacuum.logRatio =
      2 * Real.pi * s.hopf.contraction := by
  have h := level_vacuum_amplitude_fixes_hopf_contraction s
  rw [hLevel] at h
  norm_num at h ⊢
  exact h

/--
This closes the mathematical identification of the Hopf modulus with the MCS
vacuum data.  Predictivity still requires the beta function, allowed level and
renormalized vacuum to be derived rather than fitted.
-/
structure GeometricMCSClosureStatus where
  twistedHopfGeometryConstructed : Prop
  correctedMCSMatchingDerived : Prop
  tunnelExponentEqualsRGExponent : Prop
  quotientContractionDerived : Prop
  vacuumAmplitudeDerived : Prop
  anomalyAllowedLevelSelected : Prop
  noObservedScaleImported : Prop
  absoluteAlphaPredicted : Prop

end P0EFTJanusTwistedHopfMCSMatching
end JanusFormal
