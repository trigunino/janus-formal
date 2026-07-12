import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGImprovedSexticVacuum
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusMaxwellChernSimonsChargeNormalization

namespace JanusFormal
namespace P0EFTJanusRGInvariantMCSAlpha

set_option autoImplicit false

open P0EFTJanusRGImprovedSexticVacuum
open P0EFTJanusMaxwellChernSimonsChargeNormalization

/--
Join the one-log composite vacuum to the compact Maxwell--Chern--Simons
normalization.

The RG-invariant mass is represented without division by

`b * t = -lambda`,
`Lambda_RG = mu * exp(t)`.

The stationary point then lies at `x_* = t - 1/3`.
-/
structure RGInvariantMCSAlpha where
  vacuum : OneLogAlphaVacuum
  mcsScale : MaxwellChernSimonsLLScale
  transmutationMass : ℝ
  transmutationLog : ℝ
  transmutationMassPositive : 0 < transmutationMass
  sameCondensate :
    mcsScale.condensateMass = vacuum.condensateMass
  sameAlpha :
    mcsScale.alphaSquaredLength = vacuum.alphaSquaredLength
  betaInvariantLaw :
    vacuum.logCoefficient * transmutationLog =
      -vacuum.sexticCoupling
  transmutationMassLaw :
    transmutationMass =
      vacuum.renormalizationMass * Real.exp transmutationLog

/-- The stationary logarithm is the RG transmutation logarithm minus `1/3`. -/
theorem stationary_log_from_rg_invariant
    (s : RGInvariantMCSAlpha) :
    3 * s.vacuum.logRatio + 1 =
      3 * s.transmutationLog := by
  have hStationary := s.vacuum.stationarityBracket
  have hBeta := s.betaInvariantLaw
  have hFactor :
      s.vacuum.logCoefficient *
        (3 * s.vacuum.logRatio + 1 -
          3 * s.transmutationLog) = 0 := by
    nlinarith [hStationary, hBeta]
  have hCoefficientNonzero : s.vacuum.logCoefficient ≠ 0 :=
    ne_of_gt s.vacuum.logCoefficientPositive
  have hBracket :
      3 * s.vacuum.logRatio + 1 -
        3 * s.transmutationLog = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hCoefficientNonzero
  linarith

/-- The physical condensate is `exp(-1/3)` times the RG-invariant mass. -/
theorem condensate_times_exp_third_eq_transmutation_mass
    (s : RGInvariantMCSAlpha) :
    s.vacuum.condensateMass * Real.exp ((1 : ℝ) / 3) =
      s.transmutationMass := by
  have hLog := stationary_log_from_rg_invariant s
  have hLogAdd :
      s.vacuum.logRatio + (1 : ℝ) / 3 =
        s.transmutationLog := by
    linarith
  calc
    s.vacuum.condensateMass * Real.exp ((1 : ℝ) / 3) =
        (s.vacuum.renormalizationMass *
          Real.exp s.vacuum.logRatio) *
          Real.exp ((1 : ℝ) / 3) := by
      rw [s.vacuum.condensateLaw]
    _ = s.vacuum.renormalizationMass *
        (Real.exp s.vacuum.logRatio *
          Real.exp ((1 : ℝ) / 3)) := by ring
    _ = s.vacuum.renormalizationMass *
        Real.exp (s.vacuum.logRatio + (1 : ℝ) / 3) := by
      rw [Real.exp_add]
    _ = s.vacuum.renormalizationMass *
        Real.exp s.transmutationLog := by
      rw [hLogAdd]
    _ = s.transmutationMass := s.transmutationMassLaw.symm

/--
The subtraction-scale independent final law is

`K * Lambda_RG * A = pi * exp(1/3)`.
-/
theorem rg_invariant_level_alpha_law
    (s : RGInvariantMCSAlpha) :
    s.mcsScale.levelMagnitude * s.transmutationMass *
        s.vacuum.alphaSquaredLength =
      Real.pi * Real.exp ((1 : ℝ) / 3) := by
  have hMCS := level_condensate_alpha_law s.mcsScale
  rw [s.sameCondensate, s.sameAlpha] at hMCS
  have hCondensate :=
    condensate_times_exp_third_eq_transmutation_mass s
  calc
    s.mcsScale.levelMagnitude * s.transmutationMass *
        s.vacuum.alphaSquaredLength =
      s.mcsScale.levelMagnitude *
        (s.vacuum.condensateMass * Real.exp ((1 : ℝ) / 3)) *
        s.vacuum.alphaSquaredLength := by
          rw [hCondensate]
    _ =
      (s.mcsScale.levelMagnitude * s.vacuum.condensateMass *
        s.vacuum.alphaSquaredLength) *
        Real.exp ((1 : ℝ) / 3) := by ring
    _ = Real.pi * Real.exp ((1 : ℝ) / 3) := by
      rw [hMCS]

/-- Primitive level `K=1` gives `Lambda_RG*A = pi*exp(1/3)`. -/
theorem unit_level_rg_invariant_alpha_law
    (s : RGInvariantMCSAlpha)
    (hUnit : s.mcsScale.levelMagnitude = 1) :
    s.transmutationMass * s.vacuum.alphaSquaredLength =
      Real.pi * Real.exp ((1 : ℝ) / 3) := by
  have hLaw := rg_invariant_level_alpha_law s
  rw [hUnit] at hLaw
  norm_num at hLaw ⊢
  exact hLaw

/--
The only continuous microscopic scale left in this one-log candidate is the RG
invariant `Lambda_RG`; `mu` and `lambda6` separately are subtraction-scheme
data.
-/
structure RGInvariantClosureStatus where
  leadingLogCoefficientComputed : Prop
  callanSymanzikEquationDerived : Prop
  transmutationMassSchemeIndependent : Prop
  compactLevelQuantized : Prop
  poleMassNormalizationDerived : Prop
  primitiveFluxLawDerived : Prop
  stableGlobalVacuumProvedBeyondTruncation : Prop
  absoluteAlphaDerived : Prop


def rgInvariantClosure (s : RGInvariantClosureStatus) : Prop :=
  s.leadingLogCoefficientComputed /\
  s.callanSymanzikEquationDerived /\
  s.transmutationMassSchemeIndependent /\
  s.compactLevelQuantized /\
  s.poleMassNormalizationDerived /\
  s.primitiveFluxLawDerived /\
  s.stableGlobalVacuumProvedBeyondTruncation /\
  s.absoluteAlphaDerived

end P0EFTJanusRGInvariantMCSAlpha
end JanusFormal
