import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGImprovedSexticVacuum

namespace JanusFormal
namespace P0EFTJanusChernSimonsCriticalAlpha

set_option autoImplicit false

open P0EFTJanusRGImprovedSexticVacuum

/--
Large-N `U(N)_kappa` Chern--Simons scalar critical data.

The paper arXiv:1402.4196 finds the massive flat-direction phase at

`lambda^2 + lambda6/(8*pi^2) = 4`,

where `lambda = N/kappa`.  We store the equivalent cleared relation.
-/
structure ChernSimonsCriticalLine where
  rank : ℕ
  level : ℕ
  tHooftCoupling : ℝ
  sexticCoupling : ℝ
  rankPositive : 0 < rank
  levelPositive : 0 < level
  tHooftLaw :
    (level : ℝ) * tHooftCoupling = (rank : ℝ)
  criticalLineCleared :
    8 * Real.pi ^ 2 * tHooftCoupling ^ 2 + sexticCoupling =
      32 * Real.pi ^ 2

/-- The critical sextic coupling is fixed by the discrete 't Hooft ratio. -/
theorem sextic_coupling_from_tHooft
    (c : ChernSimonsCriticalLine) :
    c.sexticCoupling =
      8 * Real.pi ^ 2 * (4 - c.tHooftCoupling ^ 2) := by
  nlinarith [c.criticalLineCleared]

/-- Positive subcritical 't Hooft magnitude gives a positive sextic coupling. -/
theorem sextic_coupling_positive
    (c : ChernSimonsCriticalLine)
    (hSubcritical : c.tHooftCoupling ^ 2 < 4) :
    0 < c.sexticCoupling := by
  rw [sextic_coupling_from_tHooft c]
  have hPiSquare : 0 < Real.pi ^ 2 :=
    pow_pos Real.pi_pos 2
  exact mul_pos
    (mul_pos (by norm_num) hPiSquare)
    (sub_pos.mpr hSubcritical)

/--
Finite-N lifting of the large-N flat direction.  `vacuum` supplies a positive
one-log coefficient and the LL charge normalization.
-/
structure CriticalLineAlphaVacuum where
  critical : ChernSimonsCriticalLine
  vacuum : OneLogAlphaVacuum
  sexticIdentification :
    vacuum.sexticCoupling = critical.sexticCoupling

/-- The stationary exponent is completely constrained by `lambda`, `b`. -/
theorem critical_stationary_exponent_equation
    (s : CriticalLineAlphaVacuum) :
    3 * s.vacuum.logCoefficient * (-s.vacuum.logRatio) =
      24 * Real.pi ^ 2 *
        (4 - s.critical.tHooftCoupling ^ 2) +
      s.vacuum.logCoefficient := by
  have hStationary := stationary_log_equation
    s.vacuum.toOneLogCompositeVacuum
  have hSextic := sextic_coupling_from_tHooft s.critical
  rw [s.sexticIdentification, hSextic] at hStationary
  nlinarith

/-- Positive logarithmic coefficient and positive critical sextic give hierarchy exponent > 0. -/
theorem hierarchy_exponent_positive
    (s : CriticalLineAlphaVacuum)
    (hSubcritical : s.critical.tHooftCoupling ^ 2 < 4) :
    0 < -s.vacuum.logRatio := by
  have hSexticPositive := sextic_coupling_positive s.critical hSubcritical
  have hSexticVacuum : 0 < s.vacuum.sexticCoupling := by
    rw [s.sexticIdentification]
    exact hSexticPositive
  have hStationary := stationary_log_equation
    s.vacuum.toOneLogCompositeVacuum
  have hNumerator :
      0 < 3 * s.vacuum.sexticCoupling +
        s.vacuum.logCoefficient := by
    nlinarith [hSexticVacuum, s.vacuum.logCoefficientPositive]
  have hProduct :
      0 < 3 * s.vacuum.logCoefficient * (-s.vacuum.logRatio) := by
    nlinarith [hStationary, hNumerator]
  have hCoefficient : 0 < 3 * s.vacuum.logCoefficient := by
    nlinarith [s.vacuum.logCoefficientPositive]
  exact pos_of_mul_pos_right hProduct (le_of_lt hCoefficient)

/--
The microscopic formula in exponential form:

`2*a_q*mu*A = exp(H)`, where `H = -logRatio`.
-/
theorem critical_alpha_exponential_law
    (s : CriticalLineAlphaVacuum) :
    2 * s.vacuum.chargeAmplitude *
        s.vacuum.renormalizationMass *
        s.vacuum.alphaSquaredLength =
      Real.exp (-s.vacuum.logRatio) := by
  have hMicroscopic := microscopic_alpha_equation s.vacuum
  have hProduct :
      (2 * s.vacuum.chargeAmplitude *
          s.vacuum.renormalizationMass *
          s.vacuum.alphaSquaredLength) *
        Real.exp s.vacuum.logRatio = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hMicroscopic
  calc
    2 * s.vacuum.chargeAmplitude *
        s.vacuum.renormalizationMass *
        s.vacuum.alphaSquaredLength =
      (2 * s.vacuum.chargeAmplitude *
          s.vacuum.renormalizationMass *
          s.vacuum.alphaSquaredLength) *
        (Real.exp s.vacuum.logRatio *
          Real.exp (-s.vacuum.logRatio)) := by
        rw [← Real.exp_add]
        simp
    _ =
      ((2 * s.vacuum.chargeAmplitude *
          s.vacuum.renormalizationMass *
          s.vacuum.alphaSquaredLength) *
        Real.exp s.vacuum.logRatio) *
          Real.exp (-s.vacuum.logRatio) := by ring
    _ = Real.exp (-s.vacuum.logRatio) := by
      rw [hProduct]
      ring

/--
Discrete and quantum data required for a no-fit prediction.  The critical-line
relation removes `lambda6` as a free coupling; finite-N dynamics must still
compute the positive logarithmic coefficient and the subtraction/UV anchor.
-/
structure CriticalPredictionStatus where
  rankAndLevelSelectedByTopology : Prop
  parityAnomalyCancelled : Prop
  criticalLineDerived : Prop
  finiteNLogCoefficientComputed : Prop
  uvMassAnchorDerived : Prop
  chargeAmplitudeComputed : Prop
  stableVacuumProved : Prop
  noObservedScaleImported : Prop
  alphaPredicted : Prop


def criticalPredictionClosed (s : CriticalPredictionStatus) : Prop :=
  s.rankAndLevelSelectedByTopology /\
  s.parityAnomalyCancelled /\
  s.criticalLineDerived /\
  s.finiteNLogCoefficientComputed /\
  s.uvMassAnchorDerived /\
  s.chargeAmplitudeComputed /\
  s.stableVacuumProved /\
  s.noObservedScaleImported /\
  s.alphaPredicted

end P0EFTJanusChernSimonsCriticalAlpha
end JanusFormal
