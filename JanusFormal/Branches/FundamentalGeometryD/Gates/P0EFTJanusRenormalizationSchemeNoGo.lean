import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusHeatKernelCountertermScheme

namespace JanusFormal
namespace P0EFTJanusRenormalizationSchemeNoGo

set_option autoImplicit false

open P0EFTJanusHeatKernelCountertermScheme

/-- The same physical target cannot be stationary for two different finite local coefficients. -/
theorem same_target_stationary_implies_same_finite_coefficient
    (firstCoefficient secondCoefficient nonlocalWeight targetExponent : ℝ)
    (hTarget : targetExponent + 1 ≠ 0)
    (hFirst :
      QuarterCountertermStationarity firstCoefficient
        nonlocalWeight targetExponent)
    (hSecond :
      QuarterCountertermStationarity secondCoefficient
        nonlocalWeight targetExponent) :
    firstCoefficient = secondCoefficient := by
  unfold QuarterCountertermStationarity at hFirst hSecond
  have hFactor :
      (firstCoefficient - secondCoefficient) *
        (targetExponent + 1) = 0 := by
    nlinarith [hFirst, hSecond]
  have hDifference : firstCoefficient - secondCoefficient = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right hTarget
  linarith

/-- Any nonzero finite counterterm shift destroys stationarity at the old target. -/
theorem nonzero_finite_shift_moves_stationary_target
    (localCoefficient shift nonlocalWeight targetExponent : ℝ)
    (hTarget : targetExponent + 1 ≠ 0)
    (hStationary :
      QuarterCountertermStationarity localCoefficient
        nonlocalWeight targetExponent)
    (hShift : shift ≠ 0) :
    Not (
      QuarterCountertermStationarity (localCoefficient + shift)
        nonlocalWeight targetExponent) := by
  intro hShifted
  have hEqual := same_target_stationary_implies_same_finite_coefficient
    localCoefficient (localCoefficient + shift)
    nonlocalWeight targetExponent hTarget hStationary hShifted
  apply hShift
  linarith

/-- Two schemes related by a finite local shift. -/
structure FiniteSchemePair where
  firstCoefficient : ℝ
  secondCoefficient : ℝ
  shift : ℝ
  shiftLaw : secondCoefficient = firstCoefficient + shift

/-- A scheme-independent stationary target requires the finite shift to vanish. -/
theorem scheme_independent_target_forces_zero_shift
    (s : FiniteSchemePair)
    (nonlocalWeight targetExponent : ℝ)
    (hTarget : targetExponent + 1 ≠ 0)
    (hFirst :
      QuarterCountertermStationarity s.firstCoefficient
        nonlocalWeight targetExponent)
    (hSecond :
      QuarterCountertermStationarity s.secondCoefficient
        nonlocalWeight targetExponent) :
    s.shift = 0 := by
  have hCoefficients :=
    same_target_stationary_implies_same_finite_coefficient
      s.firstCoefficient s.secondCoefficient
      nonlocalWeight targetExponent hTarget hFirst hSecond
  rw [s.shiftLaw] at hCoefficients
  linarith

/--
A physical modulus can be called scheme independent only after the allowed
finite counterterm ambiguity is removed.  Otherwise changing renormalization
scheme moves the stationary point continuously.
-/
structure SchemeIndependentModulusStatus where
  divergentSubtractionFixed : Prop
  allowedFiniteShiftsClassified : Prop
  allAllowedFiniteShiftsVanish : Prop
  microscopicMatchingConditionDerived : Prop
  targetIndependentRenormalizationConditionDerived : Prop
  stationaryModulusSchemeIndependent : Prop


def schemeIndependentModulusClosed
    (s : SchemeIndependentModulusStatus) : Prop :=
  s.divergentSubtractionFixed /\
  s.allowedFiniteShiftsClassified /\
  s.allAllowedFiniteShiftsVanish /\
  s.microscopicMatchingConditionDerived /\
  s.targetIndependentRenormalizationConditionDerived /\
  s.stationaryModulusSchemeIndependent

end P0EFTJanusRenormalizationSchemeNoGo
end JanusFormal
