import Mathlib

namespace JanusFormal
namespace P0EFTJanusBulkBoundaryChargeNormalization

set_option autoImplicit false

/--
A primitive orientation-preserving transgression computes the same physical
boundary charge from a bulk twisted-flux integer and from the LL auxiliary
flux integer.
-/
structure OrientationPreservingChargeTransgression where
  bulkFluxInteger : ℤ
  auxiliaryFluxInteger : ℤ
  bulkChargeUnit : ℝ
  auxiliaryChargeUnit : ℝ
  physicalBoundaryCharge : ℝ
  bulkIntegerAsRealNonzero : (bulkFluxInteger : ℝ) ≠ 0
  primitiveIntegerTransport : auxiliaryFluxInteger = bulkFluxInteger
  bulkChargeLaw :
    physicalBoundaryCharge =
      bulkChargeUnit * (bulkFluxInteger : ℝ)
  auxiliaryChargeLaw :
    physicalBoundaryCharge =
      auxiliaryChargeUnit * (auxiliaryFluxInteger : ℝ)

/-- Primitive orientation-preserving transgression transports the full unit. -/
theorem charge_units_are_equal
    (t : OrientationPreservingChargeTransgression) :
    t.bulkChargeUnit = t.auxiliaryChargeUnit := by
  have hCharge :
      t.bulkChargeUnit * (t.bulkFluxInteger : ℝ) =
        t.auxiliaryChargeUnit * (t.bulkFluxInteger : ℝ) := by
    calc
      t.bulkChargeUnit * (t.bulkFluxInteger : ℝ) =
          t.physicalBoundaryCharge := t.bulkChargeLaw.symm
      _ = t.auxiliaryChargeUnit *
          (t.auxiliaryFluxInteger : ℝ) := t.auxiliaryChargeLaw
      _ = t.auxiliaryChargeUnit *
          (t.bulkFluxInteger : ℝ) := by
        rw [t.primitiveIntegerTransport]
  have hFactor :
      (t.bulkChargeUnit - t.auxiliaryChargeUnit) *
        (t.bulkFluxInteger : ℝ) = 0 := by
    nlinarith [hCharge]
  have hDifference :
      t.bulkChargeUnit - t.auxiliaryChargeUnit = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right t.bulkIntegerAsRealNonzero
  linarith

/--
An orientation-reversing primitive transgression changes the integer sign.
-/
structure OrientationReversingChargeTransgression where
  bulkFluxInteger : ℤ
  auxiliaryFluxInteger : ℤ
  bulkChargeUnit : ℝ
  auxiliaryChargeUnit : ℝ
  physicalBoundaryCharge : ℝ
  bulkIntegerAsRealNonzero : (bulkFluxInteger : ℝ) ≠ 0
  primitiveIntegerTransport : auxiliaryFluxInteger = -bulkFluxInteger
  bulkChargeLaw :
    physicalBoundaryCharge =
      bulkChargeUnit * (bulkFluxInteger : ℝ)
  auxiliaryChargeLaw :
    physicalBoundaryCharge =
      auxiliaryChargeUnit * (auxiliaryFluxInteger : ℝ)

/-- Orientation reversal transports the unit with one sign reversal. -/
theorem reversing_transgression_flips_charge_unit
    (t : OrientationReversingChargeTransgression) :
    t.bulkChargeUnit = -t.auxiliaryChargeUnit := by
  have hCharge :
      t.bulkChargeUnit * (t.bulkFluxInteger : ℝ) =
        (-t.auxiliaryChargeUnit) * (t.bulkFluxInteger : ℝ) := by
    calc
      t.bulkChargeUnit * (t.bulkFluxInteger : ℝ) =
          t.physicalBoundaryCharge := t.bulkChargeLaw.symm
      _ = t.auxiliaryChargeUnit *
          (t.auxiliaryFluxInteger : ℝ) := t.auxiliaryChargeLaw
      _ = t.auxiliaryChargeUnit *
          ((-t.bulkFluxInteger : ℤ) : ℝ) := by
        rw [t.primitiveIntegerTransport]
      _ = (-t.auxiliaryChargeUnit) *
          (t.bulkFluxInteger : ℝ) := by
        norm_num
  have hFactor :
      (t.bulkChargeUnit - (-t.auxiliaryChargeUnit)) *
        (t.bulkFluxInteger : ℝ) = 0 := by
    nlinarith [hCharge]
  have hDifference :
      t.bulkChargeUnit - (-t.auxiliaryChargeUnit) = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right t.bulkIntegerAsRealNonzero
  linarith

/-- Orientation reversal preserves the magnitude of the charge unit. -/
theorem reversing_transgression_preserves_charge_magnitude
    (t : OrientationReversingChargeTransgression) :
    |t.bulkChargeUnit| = |t.auxiliaryChargeUnit| := by
  rw [reversing_transgression_flips_charge_unit t, abs_neg]

/-- Equality of quantized physical charges. -/
def ChargeCompatibility
    (bulkUnit auxiliaryUnit bulkInteger auxiliaryInteger : ℝ) : Prop :=
  bulkUnit * bulkInteger = auxiliaryUnit * auxiliaryInteger

/-- Common rescaling of both charge units preserves the commuting diagram. -/
theorem common_unit_rescaling_preserves_compatibility
    (bulkUnit auxiliaryUnit bulkInteger auxiliaryInteger scale : ℝ)
    (hCompatibility :
      ChargeCompatibility bulkUnit auxiliaryUnit
        bulkInteger auxiliaryInteger) :
    ChargeCompatibility (scale * bulkUnit) (scale * auxiliaryUnit)
      bulkInteger auxiliaryInteger := by
  unfold ChargeCompatibility at hCompatibility ⊢
  calc
    (scale * bulkUnit) * bulkInteger =
        scale * (bulkUnit * bulkInteger) := by ring
    _ = scale * (auxiliaryUnit * auxiliaryInteger) := by
      rw [hCompatibility]
    _ = (scale * auxiliaryUnit) * auxiliaryInteger := by ring

/--
The transgression transports a dimensionful normalization but cannot generate
it: a separate microscopic law must break the common rescaling orbit.
-/
structure AbsoluteNormalizationClosureStatus where
  relativeBulkClassDerived : Prop
  boundaryMapDerived : Prop
  primitiveTransgressionDerived : Prop
  largeGaugePeriodsMatched : Prop
  chargeUnitTransportProved : Prop
  independentDimensionfulUnitDerived : Prop
  commonRescalingOrbitBroken : Prop
  absoluteLLChargeNormalized : Prop


def absoluteNormalizationClosed
    (s : AbsoluteNormalizationClosureStatus) : Prop :=
  s.relativeBulkClassDerived /\
  s.boundaryMapDerived /\
  s.primitiveTransgressionDerived /\
  s.largeGaugePeriodsMatched /\
  s.chargeUnitTransportProved /\
  s.independentDimensionfulUnitDerived /\
  s.commonRescalingOrbitBroken /\
  s.absoluteLLChargeNormalized

end P0EFTJanusBulkBoundaryChargeNormalization
end JanusFormal
