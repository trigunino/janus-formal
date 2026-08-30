import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-!
# T07 quantized PT families-index constraint

This checkpoint applies a supplied integral characteristic-number realization
of the local families-index curvature to the actual two outer Program-P
sectors.  Equal PT multiplicities cancel both the integral class and its
continuous Bismut--Freed representative.  Conversely, any nonzero
characteristic number forces the two multiplicities to agree.

This does not close T07: computing the characteristic numbers from the full
geometric field family and constructing an equivariant trivialization remain
separate obligations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT07QuantizedPTFamiliesIndexConstraint4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D

/-- A geometric families-index curvature together with its integral
characteristic-number evaluation. -/
structure QuantizedGeometricFamiliesIndexData4D
    (Base Tangent : Type*) where
  geometry : GeometricFamiliesIndexCurvatureData Base Tangent
  characteristicNumber : Base → Tangent → Tangent → ℤ
  localFamiliesIndex_eq_characteristic : ∀ base first second,
    geometry.localFamiliesIndexCurvature base first second =
      (characteristicNumber base first second : Complex)

/-- PT reverses the integral characteristic number on the negative sector. -/
def ptSectorCharacteristicNumber
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (sector : Sector) (base : Base) (first second : Tangent) : ℤ :=
  match sector with
  | .plus => data.characteristicNumber base first second
  | .minus => -data.characteristicNumber base first second

/-- Multiplicity-weighted characteristic number of the two physical sectors. -/
def totalPTCharacteristicNumber
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (multiplicity : Sector → ℕ)
    (base : Base) (first second : Tangent) : ℤ :=
  (multiplicity .plus : ℤ) *
      ptSectorCharacteristicNumber data .plus base first second +
    (multiplicity .minus : ℤ) *
      ptSectorCharacteristicNumber data .minus base first second

/-- Multiplicity-weighted continuous local families-index representative. -/
def totalPTLocalFamiliesIndexCurvature
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (multiplicity : Sector → ℕ)
    (base : Base) (first second : Tangent) : Complex :=
  (multiplicity .plus : Complex) *
      data.geometry.localFamiliesIndexCurvature base first second +
    (multiplicity .minus : Complex) *
      (-data.geometry.localFamiliesIndexCurvature base first second)

/-- The outer Program-P field packet contains one copy of each PT sector. -/
def programPOuterSectorMultiplicity (_sector : Sector) : ℕ := 1

@[simp] theorem programP_outer_characteristic_class_cancels
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (base : Base) (first second : Tangent) :
    totalPTCharacteristicNumber data programPOuterSectorMultiplicity
        base first second = 0 := by
  simp [totalPTCharacteristicNumber, ptSectorCharacteristicNumber,
    programPOuterSectorMultiplicity]

@[simp] theorem programP_outer_local_families_index_cancels
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (base : Base) (first second : Tangent) :
    totalPTLocalFamiliesIndexCurvature data programPOuterSectorMultiplicity
        base first second = 0 := by
  simp [totalPTLocalFamiliesIndexCurvature,
    programPOuterSectorMultiplicity]

/-- A nonzero integral characteristic number turns anomaly cancellation into
the discrete equality of the two sector multiplicities. -/
theorem characteristic_cancellation_iff_equal_multiplicity
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (multiplicity : Sector → ℕ)
    (base : Base) (first second : Tangent)
    (hNonzero : data.characteristicNumber base first second ≠ 0) :
    totalPTCharacteristicNumber data multiplicity base first second = 0 ↔
      multiplicity .plus = multiplicity .minus := by
  constructor
  · intro hCancel
    change
      (multiplicity .plus : ℤ) *
          data.characteristicNumber base first second +
        (multiplicity .minus : ℤ) *
          (-data.characteristicNumber base first second) = 0 at hCancel
    have hProduct :
        ((multiplicity .plus : ℤ) - (multiplicity .minus : ℤ)) *
            data.characteristicNumber base first second = 0 := by
      calc
        _ = (multiplicity .plus : ℤ) *
              data.characteristicNumber base first second +
            (multiplicity .minus : ℤ) *
              (-data.characteristicNumber base first second) := by ring
        _ = 0 := hCancel
    have hCast : (multiplicity .plus : ℤ) =
        (multiplicity .minus : ℤ) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hNonzero)
    exact_mod_cast hCast
  · intro hEqual
    simp [totalPTCharacteristicNumber, ptSectorCharacteristicNumber, hEqual]

/-- The same discrete constraint follows directly from the continuous
families-index curvature whenever its integral characteristic number is
nonzero. -/
theorem local_families_index_cancellation_iff_equal_multiplicity
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (multiplicity : Sector → ℕ)
    (base : Base) (first second : Tangent)
    (hNonzero : data.characteristicNumber base first second ≠ 0) :
    totalPTLocalFamiliesIndexCurvature data multiplicity base first second = 0 ↔
      multiplicity .plus = multiplicity .minus := by
  have hCurvature :
      data.geometry.localFamiliesIndexCurvature base first second ≠ 0 := by
    rw [data.localFamiliesIndex_eq_characteristic]
    exact_mod_cast hNonzero
  constructor
  · intro hCancel
    change
      (multiplicity .plus : Complex) *
          data.geometry.localFamiliesIndexCurvature base first second +
        (multiplicity .minus : Complex) *
          (-data.geometry.localFamiliesIndexCurvature base first second) = 0 at hCancel
    have hProduct :
        ((multiplicity .plus : Complex) -
            (multiplicity .minus : Complex)) *
          data.geometry.localFamiliesIndexCurvature base first second = 0 := by
      calc
        _ = (multiplicity .plus : Complex) *
              data.geometry.localFamiliesIndexCurvature base first second +
            (multiplicity .minus : Complex) *
              (-data.geometry.localFamiliesIndexCurvature base first second) := by ring
        _ = 0 := hCancel
    have hCast : (multiplicity .plus : Complex) =
        (multiplicity .minus : Complex) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hCurvature)
    exact_mod_cast hCast
  · intro hEqual
    simp [totalPTLocalFamiliesIndexCurvature, hEqual]

/-- Compiled T07 support certificate: the continuous and integral PT
cancellations agree on the physical outer packet, and every detected nonzero
characteristic number supplies an effective discrete constraint. -/
structure ProgramPT07QuantizedPTFamiliesIndexConstraintCertificate4D
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent) where
  familiesIndexCharacteristicMatch : ∀ base first second,
    data.geometry.localFamiliesIndexCurvature base first second =
      (data.characteristicNumber base first second : Complex)
  physicalIntegralCancellation : ∀ base first second,
    totalPTCharacteristicNumber data programPOuterSectorMultiplicity
        base first second = 0
  physicalContinuousCancellation : ∀ base first second,
    totalPTLocalFamiliesIndexCurvature data programPOuterSectorMultiplicity
        base first second = 0
  discreteConstraint : ∀ multiplicity base first second,
    data.characteristicNumber base first second ≠ 0 →
      (totalPTLocalFamiliesIndexCurvature data multiplicity base first second = 0 ↔
        multiplicity .plus = multiplicity .minus)

def programPT07QuantizedPTFamiliesIndexConstraintCertificate4D
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent) :
    ProgramPT07QuantizedPTFamiliesIndexConstraintCertificate4D data where
  familiesIndexCharacteristicMatch :=
    data.localFamiliesIndex_eq_characteristic
  physicalIntegralCancellation :=
    programP_outer_characteristic_class_cancels data
  physicalContinuousCancellation :=
    programP_outer_local_families_index_cancels data
  discreteConstraint :=
    local_families_index_cancellation_iff_equal_multiplicity data

/-- Public T07 support checkpoint. -/
theorem t07_quantized_pt_families_index_constraint_gate
    {Base Tangent : Type*}
    (data : QuantizedGeometricFamiliesIndexData4D Base Tangent) :
    Nonempty (ProgramPT07QuantizedPTFamiliesIndexConstraintCertificate4D data) :=
  ⟨programPT07QuantizedPTFamiliesIndexConstraintCertificate4D data⟩

end
end P0EFTJanusProgramPT07QuantizedPTFamiliesIndexConstraint4D
end JanusFormal
