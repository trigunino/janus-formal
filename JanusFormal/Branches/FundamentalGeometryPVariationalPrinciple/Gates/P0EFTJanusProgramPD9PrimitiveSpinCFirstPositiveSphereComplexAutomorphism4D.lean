import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Dirac automorphism on the geometric complex first-sphere packet

The simultaneous complex synthesis need not yet be known injective in order
to control the actual operator on its geometric range.  The exact identity

`D² = (k² + 2) id`

holds on that range, and the scalar is strictly positive.  Consequently the
restriction of the genuine differential Dirac operator is a linear
automorphism with inverse `(k² + 2)⁻¹ D`.

This is an operator theorem on actual smooth sections, not merely a statement
about the abstract coefficient diagonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Positive squared frequency of the first spherical geometric packet. -/
def primitiveSpinCHopfFirstSphereSquaredFrequency
    (sector : NormalRootChoice) (mode : Int) : Real :=
  normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2

/-- The first-sphere squared frequency is strictly positive for every root
sector, circle label and nonzero period. -/
theorem primitiveSpinCHopfFirstSphereSquaredFrequency_pos
    (sector : NormalRootChoice) (mode : Int) :
    0 < primitiveSpinCHopfFirstSphereSquaredFrequency
      period sector mode := by
  unfold primitiveSpinCHopfFirstSphereSquaredFrequency
  positivity

/-- Hence the first-sphere squared frequency never vanishes. -/
theorem primitiveSpinCHopfFirstSphereSquaredFrequency_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereSquaredFrequency
        period sector mode ≠ 0 :=
  ne_of_gt
    (primitiveSpinCHopfFirstSphereSquaredFrequency_pos
      period sector mode)

/-- On the actual geometric range, the square of the restricted differential
Dirac operator is the positive squared frequency times the identity. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDirac_sq
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode state) =
      primitiveSpinCHopfFirstSphereSquaredFrequency
          period sector mode • state := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  apply Subtype.ext
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state.1) =
      primitiveSpinCHopfFirstSphereSquaredFrequency
          period sector mode • state.1
  rw [← hCoefficients,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac_sq]
  change
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSquaredFrequency
          period sector mode • coefficients) =
      primitiveSpinCHopfFirstSphereSquaredFrequency
        period sector mode •
          primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients
  exact map_smul
    (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
      period hPeriod sector mode)
    (primitiveSpinCHopfFirstSphereSquaredFrequency period sector mode)
    coefficients

/-- Explicit inverse candidate on the actual geometric range. -/
def primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode →ₗ[Real]
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode :=
  (primitiveSpinCHopfFirstSphereSquaredFrequency
      period sector mode)⁻¹ •
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
      period hPeriod sector mode

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_apply
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse
        period hPeriod sector mode state =
      (primitiveSpinCHopfFirstSphereSquaredFrequency
        period sector mode)⁻¹ •
        primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode state :=
  rfl

/-- The explicit inverse is a left inverse of the actual restricted Dirac
operator. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_left
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode state) =
      state := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_apply,
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac_sq,
    ← mul_smul]
  simp [primitiveSpinCHopfFirstSphereSquaredFrequency_ne_zero
    period sector mode]

/-- The same explicit inverse is a right inverse of the actual restricted
Dirac operator. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_right
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse
          period hPeriod sector mode state) =
      state := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_apply,
    map_smul,
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac_sq,
    ← mul_smul]
  simp [primitiveSpinCHopfFirstSphereSquaredFrequency_ne_zero
    period sector mode]

/-- Exact linear equivalence induced by the genuine differential Dirac
operator on the complex first-sphere geometric range. -/
def primitiveSpinCHopfFirstSphereSignedComplexActualDiracLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode ≃ₗ[Real]
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode where
  toLinearMap :=
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
      period hPeriod sector mode
  invFun :=
    primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse
      period hPeriod sector mode
  left_inv :=
    primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_left
      period hPeriod sector mode
  right_inv :=
    primitiveSpinCHopfFirstSphereSignedComplexActualDiracInverse_right
      period hPeriod sector mode

/-- The actual geometric Dirac restriction is bijective. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDirac_bijective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Bijective
      (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
        period hPeriod sector mode) :=
  (primitiveSpinCHopfFirstSphereSignedComplexActualDiracLinearEquiv
    period hPeriod sector mode).bijective

/-- In particular there is no geometric zero mode inside the complex first
sphere packet. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDirac_ker_eq_bot
    (sector : NormalRootChoice) (mode : Int) :
    LinearMap.ker
        (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (primitiveSpinCHopfFirstSphereSignedComplexActualDirac_bijective
      period hPeriod sector mode).1

/-- Consolidated operator-level closure of the complex first-sphere block. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDiracAutomorphism_closed
    (sector : NormalRootChoice) (mode : Int) :
    (∀ state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode,
      primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode
          (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
            period hPeriod sector mode state) =
        primitiveSpinCHopfFirstSphereSquaredFrequency
          period sector mode • state) ∧
      Function.Bijective
        (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode) ∧
      LinearMap.ker
          (primitiveSpinCHopfFirstSphereSignedComplexActualDirac
            period hPeriod sector mode) = ⊥ :=
  ⟨primitiveSpinCHopfFirstSphereSignedComplexActualDirac_sq
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac_bijective
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac_ker_eq_bot
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D
end JanusFormal
