import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonSquaredSpinorPairingNoGo4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCliffordSpin2DoubleCover

/-! # Rank-two Clifford SpinC Hermitian pairing

The natural product character kills the diagonal `(-1,-1)` and therefore
descends to the actual algebraic `CliffordSpinC2` quotient.  Its complex line
representation carries the canonical invariant Hermitian pairing.  This is
not yet a global Janus SpinC bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D

set_option autoImplicit false
noncomputable section

open Complex
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonSquaredSpinorPairingNoGo4D
open P0EFTJanusCliffordSpin2Bridge
open P0EFTJanusCliffordSpin2DoubleCover

variable (period : Real) (hPeriod : period ≠ 0)

/-- Product of the Clifford spin phase and determinant-line phase. -/
def cliffordSpin2PhaseSpinorCharacter :
    CliffordSpin2 × Circle →* Circle where
  toFun element := circleEquivCliffordSpin2.symm element.1 * element.2
  map_one' := by simp
  map_mul' first second := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

@[simp] theorem cliffordSpin2PhaseSpinorCharacter_diagonalMinusOne :
    cliffordSpin2PhaseSpinorCharacter cliffordSpin2DiagonalMinusOne = 1 := by
  simp [cliffordSpin2PhaseSpinorCharacter,
    cliffordSpin2DiagonalMinusOne, cliffordSpin2MinusOne]

private theorem cliffordSpin2DiagonalSubgroup_le_characterKernel :
    cliffordSpin2DiagonalSubgroup ≤
      cliffordSpin2PhaseSpinorCharacter.ker := by
  exact (Subgroup.closure_le _).2 (by
    simp [cliffordSpin2PhaseSpinorCharacter_diagonalMinusOne])

/-- Natural complex-line character of the diagonal Clifford SpinC quotient. -/
def cliffordSpinC2SpinorCharacter : CliffordSpinC2 →* Circle :=
  QuotientGroup.lift cliffordSpin2DiagonalSubgroup
    cliffordSpin2PhaseSpinorCharacter
    cliffordSpin2DiagonalSubgroup_le_characterKernel

@[simp] theorem cliffordSpinC2SpinorCharacter_mk
    (spin : CliffordSpin2) (phase : Circle) :
    cliffordSpinC2SpinorCharacter
        (QuotientGroup.mk' cliffordSpin2DiagonalSubgroup (spin, phase)) =
      circleEquivCliffordSpin2.symm spin * phase := by
  exact QuotientGroup.lift_mk' _ _ (spin, phase)

abbrev RankTwoSpinor := Complex

def rankTwoSpinCSpinorAction
    (element : CliffordSpinC2) (spinor : RankTwoSpinor) : RankTwoSpinor :=
  (cliffordSpinC2SpinorCharacter element : Complex) * spinor

def rankTwoSpinorHermitianPairing
    (first second : RankTwoSpinor) : Complex :=
  (starRingEnd Complex) first * second

/-- The descended Clifford SpinC character acts unitarily. -/
theorem rankTwoSpinorHermitianPairing_invariant
    (element : CliffordSpinC2) (first second : RankTwoSpinor) :
    rankTwoSpinorHermitianPairing
        (rankTwoSpinCSpinorAction element first)
        (rankTwoSpinCSpinorAction element second) =
      rankTwoSpinorHermitianPairing first second := by
  let phase := cliffordSpinC2SpinorCharacter element
  change (starRingEnd Complex) ((phase : Complex) * first) *
      ((phase : Complex) * second) =
    (starRingEnd Complex) first * second
  have hPhaseStar :
      (starRingEnd Complex) (phase : Complex) =
        ((phase⁻¹ : Circle) : Complex) :=
    (Circle.coe_inv_eq_conj phase).symm
  rw [map_mul, hPhaseStar]
  calc
    (((phase⁻¹ : Circle) : Complex) * (starRingEnd Complex) first) *
          ((phase : Complex) * second) =
        (((phase⁻¹ : Circle) : Complex) * (phase : Complex)) *
          ((starRingEnd Complex) first * second) := by ring
    _ = (starRingEnd Complex) first * second := by
      rw [← Circle.coe_mul]
      simp

/-- The canonical Hermitian pairing has no radical. -/
theorem rankTwoSpinorHermitianPairing_nondegenerate
    (spinor : RankTwoSpinor)
    (hRadical : ∀ test, rankTwoSpinorHermitianPairing spinor test = 0) :
    spinor = 0 := by
  have hSelf := hRadical spinor
  change (starRingEnd Complex) spinor * spinor = 0 at hSelf
  have hNormComplex : (Complex.normSq spinor : Complex) = 0 := by
    calc
      (Complex.normSq spinor : Complex) =
          (starRingEnd Complex) spinor * spinor :=
        Complex.normSq_eq_conj_mul_self
      _ = 0 := hSelf
  exact Complex.normSq_eq_zero.mp
    (Complex.ofReal_injective hNormComplex)

structure ProgramPRankTwoSpinCHermitianPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  commonFrontier :
    ProgramPCommonSquaredSpinorPairingFrontier4D period hPeriod domain
  hermitianInvariant :
    ∀ element first second,
      rankTwoSpinorHermitianPairing
          (rankTwoSpinCSpinorAction element first)
          (rankTwoSpinCSpinorAction element second) =
        rankTwoSpinorHermitianPairing first second
  hermitianNondegenerate :
    ∀ spinor,
      (∀ test, rankTwoSpinorHermitianPairing spinor test = 0) → spinor = 0

def programPRankTwoSpinCHermitianPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPRankTwoSpinCHermitianPairingCertificate4D period hPeriod domain where
  commonFrontier :=
    programPCommonSquaredSpinorPairingFrontier4D period hPeriod domain
  hermitianInvariant := rankTwoSpinorHermitianPairing_invariant
  hermitianNondegenerate := rankTwoSpinorHermitianPairing_nondegenerate

theorem canonicalProgramPRankTwoSpinCHermitianPairingCertificate4D_nonempty :
    Nonempty
      (ProgramPRankTwoSpinCHermitianPairingCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPRankTwoSpinCHermitianPairingCertificate4D period hPeriod _⟩

end
end P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D
end JanusFormal
