import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D

/-! # Ambient PinC bundle twisted by a circle Cech cocycle

An ambient `U(1)` cocycle on the canonical Janus cover combines with the
actual `Pin⁻(4)` cocycle to give a `PinC(4)` cocycle.  Its determinant is
exactly the square of the circle transition.  Thus the remaining geometric
input is isolated as an actual nontrivial ambient circle cocycle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCTwistedCechBundle4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusEuclideanGlobalSpinCJetRealization
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Circle transition data on exactly the canonical ambient Janus cover. -/
structure AmbientCircleCechTwist where
  transition : AmbientCover period hPeriod → AmbientCover period hPeriod →
    AmbientBase period hPeriod → Circle
  transition_self : ∀ index base,
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain index →
      transition index index base = 1
  transition_inverse : ∀ first second base,
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain first →
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain second →
      transition first second base * transition second first base = 1
  transition_cocycle : ∀ first second third base,
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain first →
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain second →
    base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain third →
      transition first second base * transition second third base =
        transition first third base

/-- The circle cocycle viewed as a principal Cech bundle presentation. -/
def AmbientCircleCechTwist.toCechPrincipalBundleData
    (twist : AmbientCircleCechTwist period hPeriod) :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) Circle where
  domain := (canonicalAmbientPinMinusCechBundle period hPeriod).domain
  domain_isOpen :=
    (canonicalAmbientPinMinusCechBundle period hPeriod).domain_isOpen
  cover := (canonicalAmbientPinMinusCechBundle period hPeriod).cover
  transition := twist.transition
  transition_self := twist.transition_self
  transition_inverse := twist.transition_inverse
  transition_cocycle := twist.transition_cocycle

/-- The trivial phase sector on the canonical ambient cover. -/
def trivialAmbientCircleCechTwist :
    AmbientCircleCechTwist period hPeriod where
  transition := fun _ _ _ => 1
  transition_self := by simp
  transition_inverse := by simp
  transition_cocycle := by simp

/-- Combine the canonical Pin-minus cocycle with an ambient circle twist. -/
def canonicalAmbientTwistedPinCCechBundle
    (twist : AmbientCircleCechTwist period hPeriod) :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientPinC4 := by
  let pinBundle := canonicalAmbientPinMinusCechBundle period hPeriod
  exact {
    domain := pinBundle.domain
    domain_isOpen := pinBundle.domain_isOpen
    cover := pinBundle.cover
    transition := fun first second base =>
      QuotientGroup.mk' ambientPinCDiagonalSubgroup
        (pinBundle.transition first second base,
          twist.transition first second base)
    transition_self := by
      intro index base hBase
      rw [pinBundle.transition_self index base hBase,
        twist.transition_self index base hBase]
      exact map_one (QuotientGroup.mk' ambientPinCDiagonalSubgroup)
    transition_inverse := by
      intro first second base hFirst hSecond
      rw [← map_mul]
      change QuotientGroup.mk' ambientPinCDiagonalSubgroup
        (pinBundle.transition first second base *
            pinBundle.transition second first base,
          twist.transition first second base *
            twist.transition second first base) = 1
      rw [pinBundle.transition_inverse first second base hFirst hSecond,
        twist.transition_inverse first second base hFirst hSecond]
      exact map_one (QuotientGroup.mk' ambientPinCDiagonalSubgroup)
    transition_cocycle := by
      intro first second third base hFirst hSecond hThird
      rw [← map_mul]
      change QuotientGroup.mk' ambientPinCDiagonalSubgroup
        (pinBundle.transition first second base *
            pinBundle.transition second third base,
          twist.transition first second base *
            twist.transition second third base) = _
      rw [pinBundle.transition_cocycle first second third base
          hFirst hSecond hThird,
        twist.transition_cocycle first second third base
          hFirst hSecond hThird]
  }

/-- The determinant transition of the twisted bundle is the squared phase. -/
theorem canonicalAmbientTwistedPinCCechBundle_determinantTransition
    (twist : AmbientCircleCechTwist period hPeriod)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    ambientPinCDeterminantCharacter
        ((canonicalAmbientTwistedPinCCechBundle period hPeriod twist).transition
          first second base) =
      twist.transition first second base ^ 2 := by
  apply ambientPinCDeterminantCharacter_mk

/-- The trivial twist recovers the canonical PinC transition. -/
theorem canonicalAmbientTwistedPinCCechBundle_trivial_transition
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    (canonicalAmbientTwistedPinCCechBundle period hPeriod
        (trivialAmbientCircleCechTwist period hPeriod)).transition
        first second base =
      (canonicalAmbientPinCCechBundle period hPeriod).transition
        first second base := by
  rfl

structure ProgramPAmbientPinCTwistedCechBundleCertificate4D where
  twist : AmbientCircleCechTwist period hPeriod
  pinCBundle : CechPrincipalBundleData (AmbientBase period hPeriod)
    (AmbientCover period hPeriod) AmbientPinC4
  pinCBundleCanonical :
    pinCBundle = canonicalAmbientTwistedPinCCechBundle period hPeriod twist
  determinantLaw : ∀ first second base,
    ambientPinCDeterminantCharacter
        (pinCBundle.transition first second base) =
      twist.transition first second base ^ 2

def programPAmbientPinCTwistedCechBundleCertificate4D
    (twist : AmbientCircleCechTwist period hPeriod) :
    ProgramPAmbientPinCTwistedCechBundleCertificate4D period hPeriod where
  twist := twist
  pinCBundle := canonicalAmbientTwistedPinCCechBundle period hPeriod twist
  pinCBundleCanonical := rfl
  determinantLaw :=
    canonicalAmbientTwistedPinCCechBundle_determinantTransition
      period hPeriod twist

theorem programPAmbientPinCTwistedCechBundleCertificate4D_nonempty
    (twist : AmbientCircleCechTwist period hPeriod) :
    Nonempty (ProgramPAmbientPinCTwistedCechBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientPinCTwistedCechBundleCertificate4D
    period hPeriod twist⟩

end
end P0EFTJanusProgramPAmbientPinCTwistedCechBundle4D
end JanusFormal
