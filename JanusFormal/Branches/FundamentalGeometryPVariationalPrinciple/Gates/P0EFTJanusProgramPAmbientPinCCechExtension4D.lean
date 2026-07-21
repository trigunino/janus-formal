import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanGlobalSpinCJetRealization

/-! # Algebraic ambient PinC extension of the canonical Pin-minus bundle

The canonical multi-chart `Pin⁻(4)` cocycle is pushed through the diagonal
quotient `(Pin⁻(4) × U(1)) / ⟨(-1,-1)⟩`.  This constructs the algebraic Cech
`PinC(4)` bundle; a full spinor representation remains separate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCCechExtension4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusEuclideanGlobalSpinCJetRealization

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)

def ambientPinCDiagonalMinusOne :
    AmbientCoordinatePinMinusGroup × Circle :=
  (ambientPinMinusCentralSign, -1)

/-- Normal subgroup imposing the simultaneous Pin and circle sign relation. -/
def ambientPinCDiagonalSubgroup :
    Subgroup (AmbientCoordinatePinMinusGroup × Circle) :=
  Subgroup.normalClosure {ambientPinCDiagonalMinusOne}

instance ambientPinCDiagonalSubgroup_normal :
    ambientPinCDiagonalSubgroup.Normal := by
  change (Subgroup.normalClosure {ambientPinCDiagonalMinusOne}).Normal
  infer_instance

/-- Concrete algebraic ambient `PinC(4)` group. -/
abbrev AmbientPinC4 :=
  (AmbientCoordinatePinMinusGroup × Circle) ⧸ ambientPinCDiagonalSubgroup

def ambientPinMinusUnitPhase :
    AmbientCoordinatePinMinusGroup →* AmbientCoordinatePinMinusGroup × Circle where
  toFun pin := (pin, 1)
  map_one' := by simp
  map_mul' first second := by simp

/-- Canonical inclusion of `Pin⁻(4)` into the diagonal PinC quotient. -/
def ambientPinMinusToPinC : AmbientCoordinatePinMinusGroup →* AmbientPinC4 :=
  (QuotientGroup.mk' ambientPinCDiagonalSubgroup).comp ambientPinMinusUnitPhase

theorem ambientPinCDiagonalMinusOne_killed :
    QuotientGroup.mk' ambientPinCDiagonalSubgroup
        ambientPinCDiagonalMinusOne = 1 := by
  apply (QuotientGroup.eq_one_iff ambientPinCDiagonalMinusOne).2
  exact Subgroup.subset_normalClosure
    (show ambientPinCDiagonalMinusOne ∈ {ambientPinCDiagonalMinusOne} by simp)

/-- Cech presentation extracted from the genuine canonical principal core.
Indices are reversed to match the transition convention of
`CechPrincipalBundleData`. -/
def canonicalAmbientPinMinusCechBundle :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientCoordinatePinMinusGroup := by
  let core := canonicalAmbientPinMinusPrincipalBundleCore period hPeriod
  exact {
    domain := core.baseSet
    domain_isOpen := core.isOpen_baseSet
    cover := fun base => ⟨core.indexAt base, core.mem_baseSet_at base⟩
    transition := fun first second base =>
      core.coordChange second first base 1
    transition_self := by
      intro index base hBase
      exact core.coordChange_self index base hBase 1
    transition_inverse := by
      intro first second base hFirst hSecond
      have hComp := core.coordChange_comp first second first base
        ⟨⟨hFirst, hSecond⟩, hFirst⟩ 1
      rw [core.coordChange_self first base hFirst 1] at hComp
      simpa [core, canonicalAmbientPinMinusPrincipalBundleCore,
        canonicalAmbientPinMinusPrincipalCoordChange] using hComp
    transition_cocycle := by
      intro first second third base hFirst hSecond hThird
      have hComp := core.coordChange_comp third second first base
        ⟨⟨hThird, hSecond⟩, hFirst⟩ 1
      simpa [core, canonicalAmbientPinMinusPrincipalBundleCore,
        canonicalAmbientPinMinusPrincipalCoordChange] using hComp
  }

/-- Push-forward of the actual ambient Pin-minus cocycle to `PinC(4)`. -/
def canonicalAmbientPinCCechBundle :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientPinC4 := by
  let pinBundle := canonicalAmbientPinMinusCechBundle period hPeriod
  exact {
    domain := pinBundle.domain
    domain_isOpen := pinBundle.domain_isOpen
    cover := pinBundle.cover
    transition := fun first second base =>
      ambientPinMinusToPinC (pinBundle.transition first second base)
    transition_self := by
      intro index base hBase
      rw [pinBundle.transition_self index base hBase, map_one]
    transition_inverse := by
      intro first second base hFirst hSecond
      rw [← map_mul,
        pinBundle.transition_inverse first second base hFirst hSecond, map_one]
    transition_cocycle := by
      intro first second third base hFirst hSecond hThird
      rw [← map_mul,
        pinBundle.transition_cocycle first second third base
          hFirst hSecond hThird]
  }

theorem canonicalAmbientPinCCechTransition_is_pushforward
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    (canonicalAmbientPinCCechBundle period hPeriod).transition
        first second base =
      ambientPinMinusToPinC
        ((canonicalAmbientPinMinusCechBundle period hPeriod).transition
          first second base) :=
  rfl

structure ProgramPAmbientPinCCechExtensionCertificate4D where
  pinMinusBundle :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientCoordinatePinMinusGroup
  pinMinusBundleCanonical :
    pinMinusBundle = canonicalAmbientPinMinusCechBundle period hPeriod
  pinCBundle :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientPinC4
  pinCBundleCanonical :
    pinCBundle = canonicalAmbientPinCCechBundle period hPeriod
  transitionPushforward :
    ∀ first second base,
      pinCBundle.transition first second base =
        ambientPinMinusToPinC (pinMinusBundle.transition first second base)

def programPAmbientPinCCechExtensionCertificate4D :
    ProgramPAmbientPinCCechExtensionCertificate4D period hPeriod where
  pinMinusBundle := canonicalAmbientPinMinusCechBundle period hPeriod
  pinMinusBundleCanonical := rfl
  pinCBundle := canonicalAmbientPinCCechBundle period hPeriod
  pinCBundleCanonical := rfl
  transitionPushforward :=
    canonicalAmbientPinCCechTransition_is_pushforward period hPeriod

theorem programPAmbientPinCCechExtensionCertificate4D_nonempty :
    Nonempty (ProgramPAmbientPinCCechExtensionCertificate4D period hPeriod) :=
  ⟨programPAmbientPinCCechExtensionCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPAmbientPinCCechExtension4D
end JanusFormal
