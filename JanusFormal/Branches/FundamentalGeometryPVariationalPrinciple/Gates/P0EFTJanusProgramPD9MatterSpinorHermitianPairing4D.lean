import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D

/-! # Hermitian pairing on the actual D9-rank spinor bundle

The ambient Dirac pairing restricts to the invariant rank-two block and is
then transported through the canonical real-linear equivalence with the D9
matter fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

def ambientHalfSpinorHermitianPairing
    (first second : AmbientHalfSpinor2) : Complex :=
  ambientPinCSpinorHermitianPairing
    (ambientHalfSpinorEmbed first) (ambientHalfSpinorEmbed second)

theorem canonicalAmbientPinCHalfSpinorCoordChange_preserves_pairing
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (left right : AmbientHalfSpinor2) :
    ambientHalfSpinorHermitianPairing
        (canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
          first second base left)
        (canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
          first second base right) =
      ambientHalfSpinorHermitianPairing left right := by
  have hFull := canonicalAmbientPinCSpinorCoordChange_preserves_pairing
    period hPeriod choice first second base
      (ambientHalfSpinorEmbed left) (ambientHalfSpinorEmbed right)
  rw [canonicalAmbientPinCSpinorCoordChange_preserves_halfSpinor,
    canonicalAmbientPinCSpinorCoordChange_preserves_halfSpinor] at hFull
  exact hFull

theorem ambientHalfSpinorHermitianPairing_nondegenerate
    (spinor : AmbientHalfSpinor2)
    (hRadical : ∀ test, ambientHalfSpinorHermitianPairing spinor test = 0) :
    spinor = 0 := by
  funext index
  have hIndex := hRadical (fun candidate ↦ if candidate = index then 1 else 0)
  fin_cases index <;>
    simp [ambientHalfSpinorHermitianPairing,
      ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
      Fin.sum_univ_succ] at hIndex ⊢
  all_goals
    apply (starRingEnd Complex).injective
    simpa using hIndex

def d9MatterSpinorHermitianPairing
    (first second : MatterFiber) : Complex :=
  ambientHalfSpinorHermitianPairing
    (matterFiberHalfSpinorLinearEquiv first)
    (matterFiberHalfSpinorLinearEquiv second)

theorem d9MatterSpinorHermitianPairing_nondegenerate
    (matter : MatterFiber)
    (hRadical : ∀ test, d9MatterSpinorHermitianPairing matter test = 0) :
    matter = 0 := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  rw [map_zero]
  apply ambientHalfSpinorHermitianPairing_nondegenerate
  intro test
  simpa [d9MatterSpinorHermitianPairing] using
    hRadical (matterFiberHalfSpinorLinearEquiv.symm test)

def canonicalAmbientPinCMatterCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (matter : MatterFiber) : MatterFiber :=
  matterFiberHalfSpinorLinearEquiv.symm
    (canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
      first second base (matterFiberHalfSpinorLinearEquiv matter))

theorem canonicalAmbientPinCMatterCoordChange_preserves_pairing
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (left right : MatterFiber) :
    d9MatterSpinorHermitianPairing
        (canonicalAmbientPinCMatterCoordChange period hPeriod choice
          first second base left)
        (canonicalAmbientPinCMatterCoordChange period hPeriod choice
          first second base right) =
      d9MatterSpinorHermitianPairing left right := by
  unfold d9MatterSpinorHermitianPairing
    canonicalAmbientPinCMatterCoordChange
  simp only [LinearEquiv.apply_symm_apply]
  exact canonicalAmbientPinCHalfSpinorCoordChange_preserves_pairing
    period hPeriod choice first second base _ _

structure ProgramPD9MatterSpinorHermitianPairingCertificate4D where
  choice : NormalRootChoice
  bundle : ProgramPAmbientHalfSpinorActualBundleCertificate4D period hPeriod
  pairing : MatterFiber → MatterFiber → Complex
  pairingCanonical : pairing = d9MatterSpinorHermitianPairing
  pairingNondegenerate : ∀ matter,
    (∀ test, pairing matter test = 0) → matter = 0
  pairingInvariant : ∀ first second base left right,
    pairing
        (canonicalAmbientPinCMatterCoordChange period hPeriod choice
          first second base left)
        (canonicalAmbientPinCMatterCoordChange period hPeriod choice
          first second base right) =
      pairing left right

def programPD9MatterSpinorHermitianPairingCertificate4D
    (choice : NormalRootChoice) :
    ProgramPD9MatterSpinorHermitianPairingCertificate4D period hPeriod where
  choice := choice
  bundle := programPAmbientHalfSpinorActualBundleCertificate4D
    period hPeriod choice
  pairing := d9MatterSpinorHermitianPairing
  pairingCanonical := rfl
  pairingNondegenerate := d9MatterSpinorHermitianPairing_nondegenerate
  pairingInvariant :=
    canonicalAmbientPinCMatterCoordChange_preserves_pairing
      period hPeriod choice

theorem programPD9MatterSpinorHermitianPairingCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorHermitianPairingCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorHermitianPairingCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
end JanusFormal
