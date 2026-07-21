import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D

/-! # Hermitian structure on the actual ambient PinC spinor bundle

The actual transition functions use the reference `ZMod 4` Pin-minus
character and a circle phase.  Their four-component gamma action preserves
the standard Hermitian pairing on `ℂ⁴`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

def ambientPinCSpinorHermitianPairing
    (first second : AmbientDiracSpinor4) : Complex :=
  ∑ index, (starRingEnd Complex) (first index) * second index

theorem ambientPinCSpinorHermitianPairing_circle_smul
    (phase : Circle) (first second : AmbientDiracSpinor4) :
    ambientPinCSpinorHermitianPairing
        ((phase : Complex) • first) ((phase : Complex) • second) =
      ambientPinCSpinorHermitianPairing first second := by
  unfold ambientPinCSpinorHermitianPairing
  apply Finset.sum_congr rfl
  intro index _
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Circle.coe_inv_eq_conj]
  calc
    (((phase⁻¹ : Circle) : Complex) * (starRingEnd Complex) (first index)) *
          ((phase : Complex) * second index) =
        (((phase⁻¹ : Circle) : Complex) * (phase : Complex)) *
          ((starRingEnd Complex) (first index) * second index) := by ring
    _ = (starRingEnd Complex) (first index) * second index := by
      rw [← Circle.coe_mul]
      simp

@[simp] theorem ambientCircleGammaScalarRepresentation_mulVec
    (phase : Circle) (spinor : AmbientDiracSpinor4) :
    (ambientCircleGammaScalarRepresentation phase : AmbientComplexMatrix4) *ᵥ
        spinor =
      (phase : Complex) • spinor := by
  ext index
  fin_cases index <;>
    simp [ambientCircleGammaScalarRepresentation_coe,
      Matrix.algebraMap_matrix_apply, Matrix.mulVec, dotProduct]

theorem ambientPinMinusReferenceZ4SpinorPairing_invariant
    (winding : ZMod 4) (first second : AmbientDiracSpinor4) :
    ambientPinCSpinorHermitianPairing
        ((ambientPinMinusGammaRepresentation
            (ambientPinMinusReferenceZ4Character winding) :
              AmbientComplexMatrix4) *ᵥ first)
        ((ambientPinMinusGammaRepresentation
            (ambientPinMinusReferenceZ4Character winding) :
              AmbientComplexMatrix4) *ᵥ second) =
      ambientPinCSpinorHermitianPairing first second := by
  rw [← ZMod.natCast_zmod_val winding]
  have hBound : winding.val < 4 := winding.val_lt
  interval_cases hValue : winding.val <;>
    simp [ambientPinCSpinorHermitianPairing,
      ambientPinMinusGammaRepresentation_coe,
      ambientPinMinusReferenceZ4Character_one,
      ambientPinMinusReferenceZ4Character_two,
      ambientPinMinusReferenceZ4Character_three,
      ambientPinMinusReferenceGenerator_coe,
      ambientPinMinusCentralSign_coe,
      ambientCliffordGammaRepresentation_iota,
      ambientGammaMatrix, ambientGammaBasis,
      ambientPinMinusReferenceVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem ambientReferencePinCircleSpinorPairing_invariant
    (winding : ZMod 4) (phase : Circle)
    (first second : AmbientDiracSpinor4) :
    ambientPinCSpinorHermitianPairing
        ((((ambientPinMinusGammaRepresentation
              (ambientPinMinusReferenceZ4Character winding) :
                AmbientComplexMatrix4ˣ) : AmbientComplexMatrix4) *
            ((ambientCircleGammaScalarRepresentation phase :
                AmbientComplexMatrix4ˣ) : AmbientComplexMatrix4)) *ᵥ first)
        ((((ambientPinMinusGammaRepresentation
              (ambientPinMinusReferenceZ4Character winding) :
                AmbientComplexMatrix4ˣ) : AmbientComplexMatrix4) *
            ((ambientCircleGammaScalarRepresentation phase :
                AmbientComplexMatrix4ˣ) : AmbientComplexMatrix4)) *ᵥ second) =
      ambientPinCSpinorHermitianPairing first second := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [ambientPinMinusReferenceZ4SpinorPairing_invariant,
    ambientCircleGammaScalarRepresentation_mulVec,
    ambientCircleGammaScalarRepresentation_mulVec,
    ambientPinCSpinorHermitianPairing_circle_smul]

set_option maxHeartbeats 800000 in
theorem canonicalAmbientPinCSpinorCoordChange_preserves_pairing
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (left right : AmbientDiracSpinor4) :
    ambientPinCSpinorHermitianPairing
        (canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first second base left)
        (canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first second base right) =
      ambientPinCSpinorHermitianPairing left right := by
  unfold canonicalAmbientPinCSpinorCoordChange
  rw [canonicalAmbientPinCSpinorTransitionMatrix_eq_product]
  unfold canonicalAmbientPinMinusPrincipalCoordChange
    canonicalAmbientCirclePrincipalCoordChange
    canonicalAmbientReferencePinMinusTransitionLift
    ambientCircleReferenceTransitionLift
  simp only [mul_one]
  simpa only [ambientPinMinusGammaRepresentation_coe,
    ambientCircleGammaScalarRepresentation_coe] using
    (ambientReferencePinCircleSpinorPairing_invariant
      (ambientTransitionWinding period hPeriod first second
        (P0EFTJanusMappingTorusAmbientTangentOrientationCocycle.ambientQuotientLocalChart
          period hPeriod first base) : ZMod 4)
      (normalRootCircleCharacter choice
        (ambientTransitionWinding period hPeriod first second
          (P0EFTJanusMappingTorusAmbientTangentOrientationCocycle.ambientQuotientLocalChart
            period hPeriod first base) : ZMod 4))
      left right)

theorem ambientPinCSpinorHermitianPairing_nondegenerate
    (spinor : AmbientDiracSpinor4)
    (hRadical : ∀ test,
      ambientPinCSpinorHermitianPairing spinor test = 0) :
    spinor = 0 := by
  funext index
  have hIndex := hRadical (fun candidate ↦ if candidate = index then 1 else 0)
  simp [ambientPinCSpinorHermitianPairing] at hIndex
  apply (starRingEnd Complex).injective
  simpa using hIndex

structure ProgramPAmbientPinCSpinorHermitianBundleCertificate4D where
  choice : NormalRootChoice
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientDiracSpinor4
  coreCanonical : core =
    canonicalAmbientPinCSpinorBundleCore period hPeriod choice
  pairingPreserved : ∀ first second base left right,
    ambientPinCSpinorHermitianPairing
        (core.coordChange first second base left)
        (core.coordChange first second base right) =
      ambientPinCSpinorHermitianPairing left right
  pairingNondegenerate : ∀ spinor,
    (∀ test, ambientPinCSpinorHermitianPairing spinor test = 0) → spinor = 0

def programPAmbientPinCSpinorHermitianBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientPinCSpinorHermitianBundleCertificate4D period hPeriod where
  choice := choice
  core := canonicalAmbientPinCSpinorBundleCore period hPeriod choice
  coreCanonical := rfl
  pairingPreserved :=
    canonicalAmbientPinCSpinorCoordChange_preserves_pairing
      period hPeriod choice
  pairingNondegenerate := ambientPinCSpinorHermitianPairing_nondegenerate

theorem programPAmbientPinCSpinorHermitianBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientPinCSpinorHermitianBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientPinCSpinorHermitianBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
end JanusFormal
