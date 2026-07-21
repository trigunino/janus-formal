import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D

/-! # Determinant line associated to the winding-twisted ambient PinC bundle

The continuous determinant character acts on `ℂ` by scalar multiplication.
Applying it to the actual twisted `PinC(4)` transitions gives a genuine complex
line bundle core with invariant Hermitian pairing and one-loop multiplier
`-1`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCDeterminantLineBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D
open P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

def canonicalAmbientPinCDeterminantLineMultiplier
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) : Circle :=
  ambientPinCDeterminantCharacter
    (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
      first second base)

theorem canonicalAmbientPinCDeterminantLineMultiplier_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (canonicalAmbientPinCDeterminantLineMultiplier period hPeriod choice
        first second)
      (ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) := by
  exact continuous_ambientPinCDeterminantCharacter.continuousOn.comp
    (canonicalAmbientWindingTwistedPinCTransition_continuousOn
      period hPeriod choice first second) (fun _ _ ↦ Set.mem_univ _)

def canonicalAmbientPinCDeterminantLineCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (line : Complex) : Complex :=
  (canonicalAmbientPinCDeterminantLineMultiplier period hPeriod choice
    first second base : Complex) * line

theorem canonicalAmbientPinCDeterminantLineCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × Complex ↦
        canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  refine ContinuousOn.mul
    (f := fun point : AmbientBase period hPeriod × Complex ↦
      (canonicalAmbientPinCDeterminantLineMultiplier period hPeriod choice
        first second point.1 : Complex))
    (g := fun point : AmbientBase period hPeriod × Complex ↦ point.2) ?_
      continuousOn_snd
  exact continuous_subtype_val.continuousOn.comp
    ((canonicalAmbientPinCDeterminantLineMultiplier_continuousOn
      period hPeriod choice first second).comp continuousOn_fst (by
        intro point hPoint
        exact hPoint.1)) (fun _ _ ↦ Set.mem_univ _)

/-- Actual complex determinant-line bundle associated to the twisted PinC
principal bundle. -/
def canonicalAmbientPinCDeterminantLineBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      Complex where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange :=
    canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
  coordChange_self anchor base hBase line := by
    have hSelf :=
      (canonicalAmbientWindingTwistedPinCPrincipalBundleCore
        period hPeriod choice).coordChange_self anchor base hBase 1
    change canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
      anchor anchor base * 1 = 1 at hSelf
    rw [mul_one] at hSelf
    unfold canonicalAmbientPinCDeterminantLineCoordChange
      canonicalAmbientPinCDeterminantLineMultiplier
    rw [hSelf, map_one]
    simp
  continuousOn_coordChange :=
    canonicalAmbientPinCDeterminantLineCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase line := by
    let core := canonicalAmbientWindingTwistedPinCPrincipalBundleCore
      period hPeriod choice
    have hComp := core.coordChange_comp first second third base hBase 1
    have hTransition :
        canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
              second third base *
            canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
              first second base =
          canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
            first third base := by
      simpa [core, canonicalAmbientWindingTwistedPinCPrincipalBundleCore,
        canonicalAmbientWindingTwistedPinCPrincipalCoordChange] using hComp
    have hCharacter := congrArg ambientPinCDeterminantCharacter hTransition
    simp only [map_mul] at hCharacter
    unfold canonicalAmbientPinCDeterminantLineCoordChange
      canonicalAmbientPinCDeterminantLineMultiplier
    rw [← mul_assoc, ← Circle.coe_mul, hCharacter]

def ambientPinCDeterminantHermitianPairing
    (first second : Complex) : Complex :=
  (starRingEnd Complex) first * second

theorem canonicalAmbientPinCDeterminantLineCoordChange_preserves_pairing
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (left right : Complex) :
    ambientPinCDeterminantHermitianPairing
        (canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
          first second base left)
        (canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
          first second base right) =
      ambientPinCDeterminantHermitianPairing left right := by
  let phase := canonicalAmbientPinCDeterminantLineMultiplier
    period hPeriod choice first second base
  change (starRingEnd Complex) ((phase : Complex) * left) *
      ((phase : Complex) * right) =
    (starRingEnd Complex) left * right
  rw [map_mul, ← Circle.coe_inv_eq_conj]
  calc
    (((phase⁻¹ : Circle) : Complex) * (starRingEnd Complex) left) *
          ((phase : Complex) * right) =
        (((phase⁻¹ : Circle) : Complex) * (phase : Complex)) *
          ((starRingEnd Complex) left * right) := by ring
    _ = (starRingEnd Complex) left * right := by
      rw [← Circle.coe_mul]
      simp

theorem canonicalAmbientPinCDeterminantLineCoordChange_one_loop
    (choice : NormalRootChoice)
    (anchor : AmbientCover period hPeriod) (line : Complex) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
      anchor ((1 : Int) +ᵥ anchor) base line = -line := by
  let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
  change canonicalAmbientPinCDeterminantLineCoordChange period hPeriod choice
      anchor ((1 : Int) +ᵥ anchor) base line = -line
  unfold canonicalAmbientPinCDeterminantLineCoordChange
    canonicalAmbientPinCDeterminantLineMultiplier
  rw [canonicalAmbientWindingTwistedPinC_determinantTransition_one_loop]
  simp

abbrev CanonicalAmbientPinCDeterminantLineFiber
    (choice : NormalRootChoice) :=
  (canonicalAmbientPinCDeterminantLineBundleCore period hPeriod choice).Fiber

@[reducible] def canonicalAmbientPinCDeterminantLineFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle Complex
      (CanonicalAmbientPinCDeterminantLineFiber period hPeriod choice) :=
  inferInstance

structure ProgramPAmbientPinCDeterminantLineBundleCertificate4D where
  choice : NormalRootChoice
  pinCBundle :
    ProgramPAmbientWindingTwistedPinCActualBundleCertificate4D period hPeriod
  lineCore : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) Complex
  lineCoreCanonical : lineCore =
    canonicalAmbientPinCDeterminantLineBundleCore period hPeriod choice
  pairingPreserved : ∀ first second base left right,
    ambientPinCDeterminantHermitianPairing
        (lineCore.coordChange first second base left)
        (lineCore.coordChange first second base right) =
      ambientPinCDeterminantHermitianPairing left right

def programPAmbientPinCDeterminantLineBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientPinCDeterminantLineBundleCertificate4D period hPeriod where
  choice := choice
  pinCBundle := programPAmbientWindingTwistedPinCActualBundleCertificate4D
    period hPeriod choice
  lineCore := canonicalAmbientPinCDeterminantLineBundleCore
    period hPeriod choice
  lineCoreCanonical := rfl
  pairingPreserved :=
    canonicalAmbientPinCDeterminantLineCoordChange_preserves_pairing
      period hPeriod choice

theorem programPAmbientPinCDeterminantLineBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientPinCDeterminantLineBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientPinCDeterminantLineBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientPinCDeterminantLineBundle4D
end JanusFormal
