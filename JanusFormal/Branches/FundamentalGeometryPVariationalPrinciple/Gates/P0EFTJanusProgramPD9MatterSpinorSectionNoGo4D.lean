import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentFieldVariationLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-! # No-go for the current D9 matter coefficient space

The current matter variations are ordinary globally trivial coefficient
functions.  A concrete constant coefficient fails the one-loop transition of
the actual throat spinor bundle, so that space cannot yet be its section space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorSectionNoGo4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase := MappingTorus (fixedEquatorData period hPeriod)

def firstHalfSpinor : AmbientHalfSpinor2 :=
  fun index => if index = 0 then 1 else 0

theorem canonicalAmbientPinCHalfSpinorCoordChange_one_loop_first_ne
    (choice : NormalRootChoice) (anchor : AmbientCover period hPeriod) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
        anchor ((1 : Int) +ᵥ anchor) base firstHalfSpinor ≠
      firstHalfSpinor := by
  dsimp only
  unfold canonicalAmbientPinCHalfSpinorCoordChange
    canonicalAmbientPinCSpinorCoordChange
  rw [canonicalAmbientPinCSpinorTransitionMatrix_eq_product,
    ← Matrix.mulVec_mulVec]
  unfold canonicalAmbientPinMinusPrincipalCoordChange
    canonicalAmbientCirclePrincipalCoordChange
    canonicalAmbientReferencePinMinusTransitionLift
    ambientCircleReferenceTransitionLift
  simp only [mul_one]
  rw [ambientTransitionWinding_one_loop period hPeriod anchor]
  change ambientHalfSpinorProject
      ((ambientPinMinusGammaRepresentation
          (ambientPinMinusReferenceZ4Character 1) : AmbientComplexMatrix4) *ᵥ
        ((ambientCircleGammaScalarRepresentation
          (normalRootCircleCharacter choice 1) : AmbientComplexMatrix4) *ᵥ
          ambientHalfSpinorEmbed firstHalfSpinor)) ≠ firstHalfSpinor
  rw [P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D.ambientCircleGammaScalarRepresentation_mulVec,
    ← ambientHalfSpinorEmbed_smul,
    ambientReferenceZ4Action_preserves_halfSpinor,
    ambientHalfSpinorProject_embed]
  intro hEqual
  have hZero := congrFun hEqual 0
  simp [firstHalfSpinor, ambientHalfGammaZ4Representation_one,
    ambientHalfGammaGeneratorUnit, ambientHalfGammaGenerator,
    Matrix.mulVec, dotProduct] at hZero

def firstSpinorMatterCoordinate : MatterFiber :=
  matterFiberHalfSpinorLinearEquiv.symm firstHalfSpinor

theorem canonicalAmbientPinCMatterCoordChange_one_loop_first_ne
    (choice : NormalRootChoice) (anchor : AmbientCover period hPeriod) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    canonicalAmbientPinCMatterCoordChange period hPeriod choice
        anchor ((1 : Int) +ᵥ anchor) base firstSpinorMatterCoordinate ≠
      firstSpinorMatterCoordinate := by
  dsimp only
  intro hEqual
  have hMapped := congrArg matterFiberHalfSpinorLinearEquiv hEqual
  simp only [canonicalAmbientPinCMatterCoordChange,
    LinearEquiv.apply_symm_apply] at hMapped
  exact canonicalAmbientPinCHalfSpinorCoordChange_one_loop_first_ne
    period hPeriod choice anchor hMapped

theorem throatAmbientPinCMatterCoordChange_one_loop_first_ne
    (choice : NormalRootChoice)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    throatAmbientPinCMatterCoordChange period hPeriod choice
        ambientAnchor ((1 : Int) +ᵥ ambientAnchor) base
        firstSpinorMatterCoordinate ≠ firstSpinorMatterCoordinate := by
  dsimp only
  unfold throatAmbientPinCMatterCoordChange
  rw [fixedThroatQuotientInclusion_mk]
  exact canonicalAmbientPinCMatterCoordChange_one_loop_first_ne
    period hPeriod choice (fixedThroatCoverInclusion period hPeriod anchor)

def constantFirstMatterVariation :
    IndependentFieldVariation period hPeriod :=
  { (0 : IndependentFieldVariation period hPeriod) with
    matter :=
      (constantSmoothField period hPeriod MatterFiber
          firstSpinorMatterCoordinate,
        constantSmoothField period hPeriod MatterFiber 0) }

@[simp] theorem d9MatterCoefficient_constantFirst
    (point : ThroatBase period hPeriod) :
    d9MatterCoefficient period hPeriod
        (constantFirstMatterVariation period hPeriod) .plus point =
      firstSpinorMatterCoordinate := by
  rfl

theorem currentD9MatterFieldSpace_contains_nonsection
    (choice : NormalRootChoice)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    throatAmbientPinCMatterCoordChange period hPeriod choice
        ambientAnchor ((1 : Int) +ᵥ ambientAnchor) base
        (d9MatterCoefficient period hPeriod
          (constantFirstMatterVariation period hPeriod) .plus base) ≠
      d9MatterCoefficient period hPeriod
        (constantFirstMatterVariation period hPeriod) .plus base := by
  dsimp only
  rw [d9MatterCoefficient_constantFirst]
  exact throatAmbientPinCMatterCoordChange_one_loop_first_ne
    period hPeriod choice anchor

structure ProgramPD9MatterSpinorSectionNoGoCertificate4D where
  choice : NormalRootChoice
  variation : IndependentFieldVariation period hPeriod
  variationCanonical : variation = constantFirstMatterVariation period hPeriod
  oneLoopFailure : ∀ anchor :
      MappingTorusCover (fixedEquatorData period hPeriod),
    let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    throatAmbientPinCMatterCoordChange period hPeriod choice
        ambientAnchor ((1 : Int) +ᵥ ambientAnchor) base
        (d9MatterCoefficient period hPeriod variation .plus base) ≠
      d9MatterCoefficient period hPeriod variation .plus base

def programPD9MatterSpinorSectionNoGoCertificate4D :
    ProgramPD9MatterSpinorSectionNoGoCertificate4D period hPeriod where
  choice := .positiveQuarter
  variation := constantFirstMatterVariation period hPeriod
  variationCanonical := rfl
  oneLoopFailure := currentD9MatterFieldSpace_contains_nonsection
    period hPeriod .positiveQuarter

theorem programPD9MatterSpinorSectionNoGoCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorSectionNoGoCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorSectionNoGoCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorSectionNoGo4D
end JanusFormal
