import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D

/-! # Bridge from the smooth D9 monodromy to the ambient pullback -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPNormalZ4RootHermitianMetric4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev AmbientCover4 :=
  MappingTorusCover (reflectedSphereData period hPeriod)

theorem ambientTransitionWinding_deck
    (winding : Int) (anchor : AmbientCover4 period hPeriod) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    let coordinate := ambientQuotientLocalChart period hPeriod anchor base
    ambientTransitionWinding period hPeriod anchor (winding +ᵥ anchor)
      coordinate = winding := by
  let data := reflectedSphereData period hPeriod
  let projection := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
  let base := mappingTorusMk data anchor
  let second := winding +ᵥ anchor
  let coordinate := ambientQuotientLocalChart period hPeriod anchor base
  have hProjection : mappingTorusMk data second = base :=
    (mappingTorusMk_isAddQuotientCoveringMap data).map_vadd winding
  have hFirst : base ∈ ambientPinMinusBundleBaseSet period hPeriod anchor :=
    ambientQuotientLocalChart_mk_mem_source period hPeriod anchor
  have hSecond : base ∈ ambientPinMinusBundleBaseSet period hPeriod second := by
    rw [← hProjection]
    exact ambientQuotientLocalChart_mk_mem_source period hPeriod second
  have hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor second).source := by
    change coordinate ∈ ((ambientQuotientLocalChart period hPeriod anchor).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(ambientQuotientLocalChart period hPeriod anchor).map_source hFirst, ?_⟩
    change (ambientQuotientLocalChart period hPeriod anchor).symm coordinate ∈
      (ambientQuotientLocalChart period hPeriod second).source
    rw [(ambientQuotientLocalChart period hPeriod anchor).left_inv hFirst]
    exact hSecond
  have hBaseCoordinate :
      (ambientQuotientLocalChart period hPeriod anchor).symm coordinate = base :=
    (ambientQuotientLocalChart period hPeriod anchor).left_inv hFirst
  have hFirstValue : projection.localInverseAt anchor base = anchor :=
    projection.localInverseAt_apply_self
  have hSecondValue : projection.localInverseAt second base = second := by
    rw [← hProjection]
    exact projection.localInverseAt_apply_self
  change ambientTransitionWinding period hPeriod anchor second coordinate = winding
  symm
  apply ambientTransitionWinding_unique period hPeriod anchor second coordinate
    hCoordinate winding
  change winding +ᵥ projection.localInverseAt anchor
        ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate) =
    projection.localInverseAt second
      ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate)
  rw [hBaseCoordinate, hFirstValue, hSecondValue]

theorem throatAmbientPinCMatterCoordChange_deck_eq_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (anchor : ThroatCover period hPeriod) (matter : MatterFiber) :
    throatAmbientPinCMatterCoordChange period hPeriod choice
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatCoverInclusion period hPeriod (winding +ᵥ anchor))
        (mappingTorusMk (ThroatData period hPeriod) anchor) matter =
      d9MatterSpinorMonodromy choice winding matter := by
  rw [fixedThroatCoverInclusion_equivariant]
  unfold throatAmbientPinCMatterCoordChange
  rw [fixedThroatQuotientInclusion_mk]
  unfold canonicalAmbientPinCMatterCoordChange
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  unfold canonicalAmbientPinCHalfSpinorCoordChange
    canonicalAmbientPinCSpinorCoordChange
  rw [canonicalAmbientPinCSpinorTransitionMatrix_eq_product,
    ← Matrix.mulVec_mulVec]
  unfold canonicalAmbientPinMinusPrincipalCoordChange
    canonicalAmbientCirclePrincipalCoordChange
    canonicalAmbientReferencePinMinusTransitionLift
    ambientCircleReferenceTransitionLift
  simp only [mul_one]
  rw [ambientTransitionWinding_deck period hPeriod winding,
    normalRootCircleCharacter_intCast]
  change ambientHalfSpinorProject
      ((ambientPinMinusGammaRepresentation
          (ambientPinMinusReferenceZ4Character (winding : ZMod 4)) :
            AmbientComplexMatrix4) *ᵥ
        ((ambientCircleGammaScalarRepresentation
          (quarterRootCircleRepresentation choice winding) :
            AmbientComplexMatrix4) *ᵥ ambientHalfSpinorEmbed
              (matterFiberHalfSpinorLinearEquiv matter))) = _
  rw [P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D.ambientCircleGammaScalarRepresentation_mulVec,
    ← ambientHalfSpinorEmbed_smul,
    ambientReferenceZ4Action_preserves_halfSpinor,
    ambientHalfSpinorProject_embed]
  simp [d9MatterSpinorMonodromy, quarterRootCircleRepresentation]

theorem d9MatterSpinorMonodromy_preserves_pairing
    (choice : NormalRootChoice) (winding : Int)
    (anchor : ThroatCover period hPeriod)
    (first second : MatterFiber) :
    d9MatterSpinorHermitianPairing
        (d9MatterSpinorMonodromy choice winding first)
        (d9MatterSpinorMonodromy choice winding second) =
      d9MatterSpinorHermitianPairing first second := by
  rw [← throatAmbientPinCMatterCoordChange_deck_eq_monodromy
      period hPeriod choice winding anchor,
    ← throatAmbientPinCMatterCoordChange_deck_eq_monodromy
      period hPeriod choice winding anchor]
  exact throatAmbientPinCMatterCoordChange_preserves_pairing
    period hPeriod choice _ _ _ _ _

theorem SmoothThroatMatterSpinorLift.deck_monodromy
    (choice : NormalRootChoice)
    (spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice)
    (winding : Int) (anchor : ThroatCover period hPeriod) :
    spinorSection (winding +ᵥ anchor) =
      d9MatterSpinorMonodromy choice winding (spinorSection anchor) := by
  rw [spinorSection.deck_equivariant]
  exact throatAmbientPinCMatterCoordChange_deck_eq_monodromy
    period hPeriod choice winding anchor (spinorSection anchor)

structure ProgramPD9MatterSpinorSmoothPullbackBridgeCertificate4D where
  choice : NormalRootChoice
  deckCompatibility : ∀ winding anchor matter,
    throatAmbientPinCMatterCoordChange period hPeriod choice
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatCoverInclusion period hPeriod (winding +ᵥ anchor))
        (mappingTorusMk (ThroatData period hPeriod) anchor) matter =
      d9MatterSpinorMonodromy choice winding matter
  sectionCompatibility : ∀
      (spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice)
      winding anchor,
    spinorSection (winding +ᵥ anchor) =
      d9MatterSpinorMonodromy choice winding (spinorSection anchor)

def programPD9MatterSpinorSmoothPullbackBridgeCertificate4D :
    ProgramPD9MatterSpinorSmoothPullbackBridgeCertificate4D period hPeriod where
  choice := .positiveQuarter
  deckCompatibility := throatAmbientPinCMatterCoordChange_deck_eq_monodromy
    period hPeriod .positiveQuarter
  sectionCompatibility := SmoothThroatMatterSpinorLift.deck_monodromy
    period hPeriod .positiveQuarter

theorem programPD9MatterSpinorSmoothPullbackBridgeCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorSmoothPullbackBridgeCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorSmoothPullbackBridgeCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
end JanusFormal
