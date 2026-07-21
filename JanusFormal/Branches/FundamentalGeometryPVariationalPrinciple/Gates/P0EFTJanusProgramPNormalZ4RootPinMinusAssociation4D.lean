import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNormalZ4RootHermitianMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusAssociatedRoots

/-! # The normal Z4-root line as a Pin-minus associated line

The complex root transitions are obtained by applying a unitary character to
the actual normal `Pin⁻(1)` principal transitions.  The latter are precisely
the throat restriction of the canonical ambient `Pin⁻(4)` bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPNormalZ4RootHermitianMetric4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

def normalRootCircleGenerator (choice : NormalRootChoice) : Circle :=
  quarterRootCircleRepresentation choice 1

private def normalRootCircleIntHom (choice : NormalRootChoice) :
    Int →+ Additive Circle :=
  zmultiplesHom (Additive Circle) (Additive.ofMul (normalRootCircleGenerator choice))

private theorem normalRootCircleIntHom_four (choice : NormalRootChoice) :
    normalRootCircleIntHom choice 4 = 0 := by
  apply Additive.toMul.injective
  simp only [normalRootCircleIntHom, zmultiplesHom_apply,
    toMul_zsmul, toMul_ofMul, toMul_zero]
  apply Circle.ext
  change (normalRootCircleGenerator choice : Complex) ^ (4 : Int) = 1
  simp only [normalRootCircleGenerator, quarterRootCircleRepresentation,
    quarterRootRepresentation_one]
  rw [zpow_ofNat]
  calc
    normalRootMultiplier choice ^ 4 =
        normalRootMultiplier choice * normalRootMultiplier choice *
          normalRootMultiplier choice * normalRootMultiplier choice := by ring
    _ = 1 := normal_root_multiplier_fourth choice

def normalRootCircleZ4AddHom (choice : NormalRootChoice) :
    ZMod 4 →+ Additive Circle :=
  ZMod.lift 4 ⟨normalRootCircleIntHom choice,
    normalRootCircleIntHom_four choice⟩

/-- Unitary complex-line character of the normal `Pin⁻(1) ≃ ZMod 4`. -/
def normalRootCircleCharacter (choice : NormalRootChoice) :
    AddChar (ZMod 4) Circle :=
  AddChar.toAddMonoidHomEquiv.symm (normalRootCircleZ4AddHom choice)

theorem normalRootCircleCharacter_intCast
    (choice : NormalRootChoice) (winding : Int) :
    normalRootCircleCharacter choice (winding : ZMod 4) =
      quarterRootCircleRepresentation choice winding := by
  change (normalRootCircleZ4AddHom choice (winding : ZMod 4)).toMul = _
  have hLift :
      normalRootCircleZ4AddHom choice (winding : ZMod 4) =
        normalRootCircleIntHom choice winding := by
    exact ZMod.lift_coe 4
      ⟨normalRootCircleIntHom choice, normalRootCircleIntHom_four choice⟩ winding
  rw [hLift]
  apply Circle.ext
  simp [normalRootCircleIntHom, normalRootCircleGenerator,
    quarterRootCircleRepresentation, quarterRootRepresentation]

/-- The complex root bundle is the associated line of the normal principal
bundle, chart by chart. -/
theorem fixedThroatNormalZ4Root_coordChange_is_pinMinus_associated
    (choice : NormalRootChoice)
    (firstChart secondChart : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) (root : Complex) :
    (fixedThroatNormalZ4RootBundleCore period hPeriod choice).coordChange
        firstChart secondChart base root =
      (normalRootCircleCharacter choice
          (localTransitionWinding period hPeriod firstChart secondChart base :
            ZMod 4) : Complex) * root := by
  simp only [fixedThroatNormalZ4RootBundleCore, quarterRootCLM_apply]
  rw [normalRootCircleCharacter_intCast]
  rfl

/-- On a compatible throat overlap the ambient Pin-minus transition and the
associated complex root transition carry the same `ZMod 4` winding. -/
theorem canonicalAmbientPinMinusTransition_and_normalRoot_associated
    (choice : NormalRootChoice)
    (firstChart secondChart : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod firstChart secondChart)
    (root : Complex) :
    canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        (fixedThroatCoverInclusion period hPeriod firstChart)
        (fixedThroatCoverInclusion period hPeriod secondChart)
        (throatAmbientOverlapCoordinate period hPeriod firstChart base) =
      ambientPinMinusReferenceZ4Character
        (localTransitionWinding period hPeriod firstChart secondChart base : ZMod 4) ∧
    (fixedThroatNormalZ4RootBundleCore period hPeriod choice).coordChange
        firstChart secondChart base root =
      (normalRootCircleCharacter choice
          (localTransitionWinding period hPeriod firstChart secondChart base :
            ZMod 4) : Complex) * root := by
  exact ⟨canonicalAmbientPinMinusPrincipalTransition_restricts_to_throat
      period hPeriod firstChart secondChart base hBase,
    fixedThroatNormalZ4Root_coordChange_is_pinMinus_associated
      period hPeriod choice firstChart secondChart base root⟩

structure ProgramPNormalZ4RootPinMinusAssociationCertificate4D
    (choice : NormalRootChoice) where
  principalBundle : NormalPinMinusPrincipalBundle period hPeriod
  principalBundleCanonical :
    principalBundle = fixedThroatNormalPinMinusPrincipalBundle period hPeriod
  associatedLine :
    VectorBundleCore Complex (ThroatBase period hPeriod) Complex
      (ThroatCover period hPeriod)
  associatedLineCanonical :
    associatedLine = fixedThroatNormalZ4RootBundleCore period hPeriod choice
  associatedCoordChange :
    ∀ firstChart secondChart base root,
      associatedLine.coordChange firstChart secondChart base root =
        (normalRootCircleCharacter choice
            (localTransitionWinding period hPeriod firstChart secondChart base :
              ZMod 4) : Complex) * root

def programPNormalZ4RootPinMinusAssociationCertificate4D
    (choice : NormalRootChoice) :
    ProgramPNormalZ4RootPinMinusAssociationCertificate4D
      period hPeriod choice where
  principalBundle := fixedThroatNormalPinMinusPrincipalBundle period hPeriod
  principalBundleCanonical := rfl
  associatedLine := fixedThroatNormalZ4RootBundleCore period hPeriod choice
  associatedLineCanonical := rfl
  associatedCoordChange :=
    fixedThroatNormalZ4Root_coordChange_is_pinMinus_associated
      period hPeriod choice

theorem programPNormalZ4RootPinMinusAssociationCertificate4D_nonempty
    (choice : NormalRootChoice) :
    Nonempty
      (ProgramPNormalZ4RootPinMinusAssociationCertificate4D
        period hPeriod choice) :=
  ⟨programPNormalZ4RootPinMinusAssociationCertificate4D
    period hPeriod choice⟩

end
end P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
end JanusFormal
