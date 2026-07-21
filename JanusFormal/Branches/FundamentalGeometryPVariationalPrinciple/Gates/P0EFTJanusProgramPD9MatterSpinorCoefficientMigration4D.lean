import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-! # Typed D9 matter coefficient from spinorial sections -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

abbrev D9SpinorialMatterVariation (choice : NormalRootChoice) :=
  SmoothThroatMatterSpinorLift period hPeriod choice ×
    SmoothThroatMatterSpinorLift period hPeriod choice

def d9SpinorialMatterCoefficient
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (anchor : ThroatCover period hPeriod) : MatterFiber :=
  selectSector sector variation anchor

theorem d9SpinorialMatterCoefficient_deck_equivariant
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (winding : Int)
    (anchor : ThroatCover period hPeriod) :
    d9SpinorialMatterCoefficient period hPeriod choice variation sector
        (winding +ᵥ anchor) =
      throatAmbientPinCMatterCoordChange period hPeriod choice
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatCoverInclusion period hPeriod (winding +ᵥ anchor))
        (mappingTorusMk (ThroatData period hPeriod) anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor) := by
  cases sector <;>
    exact (selectSector _ variation).deck_equivariant winding anchor

theorem d9SpinorialMatterPairing_deck_invariant
    (choice : NormalRootChoice)
    (first second : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (winding : Int)
    (anchor : ThroatCover period hPeriod) :
    d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice first sector
          (winding +ᵥ anchor))
        (d9SpinorialMatterCoefficient period hPeriod choice second sector
          (winding +ᵥ anchor)) =
      d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice first sector anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice second sector
          anchor) := by
  rw [d9SpinorialMatterCoefficient_deck_equivariant,
    d9SpinorialMatterCoefficient_deck_equivariant]
  exact throatAmbientPinCMatterCoordChange_preserves_pairing
    period hPeriod choice _ _ _ _ _

@[simp] theorem d9SpinorialMatterCoefficient_zero
    (choice : NormalRootChoice) (sector : Sector)
    (anchor : ThroatCover period hPeriod) :
    d9SpinorialMatterCoefficient period hPeriod choice
      (0 : D9SpinorialMatterVariation period hPeriod choice) sector anchor = 0 := by
  cases sector <;> rfl

structure ProgramPD9MatterSpinorCoefficientMigrationCertificate4D where
  choice : NormalRootChoice
  variationModule : Module Real
    (D9SpinorialMatterVariation period hPeriod choice)
  zeroVariation : D9SpinorialMatterVariation period hPeriod choice

def programPD9MatterSpinorCoefficientMigrationCertificate4D :
    ProgramPD9MatterSpinorCoefficientMigrationCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  variationModule := inferInstance
  zeroVariation := 0

theorem programPD9MatterSpinorCoefficientMigrationCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorCoefficientMigrationCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorCoefficientMigrationCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
end JanusFormal
