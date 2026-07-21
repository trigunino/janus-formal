import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinorialCompleteVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationD9FieldAssembly4D

/-! # D9 assembly from the spinorial complete variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

/-- First migrated consumer: all non-matter entries reuse the matter-free
legacy tangent, while the spinor entry comes from the genuine section. -/
def spinorialCompleteVariationD9Field
    {Spinor : Type*}
    (choice : NormalRootChoice)
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) : CompleteLocalField Spinor where
  bosonic :=
    { normalMode := variation.legacy.normalModeAt period hPeriod sector
        (mappingTorusMk (ThroatData period hPeriod) anchor)
      gaugeOneForm := d9GaugeOneForm period hPeriod
        variation.legacy.independent sector column
        (mappingTorusMk (ThroatData period hPeriod) anchor)
      metricPerturbation := variation.legacy.metricPerturbationAt
        period hPeriod sector
        (mappingTorusMk (ThroatData period hPeriod) anchor) }
  ghosts :=
    { u1Ghost := d9U1Ghost period hPeriod variation.legacy.independent
        sector column (mappingTorusMk (ThroatData period hPeriod) anchor)
      diffeomorphismGhost := variation.legacy.diffeomorphismGhostAt
        period hPeriod sector
        (mappingTorusMk (ThroatData period hPeriod) anchor) }
  spinor := matterSpinorIdentification
    (d9SpinorialMatterCoefficient period hPeriod choice variation.matter
      sector anchor)

@[simp] theorem spinorialCompleteVariationD9Field_spinor
    {Spinor : Type*}
    (choice : NormalRootChoice)
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialCompleteVariationD9Field period hPeriod choice
      matterSpinorIdentification variation sector column anchor).spinor =
      matterSpinorIdentification
        (d9SpinorialMatterCoefficient period hPeriod choice variation.matter
          sector anchor) :=
  rfl

@[simp] theorem spinorialCompleteVariationD9Field_bosonic_eq_legacy
    {Spinor : Type*}
    (choice : NormalRootChoice)
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialCompleteVariationD9Field period hPeriod choice
      matterSpinorIdentification variation sector column anchor).bosonic =
      (P0EFTJanusCompleteVariationD9FieldAssembly4D.completeVariationD9Field
        period hPeriod matterSpinorIdentification variation.legacy sector column
        (mappingTorusMk (ThroatData period hPeriod) anchor)).bosonic :=
  rfl

@[simp] theorem spinorialCompleteVariationD9Field_ghosts_eq_legacy
    {Spinor : Type*}
    (choice : NormalRootChoice)
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialCompleteVariationD9Field period hPeriod choice
      matterSpinorIdentification variation sector column anchor).ghosts =
      (P0EFTJanusCompleteVariationD9FieldAssembly4D.completeVariationD9Field
        period hPeriod matterSpinorIdentification variation.legacy sector column
        (mappingTorusMk (ThroatData period hPeriod) anchor)).ghosts :=
  rfl

structure ProgramPSpinorialCompleteVariationD9FieldAssemblyCertificate4D where
  choice : NormalRootChoice
  variation : SpinorialCompleteVariation period hPeriod choice
  legacyMatterVanishing : variation.legacy.independent.matter = 0

def programPSpinorialCompleteVariationD9FieldAssemblyCertificate4D :
    ProgramPSpinorialCompleteVariationD9FieldAssemblyCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  variation := 0
  legacyMatterVanishing := by simp

theorem programPSpinorialCompleteVariationD9FieldAssemblyCertificate4D_nonempty :
    Nonempty (ProgramPSpinorialCompleteVariationD9FieldAssemblyCertificate4D
      period hPeriod) :=
  ⟨programPSpinorialCompleteVariationD9FieldAssemblyCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D
end JanusFormal
