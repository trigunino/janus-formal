import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D

/-! # Spinorial refinement of the common D9 domain contract -/

namespace JanusFormal
namespace P0EFTJanusProgramPSpinorialD9DomainAgreementRefinement4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

def spinorialAgreementD9Field
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain)
    (choice : NormalRootChoice)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) : CompleteLocalField Spinor :=
  spinorialCompleteVariationD9Field period hPeriod choice
    agreement.matterSpinorIdentification variation sector column anchor

@[simp] theorem spinorialAgreementD9Field_normalMode
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain)
    (choice : NormalRootChoice)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialAgreementD9Field period hPeriod agreement choice variation
      sector column anchor).bosonic.normalMode =
      variation.legacy.normalModeAt period hPeriod sector
        (mappingTorusMk (ThroatData period hPeriod) anchor) :=
  rfl

@[simp] theorem spinorialAgreementD9Field_gaugeOneForm
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain)
    (choice : NormalRootChoice)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialAgreementD9Field period hPeriod agreement choice variation
      sector column anchor).bosonic.gaugeOneForm =
      d9GaugeOneForm period hPeriod variation.legacy.independent sector column
        (mappingTorusMk (ThroatData period hPeriod) anchor) :=
  rfl

@[simp] theorem spinorialAgreementD9Field_spinor
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain)
    (choice : NormalRootChoice)
    (variation : SpinorialCompleteVariation period hPeriod choice)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (spinorialAgreementD9Field period hPeriod agreement choice variation
      sector column anchor).spinor =
      agreement.matterSpinorIdentification
        (d9SpinorialMatterCoefficient period hPeriod choice variation.matter
          sector anchor) :=
  rfl

structure SpinorialD9DomainAgreementRefinement4D
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain) where
  choice : NormalRootChoice
  actionTangentD9Field :
    SpinorialCompleteVariation period hPeriod choice → Sector → Fin 2 →
      ThroatCover period hPeriod → CompleteLocalField Spinor
  actionTangentD9FieldCanonical : actionTangentD9Field =
    spinorialAgreementD9Field period hPeriod agreement choice

def spinorialD9DomainAgreementRefinement4D
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain)
    (choice : NormalRootChoice) :
    SpinorialD9DomainAgreementRefinement4D period hPeriod agreement where
  choice := choice
  actionTangentD9Field :=
    spinorialAgreementD9Field period hPeriod agreement choice
  actionTangentD9FieldCanonical := rfl

theorem spinorialD9DomainAgreementRefinement4D_nonempty
    {Spinor : Type*}
    {domain : ProgramPCommonGeometricDomain4D period hPeriod}
    (agreement : RemainingProgramPD7D9D10DomainAgreement4D
      period hPeriod Spinor domain) :
    Nonempty (SpinorialD9DomainAgreementRefinement4D
      period hPeriod agreement) :=
  ⟨spinorialD9DomainAgreementRefinement4D period hPeriod agreement
    .positiveQuarter⟩

end
end P0EFTJanusProgramPSpinorialD9DomainAgreementRefinement4D
end JanusFormal
