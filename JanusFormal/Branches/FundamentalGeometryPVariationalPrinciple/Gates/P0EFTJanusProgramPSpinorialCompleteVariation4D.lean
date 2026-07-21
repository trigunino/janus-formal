import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D

/-! # Complete Program-P variations with genuine spinorial matter -/

namespace JanusFormal
namespace P0EFTJanusProgramPSpinorialCompleteVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LegacyMatterVariation :=
  SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber

def completeVariationLegacyMatterProjection :
    ProgramPCompleteVariation4D period hPeriod →ₗ[Real]
      LegacyMatterVariation period hPeriod where
  toFun variation := variation.independent.matter
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev MatterFreeCompleteVariation :=
  LinearMap.ker (completeVariationLegacyMatterProjection period hPeriod)

/-- Transitional complete tangent: all legacy non-matter components plus the
new pair of genuine spinorial matter sections. -/
abbrev SpinorialCompleteVariation (choice : NormalRootChoice) :=
  MatterFreeCompleteVariation period hPeriod ×
    D9SpinorialMatterVariation period hPeriod choice

def SpinorialCompleteVariation.legacy
    {choice : NormalRootChoice}
    (variation : SpinorialCompleteVariation period hPeriod choice) :
    ProgramPCompleteVariation4D period hPeriod :=
  variation.1.1

def SpinorialCompleteVariation.matter
    {choice : NormalRootChoice}
    (variation : SpinorialCompleteVariation period hPeriod choice) :
    D9SpinorialMatterVariation period hPeriod choice :=
  variation.2

@[simp] theorem SpinorialCompleteVariation.legacy_matter_eq_zero
    {choice : NormalRootChoice}
    (variation : SpinorialCompleteVariation period hPeriod choice) :
    variation.legacy.independent.matter = 0 :=
  variation.1.2

def pureSpinorialMatterCompleteVariation
    (choice : NormalRootChoice)
    (matter : D9SpinorialMatterVariation period hPeriod choice) :
    SpinorialCompleteVariation period hPeriod choice :=
  ⟨0, matter⟩

@[simp] theorem pureSpinorialMatterCompleteVariation_matter
    (choice : NormalRootChoice)
    (matter : D9SpinorialMatterVariation period hPeriod choice) :
    (pureSpinorialMatterCompleteVariation period hPeriod choice matter).matter =
      matter :=
  rfl

structure ProgramPSpinorialCompleteVariationCertificate4D where
  choice : NormalRootChoice
  variationModule : Module Real
    (SpinorialCompleteVariation period hPeriod choice)
  zeroVariation : SpinorialCompleteVariation period hPeriod choice
  legacyMatterVanishing :
    zeroVariation.legacy.independent.matter = 0

def programPSpinorialCompleteVariationCertificate4D :
    ProgramPSpinorialCompleteVariationCertificate4D period hPeriod where
  choice := .positiveQuarter
  variationModule := inferInstance
  zeroVariation := 0
  legacyMatterVanishing := by simp

theorem programPSpinorialCompleteVariationCertificate4D_nonempty :
    Nonempty (ProgramPSpinorialCompleteVariationCertificate4D
      period hPeriod) :=
  ⟨programPSpinorialCompleteVariationCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPSpinorialCompleteVariation4D
end JanusFormal
