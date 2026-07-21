import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorPairingDescent4D

/-! # Real nonnegative D9 spinor density on the throat -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorRealDensity4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9MatterSpinorPairingDescent4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

theorem d9MatterSpinorHermitianPairing_self_re_nonnegative
    (matter : MatterFiber) :
    0 ≤ (d9MatterSpinorHermitianPairing matter matter).re := by
  rw [d9MatterSpinorHermitianPairing_eq_two_coordinates]
  rw [← Complex.normSq_eq_conj_mul_self,
    ← Complex.normSq_eq_conj_mul_self]
  simpa using add_nonneg
    (Complex.normSq_nonneg (matterFiberHalfSpinorLinearEquiv matter 0))
    (Complex.normSq_nonneg (matterFiberHalfSpinorLinearEquiv matter 1))

def d9SpinorialMatterRealDensity
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) : SmoothThroatField period hPeriod Real where
  toFun := fun point =>
    (d9SpinorialMatterPairingThroatField period hPeriod choice variation
      sector point).re
  contMDiff_toFun :=
    Complex.reCLM.contMDiff.comp
      (d9SpinorialMatterPairingThroatField period hPeriod choice variation
        sector).contMDiff_toFun

@[simp] theorem d9SpinorialMatterRealDensity_mk
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (anchor : ThroatCover period hPeriod) :
    d9SpinorialMatterRealDensity period hPeriod choice variation sector
        (mappingTorusMk (ThroatData period hPeriod) anchor) =
      (d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)).re :=
  rfl

theorem d9SpinorialMatterRealDensity_nonnegative
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (point : MappingTorus (ThroatData period hPeriod)) :
    0 ≤ d9SpinorialMatterRealDensity period hPeriod choice variation sector
      point := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) point
  rw [d9SpinorialMatterRealDensity_mk]
  exact d9MatterSpinorHermitianPairing_self_re_nonnegative _

@[simp] theorem d9SpinorialMatterRealDensity_zero
    (choice : NormalRootChoice) (sector : Sector)
    (point : MappingTorus (ThroatData period hPeriod)) :
    d9SpinorialMatterRealDensity period hPeriod choice
      (0 : D9SpinorialMatterVariation period hPeriod choice) sector point = 0 := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) point
  simp [d9SpinorialMatterRealDensity_mk,
    d9MatterSpinorHermitianPairing, ambientHalfSpinorHermitianPairing,
    ambientHalfSpinorEmbed,
    P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D.ambientPinCSpinorHermitianPairing]

structure ProgramPD9MatterSpinorRealDensityCertificate4D where
  choice : NormalRootChoice
  variation : D9SpinorialMatterVariation period hPeriod choice
  sector : Sector
  density : SmoothThroatField period hPeriod Real
  densityCanonical : density =
    d9SpinorialMatterRealDensity period hPeriod choice variation sector
  densityNonnegative : ∀ point, 0 ≤ density point

def programPD9MatterSpinorRealDensityCertificate4D :
    ProgramPD9MatterSpinorRealDensityCertificate4D period hPeriod where
  choice := .positiveQuarter
  variation := 0
  sector := .plus
  density := d9SpinorialMatterRealDensity
    period hPeriod .positiveQuarter 0 .plus
  densityCanonical := rfl
  densityNonnegative := d9SpinorialMatterRealDensity_nonnegative
    period hPeriod .positiveQuarter 0 .plus

theorem programPD9MatterSpinorRealDensityCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorRealDensityCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorRealDensityCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorRealDensity4D
end JanusFormal
