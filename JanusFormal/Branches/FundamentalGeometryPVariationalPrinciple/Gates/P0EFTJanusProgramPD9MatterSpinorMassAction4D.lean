import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorRealDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-! # Canonically measured D9 spinor mass action -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorMassAction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPD9MatterSpinorRealDensity4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseCompactSpace :
    CompactSpace (ThroatBase period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) := borel _

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

theorem d9SpinorialMatterRealDensity_integrable
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) :
    Integrable
      (fun point : ThroatBase period hPeriod =>
        d9SpinorialMatterRealDensity period hPeriod choice variation sector point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact
    (d9SpinorialMatterRealDensity period hPeriod choice variation sector).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def d9SpinorialMatterMassAction
    (choice : NormalRootChoice) (massSquared : Real)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) : Real :=
  massSquared / 2 *
    ∫ point : ThroatBase period hPeriod,
      d9SpinorialMatterRealDensity period hPeriod choice variation sector point
      ∂ intrinsicCanonicalThroatVolumeMeasure period hPeriod

theorem d9SpinorialMatterMassAction_nonnegative
    (choice : NormalRootChoice) (massSquared : Real)
    (hMass : 0 ≤ massSquared)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) :
    0 ≤ d9SpinorialMatterMassAction period hPeriod choice massSquared
      variation sector := by
  unfold d9SpinorialMatterMassAction
  exact mul_nonneg (div_nonneg hMass (by norm_num))
    (integral_nonneg fun point =>
      d9SpinorialMatterRealDensity_nonnegative period hPeriod choice
        variation sector point)

@[simp] theorem d9SpinorialMatterMassAction_zero_mass
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) :
    d9SpinorialMatterMassAction period hPeriod choice 0 variation sector = 0 := by
  simp [d9SpinorialMatterMassAction]

@[simp] theorem d9SpinorialMatterMassAction_zero_variation
    (choice : NormalRootChoice) (massSquared : Real)
    (sector : Sector) :
    d9SpinorialMatterMassAction period hPeriod choice massSquared
      (0 : D9SpinorialMatterVariation period hPeriod choice) sector = 0 := by
  unfold d9SpinorialMatterMassAction
  simp

structure ProgramPD9MatterSpinorMassActionCertificate4D where
  choice : NormalRootChoice
  massSquared : Real
  massSquaredNonnegative : 0 ≤ massSquared
  variation : D9SpinorialMatterVariation period hPeriod choice
  sector : Sector
  action : Real
  actionCanonical : action = d9SpinorialMatterMassAction
    period hPeriod choice massSquared variation sector
  densityIntegrable : Integrable
    (fun point : ThroatBase period hPeriod =>
      d9SpinorialMatterRealDensity period hPeriod choice variation sector point)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  actionNonnegative : 0 ≤ action

def programPD9MatterSpinorMassActionCertificate4D :
    ProgramPD9MatterSpinorMassActionCertificate4D period hPeriod where
  choice := .positiveQuarter
  massSquared := 1
  massSquaredNonnegative := by norm_num
  variation := 0
  sector := .plus
  action := d9SpinorialMatterMassAction
    period hPeriod .positiveQuarter 1 0 .plus
  actionCanonical := rfl
  densityIntegrable := d9SpinorialMatterRealDensity_integrable
    period hPeriod .positiveQuarter 0 .plus
  actionNonnegative := d9SpinorialMatterMassAction_nonnegative
    period hPeriod .positiveQuarter 1 (by norm_num) 0 .plus

theorem programPD9MatterSpinorMassActionCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorMassActionCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorMassActionCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorMassAction4D
end JanusFormal
