import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorPairingDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-! # Canonically measured intrinsic D9 doubled-spinor Dirac action -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledDiracAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9MatterSpinorPairingDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

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

private def plusPacket
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice) :
    D9SpinorialMatterVariation period hPeriod choice :=
  (lift, 0)

/-- Cover pairing `⟨ψ,Dψ⟩` in both halves of the doubled Clifford module. -/
def d9DoubledMatterDiracPairingCoverField
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    SmoothDeckInvariantThroatField period hPeriod Complex where
  toFun := fun anchor =>
    d9MatterSpinorHermitianPairing
        (lift.first anchor)
        ((d9LeviCivitaSpinDiracLift
          period hPeriod choice lift).first anchor) +
      d9MatterSpinorHermitianPairing
        (lift.second anchor)
        ((d9LeviCivitaSpinDiracLift
          period hPeriod choice lift).second anchor)
  contMDiff_toFun := by
    exact
      (d9MatterSpinorSectionPairing_contMDiff period hPeriod choice
        lift.first
        (d9LeviCivitaSpinDiracLift
          period hPeriod choice lift).first).add
      (d9MatterSpinorSectionPairing_contMDiff period hPeriod
        (oppositeRoot choice) lift.second
        (d9LeviCivitaSpinDiracLift
          period hPeriod choice lift).second)
  deck_invariant := by
    intro winding anchor
    have hFirst :=
      d9SpinorialMatterPairing_deck_invariant period hPeriod choice
        (plusPacket period hPeriod choice lift.first)
        (plusPacket period hPeriod choice
          (d9LeviCivitaSpinDiracLift
            period hPeriod choice lift).first)
        .plus winding anchor
    have hSecond :=
      d9SpinorialMatterPairing_deck_invariant period hPeriod
        (oppositeRoot choice)
        (plusPacket period hPeriod (oppositeRoot choice) lift.second)
        (plusPacket period hPeriod (oppositeRoot choice)
          (d9LeviCivitaSpinDiracLift
            period hPeriod choice lift).second)
        .plus winding anchor
    exact congrArg₂ (· + ·) hFirst hSecond

/-- Smooth quotient field of the intrinsic doubled Dirac pairing. -/
def d9DoubledMatterDiracPairingThroatField
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    SmoothThroatField period hPeriod Complex :=
  descendSmoothThroat period hPeriod
    (d9DoubledMatterDiracPairingCoverField period hPeriod choice lift)

/-- Real smooth kinetic density used by the physical action. -/
def d9DoubledMatterDiracRealDensity
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    SmoothThroatField period hPeriod Real where
  toFun := fun point =>
    (d9DoubledMatterDiracPairingThroatField
      period hPeriod choice lift point).re
  contMDiff_toFun :=
    Complex.reCLM.contMDiff.comp
      (d9DoubledMatterDiracPairingThroatField
        period hPeriod choice lift).contMDiff_toFun

@[simp]
theorem d9DoubledMatterDiracRealDensity_mk
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod) :
    d9DoubledMatterDiracRealDensity period hPeriod choice lift
        (mappingTorusMk (ThroatData period hPeriod) anchor) =
      (d9MatterSpinorHermitianPairing
          (lift.first anchor)
          ((d9LeviCivitaSpinDiracLift
            period hPeriod choice lift).first anchor) +
        d9MatterSpinorHermitianPairing
          (lift.second anchor)
          ((d9LeviCivitaSpinDiracLift
            period hPeriod choice lift).second anchor)).re :=
  rfl

theorem d9DoubledMatterDiracRealDensity_integrable
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    Integrable
      (d9DoubledMatterDiracRealDensity period hPeriod choice lift)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact
    (d9DoubledMatterDiracRealDensity period hPeriod choice lift)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Genuine integrated `Re ⟨ψ,Dψ⟩` action on the actual doubled D9 bundle. -/
def d9DoubledMatterDiracAction
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    Real :=
  ∫ point : ThroatBase period hPeriod,
    d9DoubledMatterDiracRealDensity period hPeriod choice lift point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod

end
end P0EFTJanusProgramPD9MatterSpinorDoubledDiracAction4D
end JanusFormal
