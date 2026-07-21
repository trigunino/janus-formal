import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothThroatTrace4D

/-! # Smooth descent of the D9 spinor pairing to the throat quotient -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorPairingDescent4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
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

universe u

structure SmoothDeckInvariantThroatField
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  toFun : ThroatCover period hPeriod → Fiber
  contMDiff_toFun :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Fiber) ∞ toFun
  deck_invariant : ∀ (winding : Int) (anchor : ThroatCover period hPeriod),
    toFun (winding +ᵥ anchor) = toFun anchor

instance {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    CoeFun (SmoothDeckInvariantThroatField period hPeriod Fiber)
      (fun _ => ThroatCover period hPeriod → Fiber) :=
  ⟨SmoothDeckInvariantThroatField.toFun⟩

def descendThroat
    {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothDeckInvariantThroatField period hPeriod Fiber) :
    ThroatBase period hPeriod → Fiber :=
  Quotient.lift field.toFun (fun first second hOrbit => by
    change AddAction.orbitRel Int (ThroatCover period hPeriod)
      first second at hOrbit
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
    rcases hOrbit with ⟨winding, hWinding⟩
    rw [← hWinding]
    exact field.deck_invariant winding second)

@[simp] theorem descendThroat_mk
    {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothDeckInvariantThroatField period hPeriod Fiber)
    (anchor : ThroatCover period hPeriod) :
    descendThroat period hPeriod field
      (mappingTorusMk (ThroatData period hPeriod) anchor) = field anchor :=
  rfl

theorem contMDiff_descendThroat
    {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothDeckInvariantThroatField period hPeriod Fiber) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Fiber) ∞
      (descendThroat period hPeriod field) := by
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) quotientPoint
  have hAt := fixedThroat_projection_isLocalDiffeomorph
    period hPeriod anchor
  have hLocal : ContMDiffAt throatCoverModelWithCorners 𝓘(Real, Fiber) ∞
      (field.toFun ∘ hAt.localInverse)
      (mappingTorusMk (ThroatData period hPeriod) anchor) :=
    field.contMDiff_toFun.contMDiffAt.comp _
      (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  change descendThroat period hPeriod field point = field (hAt.localInverse point)
  have hPoint' :
      mappingTorusMk (ThroatData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    descendThroat period hPeriod field point =
        descendThroat period hPeriod field
          (mappingTorusMk (ThroatData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = field (hAt.localInverse point) :=
      descendThroat_mk period hPeriod field _

def descendSmoothThroat
    {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothDeckInvariantThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber where
  toFun := descendThroat period hPeriod field
  contMDiff_toFun := contMDiff_descendThroat period hPeriod field

def d9SpinorialMatterPairingCoverField
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) :
    SmoothDeckInvariantThroatField period hPeriod Complex where
  toFun := fun anchor => d9MatterSpinorHermitianPairing
    (d9SpinorialMatterCoefficient period hPeriod choice variation sector anchor)
    (d9SpinorialMatterCoefficient period hPeriod choice variation sector anchor)
  contMDiff_toFun := d9SpinorialMatterPairing_contMDiff
    period hPeriod choice variation variation sector
  deck_invariant := d9SpinorialMatterSelfPairing_deck_invariant
    period hPeriod choice variation sector

def d9SpinorialMatterPairingThroatField
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) : SmoothThroatField period hPeriod Complex :=
  descendSmoothThroat period hPeriod
    (d9SpinorialMatterPairingCoverField period hPeriod choice variation sector)

@[simp] theorem d9SpinorialMatterPairingThroatField_mk
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (anchor : ThroatCover period hPeriod) :
    d9SpinorialMatterPairingThroatField period hPeriod choice variation sector
        (mappingTorusMk (ThroatData period hPeriod) anchor) =
      d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor) :=
  rfl

structure ProgramPD9MatterSpinorPairingDescentCertificate4D where
  choice : NormalRootChoice
  variation : D9SpinorialMatterVariation period hPeriod choice
  sector : Sector
  descendedPairing : SmoothThroatField period hPeriod Complex
  descendedPairingCanonical : descendedPairing =
    d9SpinorialMatterPairingThroatField period hPeriod choice variation sector

def programPD9MatterSpinorPairingDescentCertificate4D :
    ProgramPD9MatterSpinorPairingDescentCertificate4D period hPeriod where
  choice := .positiveQuarter
  variation := 0
  sector := .plus
  descendedPairing := d9SpinorialMatterPairingThroatField
    period hPeriod .positiveQuarter 0 .plus
  descendedPairingCanonical := rfl

theorem programPD9MatterSpinorPairingDescentCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorPairingDescentCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorPairingDescentCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorPairingDescent4D
end JanusFormal
