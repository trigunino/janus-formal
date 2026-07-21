import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSectionNoGo4D

/-! # Smooth cover presentation of throat matter-spinor sections

Matter fields are replaced by smooth cover coefficients satisfying the exact
deck-equivariance law of the pulled-back spinor bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-- A smooth coefficient upstairs with exactly the spinorial deck law. -/
structure SmoothThroatMatterSpinorLift (choice : NormalRootChoice) where
  toFun : ThroatCover period hPeriod → MatterFiber
  contMDiff_toFun :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, MatterFiber) ∞ toFun
  deck_equivariant : ∀ (winding : Int) (anchor : ThroatCover period hPeriod),
    toFun (winding +ᵥ anchor) =
      throatAmbientPinCMatterCoordChange period hPeriod choice
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatCoverInclusion period hPeriod (winding +ᵥ anchor))
        (mappingTorusMk (ThroatData period hPeriod) anchor) (toFun anchor)

instance (choice : NormalRootChoice) :
    CoeFun (SmoothThroatMatterSpinorLift period hPeriod choice)
      (fun _ => ThroatCover period hPeriod → MatterFiber) :=
  ⟨SmoothThroatMatterSpinorLift.toFun⟩

@[ext] theorem SmoothThroatMatterSpinorLift.ext
    {choice : NormalRootChoice}
    {first second : SmoothThroatMatterSpinorLift period hPeriod choice}
    (hEqual : ∀ anchor, first anchor = second anchor) : first = second := by
  cases first
  cases second
  congr
  exact funext hEqual

theorem throatAmbientPinCMatterCoordChange_zero
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : MappingTorus (ThroatData period hPeriod)) :
    throatAmbientPinCMatterCoordChange period hPeriod choice
      first second base 0 = 0 := by
  unfold throatAmbientPinCMatterCoordChange
    canonicalAmbientPinCMatterCoordChange
    canonicalAmbientPinCHalfSpinorCoordChange
    canonicalAmbientPinCSpinorCoordChange
  rw [show matterFiberHalfSpinorLinearEquiv (0 : MatterFiber) = 0 by
      exact map_zero matterFiberHalfSpinorLinearEquiv,
    show ambientHalfSpinorEmbed (0 : AmbientHalfSpinor2) = 0 by
      exact map_zero ambientHalfSpinorEmbedLinear,
    Matrix.mulVec_zero,
    show ambientHalfSpinorProject (0 : AmbientDiracSpinor4) = 0 by
      exact map_zero ambientHalfSpinorProjectLinear,
    map_zero]

instance (choice : NormalRootChoice) :
    Zero (SmoothThroatMatterSpinorLift period hPeriod choice) where
  zero :=
    { toFun := fun _ => 0
      contMDiff_toFun := contMDiff_const
      deck_equivariant := by
        intro winding anchor
        exact (throatAmbientPinCMatterCoordChange_zero
          period hPeriod choice _ _ _).symm }

structure ProgramPThroatMatterSpinorSectionSpaceCertificate4D where
  choice : NormalRootChoice
  sectionSpace : Type
  sectionSpaceCanonical : sectionSpace =
    SmoothThroatMatterSpinorLift period hPeriod choice
  zeroSection : sectionSpace

def programPThroatMatterSpinorSectionSpaceCertificate4D :
    ProgramPThroatMatterSpinorSectionSpaceCertificate4D period hPeriod where
  choice := .positiveQuarter
  sectionSpace := SmoothThroatMatterSpinorLift period hPeriod .positiveQuarter
  sectionSpaceCanonical := rfl
  zeroSection := 0

theorem programPThroatMatterSpinorSectionSpaceCertificate4D_nonempty :
    Nonempty (ProgramPThroatMatterSpinorSectionSpaceCertificate4D
      period hPeriod) :=
  ⟨programPThroatMatterSpinorSectionSpaceCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
end JanusFormal
