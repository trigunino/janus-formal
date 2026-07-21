import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D

/-!
# Flat cover connection for the smooth D9 spinor bundle

The ordinary manifold derivative on the cover obeys the exact deck covariance
law required of the canonical flat connection.  This gate does not yet package
that law as a global bundled covariant derivative or add Clifford action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Bundle ContinuousLinearMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
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

def d9MatterSpinorFlatCoverDerivative
    (choice : NormalRootChoice)
    (spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    ThroatCoverCoordinates →L[Real] MatterFiber :=
  mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
    spinorSection point

@[simp] theorem d9MatterSpinorFlatCoverDerivative_apply
    (choice : NormalRootChoice)
    (spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection point =
      mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
        spinorSection point := rfl

theorem d9MatterSpinorFlatCoverDerivative_deck_equivariant
    (choice : NormalRootChoice)
    (spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice)
    (winding : Int) (point : ThroatCover period hPeriod) :
    (d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection
        (winding +ᵥ point)).comp
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·) point) =
      (d9MatterSpinorMonodromyCLM choice winding).comp
        (d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection
          point) := by
  have hSectionAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) spinorSection point :=
    spinorSection.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSectionDeckAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) spinorSection (winding +ᵥ point) :=
    spinorSection.contMDiff_toFun.mdifferentiableAt (by simp)
  have hDeckAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners (winding +ᵥ ·) point :=
    (fixedThroatCover_deck_contMDiff period hPeriod winding).mdifferentiableAt
      (by simp)
  have hMonodromySmooth : ContMDiff 𝓘(Real, MatterFiber)
      𝓘(Real, MatterFiber) 1 (d9MatterSpinorMonodromyCLM choice winding) :=
    (d9MatterSpinorMonodromyCLM choice winding).contDiff.contMDiff
  have hMonodromyAt : MDifferentiableAt 𝓘(Real, MatterFiber)
      𝓘(Real, MatterFiber) (d9MatterSpinorMonodromyCLM choice winding)
      (spinorSection point) :=
    hMonodromySmooth.mdifferentiableAt one_ne_zero
  have hLeft :
      (d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection
          (winding +ᵥ point)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·) point) =
        mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
          (spinorSection ∘ (winding +ᵥ ·)) point :=
    (mfderiv_comp point hSectionDeckAt hDeckAt).symm
  have hCongr :
      mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
          (spinorSection ∘ (winding +ᵥ ·)) point =
        mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
          (d9MatterSpinorMonodromyCLM choice winding ∘ spinorSection) point := by
    apply mfderiv_congr
    funext current
    exact SmoothThroatMatterSpinorLift.deck_monodromy
      period hPeriod choice spinorSection winding current
  have hRight :
      mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
          (d9MatterSpinorMonodromyCLM choice winding ∘ spinorSection) point =
        (d9MatterSpinorMonodromyCLM choice winding).comp
          (d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection
            point) := by
    rw [mfderiv_comp point hMonodromyAt hSectionAt]
    simp only [d9MatterSpinorFlatCoverDerivative_apply,
      mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  exact hLeft.trans (hCongr.trans hRight)

structure ProgramPD9MatterSpinorFlatCoverConnectionCertificate4D where
  choice : NormalRootChoice
  spinorSection : SmoothThroatMatterSpinorLift period hPeriod choice
  derivative : ThroatCover period hPeriod →
    (ThroatCoverCoordinates →L[Real] MatterFiber)
  derivativeCanonical : derivative =
    d9MatterSpinorFlatCoverDerivative period hPeriod choice spinorSection
  deckEquivariant : ∀ winding point,
    (derivative (winding +ᵥ point)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·) point) =
      (d9MatterSpinorMonodromyCLM choice winding).comp (derivative point)

def programPD9MatterSpinorFlatCoverConnectionCertificate4D :
    ProgramPD9MatterSpinorFlatCoverConnectionCertificate4D period hPeriod where
  choice := .positiveQuarter
  spinorSection := 0
  derivative := d9MatterSpinorFlatCoverDerivative
    period hPeriod .positiveQuarter 0
  derivativeCanonical := rfl
  deckEquivariant := d9MatterSpinorFlatCoverDerivative_deck_equivariant
    period hPeriod .positiveQuarter 0

theorem programPD9MatterSpinorFlatCoverConnectionCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorFlatCoverConnectionCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorFlatCoverConnectionCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
end JanusFormal
