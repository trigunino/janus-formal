import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D

/-! # Flat cover connection for the doubled smooth D9 spinor bundle -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Bundle ContinuousLinearMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
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

def d9DoubledMatterSpinorFlatCoverDerivative
    (choice : NormalRootChoice)
    (spinorSection :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber :=
  mfderiv throatCoverModelWithCorners
    𝓘(Real, D9DoubledMatterFiber) spinorSection point

@[simp] theorem d9DoubledMatterSpinorFlatCoverDerivative_apply
    (choice : NormalRootChoice)
    (spinorSection :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9DoubledMatterSpinorFlatCoverDerivative
        period hPeriod choice spinorSection point =
      mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) spinorSection point := rfl

theorem d9DoubledMatterSpinorFlatCoverDerivative_deck_equivariant
    (choice : NormalRootChoice)
    (spinorSection :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (winding : Int) (point : ThroatCover period hPeriod) :
    (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
        spinorSection (winding +ᵥ point)).comp
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·) point) =
      (d9DoubledMatterSpinorMonodromyCLM choice winding).comp
        (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
          spinorSection point) := by
  have hSectionAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) spinorSection point :=
    spinorSection.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSectionDeckAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) spinorSection
      (winding +ᵥ point) :=
    spinorSection.contMDiff_toFun.mdifferentiableAt (by simp)
  have hDeckAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners (winding +ᵥ ·) point :=
    (fixedThroatCover_deck_contMDiff period hPeriod winding).mdifferentiableAt
      (by simp)
  have hMonodromySmooth : ContMDiff 𝓘(Real, D9DoubledMatterFiber)
      𝓘(Real, D9DoubledMatterFiber) 1
      (d9DoubledMatterSpinorMonodromyCLM choice winding) :=
    (d9DoubledMatterSpinorMonodromyCLM choice winding).contDiff.contMDiff
  have hMonodromyAt : MDifferentiableAt
      𝓘(Real, D9DoubledMatterFiber) 𝓘(Real, D9DoubledMatterFiber)
      (d9DoubledMatterSpinorMonodromyCLM choice winding)
      (spinorSection point) :=
    hMonodromySmooth.mdifferentiableAt one_ne_zero
  have hLeft :
      (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
          spinorSection (winding +ᵥ point)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·) point) =
        mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (spinorSection ∘ (winding +ᵥ ·)) point :=
    (mfderiv_comp point hSectionDeckAt hDeckAt).symm
  have hCongr :
      mfderiv throatCoverModelWithCorners 𝓘(Real, D9DoubledMatterFiber)
          (spinorSection ∘ (winding +ᵥ ·)) point =
        mfderiv throatCoverModelWithCorners 𝓘(Real, D9DoubledMatterFiber)
          (d9DoubledMatterSpinorMonodromyCLM choice winding ∘
            spinorSection) point := by
    apply mfderiv_congr
    funext current
    exact SmoothThroatDoubledMatterSpinorLift.deck_monodromy
      period hPeriod choice spinorSection winding current
  have hRight :
      mfderiv throatCoverModelWithCorners 𝓘(Real, D9DoubledMatterFiber)
          (d9DoubledMatterSpinorMonodromyCLM choice winding ∘
            spinorSection) point =
        (d9DoubledMatterSpinorMonodromyCLM choice winding).comp
          (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
            spinorSection point) := by
    rw [mfderiv_comp point hMonodromyAt hSectionAt]
    simp only [d9DoubledMatterSpinorFlatCoverDerivative_apply,
      mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  exact hLeft.trans (hCongr.trans hRight)

def zeroSmoothThroatDoubledMatterSpinorLift
    (choice : NormalRootChoice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice where
  first := 0
  second := 0

structure ProgramPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D where
  choice : NormalRootChoice
  spinorSection : SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  derivative : ThroatCover period hPeriod →
    (ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber)
  derivativeCanonical : derivative =
    d9DoubledMatterSpinorFlatCoverDerivative
      period hPeriod choice spinorSection
  deckEquivariant : ∀ winding point,
    (derivative (winding +ᵥ point)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·) point) =
      (d9DoubledMatterSpinorMonodromyCLM choice winding).comp
        (derivative point)

def programPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D :
    ProgramPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  spinorSection := zeroSmoothThroatDoubledMatterSpinorLift
    period hPeriod .positiveQuarter
  derivative := d9DoubledMatterSpinorFlatCoverDerivative period hPeriod
    .positiveQuarter (zeroSmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter)
  derivativeCanonical := rfl
  deckEquivariant :=
    d9DoubledMatterSpinorFlatCoverDerivative_deck_equivariant
      period hPeriod .positiveQuarter
        (zeroSmoothThroatDoubledMatterSpinorLift
          period hPeriod .positiveQuarter)

theorem programPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledFlatCoverConnectionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
end JanusFormal
