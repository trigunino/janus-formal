import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D

/-! # Smooth invariant pairing of genuine D9 matter-spinor sections -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorActualBundle4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
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

theorem d9MatterSpinorHermitianPairing_eq_two_coordinates
    (first second : MatterFiber) :
    d9MatterSpinorHermitianPairing first second =
      (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv first 0) *
          matterFiberHalfSpinorLinearEquiv second 0 +
        (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv first 1) *
          matterFiberHalfSpinorLinearEquiv second 1 := by
  simp [d9MatterSpinorHermitianPairing,
    ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    Fin.sum_univ_succ]

private def matterToHalfSpinorCLM :
    MatterFiber →L[Real] AmbientHalfSpinor2 :=
  LinearMap.toContinuousLinearMap matterFiberHalfSpinorLinearEquiv.toLinearMap

private def halfSpinorCoordinateCLM (index : Fin 2) :
    AmbientHalfSpinor2 →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun spinor => spinor index
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem d9MatterSpinorSectionPairing_contMDiff
    (choice : NormalRootChoice)
    (first second : SmoothThroatMatterSpinorLift period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (fun anchor => d9MatterSpinorHermitianPairing
        (first anchor) (second anchor)) := by
  have hFirstHalf : ContMDiff throatCoverModelWithCorners
      𝓘(Real, AmbientHalfSpinor2) ∞
      (fun anchor => matterFiberHalfSpinorLinearEquiv (first anchor)) :=
    matterToHalfSpinorCLM.contMDiff.comp first.contMDiff_toFun
  have hSecondHalf : ContMDiff throatCoverModelWithCorners
      𝓘(Real, AmbientHalfSpinor2) ∞
      (fun anchor => matterFiberHalfSpinorLinearEquiv (second anchor)) :=
    matterToHalfSpinorCLM.contMDiff.comp second.contMDiff_toFun
  have hCoordinate (index : Fin 2) : ContMDiff throatCoverModelWithCorners
      𝓘(Real, Complex) ∞
      (fun anchor =>
        (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
          (first anchor) index) *
        matterFiberHalfSpinorLinearEquiv (second anchor) index) := by
    have hFirst := (halfSpinorCoordinateCLM index).contMDiff.comp hFirstHalf
    have hSecond := (halfSpinorCoordinateCLM index).contMDiff.comp hSecondHalf
    have hConj :=
      Complex.conjCLE.toContinuousLinearMap.contMDiff.comp hFirst
    have hMul : ContMDiff throatCoverModelWithCorners
        𝓘(Real, Complex →L[Real] Complex) ∞
        (fun anchor => ContinuousLinearMap.mul Real Complex
          ((starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
            (first anchor) index))) :=
      (ContinuousLinearMap.mul Real Complex).contMDiff.comp hConj
    exact hMul.clm_apply hSecond
  rw [show (fun anchor => d9MatterSpinorHermitianPairing
      (first anchor) (second anchor)) = fun anchor =>
        (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
          (first anchor) 0) * matterFiberHalfSpinorLinearEquiv
            (second anchor) 0 +
        (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
          (first anchor) 1) * matterFiberHalfSpinorLinearEquiv
            (second anchor) 1 by
      funext anchor
      exact d9MatterSpinorHermitianPairing_eq_two_coordinates _ _]
  exact (hCoordinate 0).add (hCoordinate 1)

theorem d9SpinorialMatterPairing_contMDiff
    (choice : NormalRootChoice)
    (first second : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (fun anchor => d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice first sector anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice second sector
          anchor)) := by
  cases sector <;>
    exact d9MatterSpinorSectionPairing_contMDiff period hPeriod choice _ _

theorem d9SpinorialMatterSelfPairing_deck_invariant
    (choice : NormalRootChoice)
    (variation : D9SpinorialMatterVariation period hPeriod choice)
    (sector : Sector) (winding : Int)
    (anchor : ThroatCover period hPeriod) :
    d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          (winding +ᵥ anchor))
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          (winding +ᵥ anchor)) =
      d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor) :=
  d9SpinorialMatterPairing_deck_invariant period hPeriod choice
    variation variation sector winding anchor

structure ProgramPD9MatterSpinorPairingSmoothCertificate4D where
  choice : NormalRootChoice
  variation : D9SpinorialMatterVariation period hPeriod choice
  pairingSmooth : ∀ sector,
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (fun anchor => d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor))
  pairingDeckInvariant : ∀ (sector : Sector) (winding : Int)
      (anchor : ThroatCover period hPeriod),
    d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          (winding +ᵥ anchor))
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          (winding +ᵥ anchor)) =
      d9MatterSpinorHermitianPairing
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)
        (d9SpinorialMatterCoefficient period hPeriod choice variation sector
          anchor)

def programPD9MatterSpinorPairingSmoothCertificate4D :
    ProgramPD9MatterSpinorPairingSmoothCertificate4D period hPeriod where
  choice := .positiveQuarter
  variation := 0
  pairingSmooth := fun sector =>
    d9SpinorialMatterPairing_contMDiff period hPeriod .positiveQuarter
      0 0 sector
  pairingDeckInvariant := fun sector winding anchor =>
    d9SpinorialMatterSelfPairing_deck_invariant period hPeriod
      .positiveQuarter 0 sector winding anchor

theorem programPD9MatterSpinorPairingSmoothCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorPairingSmoothCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorPairingSmoothCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
end JanusFormal
