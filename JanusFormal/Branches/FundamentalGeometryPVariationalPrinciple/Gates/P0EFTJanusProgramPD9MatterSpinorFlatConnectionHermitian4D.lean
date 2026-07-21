import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D

/-!
# Hermitian compatibility of the flat D9 spinor connection

The cover derivative obeys the exact Hermitian Leibniz identity.  Global
bundled covariant-derivative packaging and Clifford action are not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
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

private def halfCoordinateCLM (index : Fin 2) :
    MatterFiber →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matter => matterFiberHalfSpinorLinearEquiv matter index
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }

theorem d9MatterSpinorFlatCoverDerivative_pairing_compatible
    (choice : NormalRootChoice)
    (first second : SmoothThroatMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) (tangent : ThroatCoverCoordinates) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor => d9MatterSpinorHermitianPairing
          (first anchor) (second anchor)) point tangent =
      d9MatterSpinorHermitianPairing (first point)
          (d9MatterSpinorFlatCoverDerivative period hPeriod choice second point
            tangent) +
        d9MatterSpinorHermitianPairing
          (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point
            tangent)
          (second point) := by
  have hFirst : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) first point :=
    first.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSecond : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) second point :=
    second.contMDiff_toFun.mdifferentiableAt (by simp)
  have hFirstCoordinate (index : Fin 2) : HasMFDerivAt
      throatCoverModelWithCorners 𝓘(Real, Complex)
      (fun anchor => halfCoordinateCLM index (first anchor)) point
      ((halfCoordinateCLM index).comp
        (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point)) := by
    convert (halfCoordinateCLM index).hasFDerivAt.hasMFDerivAt.comp point
      hFirst.hasMFDerivAt using 1 <;>
        simp [Function.comp_def, d9MatterSpinorFlatCoverDerivative_apply] <;> rfl
  have hSecondCoordinate (index : Fin 2) : HasMFDerivAt
      throatCoverModelWithCorners 𝓘(Real, Complex)
      (fun anchor => halfCoordinateCLM index (second anchor)) point
      ((halfCoordinateCLM index).comp
        (d9MatterSpinorFlatCoverDerivative period hPeriod choice second point)) := by
    convert (halfCoordinateCLM index).hasFDerivAt.hasMFDerivAt.comp point
      hSecond.hasMFDerivAt using 1 <;>
        simp [Function.comp_def, d9MatterSpinorFlatCoverDerivative_apply] <;> rfl
  let conjCLM : Complex →L[Real] Complex :=
    Complex.conjCLE.toContinuousLinearMap
  have hFirstConjugate (index : Fin 2) : HasMFDerivAt
      throatCoverModelWithCorners 𝓘(Real, Complex)
      (fun anchor => conjCLM (halfCoordinateCLM index (first anchor))) point
      (conjCLM.comp ((halfCoordinateCLM index).comp
        (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point))) := by
    convert conjCLM.hasFDerivAt.hasMFDerivAt.comp point
      (hFirstCoordinate index) using 1 <;> simp [Function.comp_def] <;> rfl
  have hTerm (index : Fin 2) :=
    (hFirstConjugate index).mul (hSecondCoordinate index)
  have hSum := (hTerm 0).add (hTerm 1)
  have hPairing := hSum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun anchor =>
      d9MatterSpinorHermitianPairing_eq_two_coordinates
        (first anchor) (second anchor))
  rw [hPairing.mfderiv]
  change
    (((starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv (first point) 0) *
          matterFiberHalfSpinorLinearEquiv
            (d9MatterSpinorFlatCoverDerivative period hPeriod choice second point
              tangent) 0 +
        matterFiberHalfSpinorLinearEquiv (second point) 0 *
          (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
            (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point
              tangent) 0)) +
      ((starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv (first point) 1) *
          matterFiberHalfSpinorLinearEquiv
            (d9MatterSpinorFlatCoverDerivative period hPeriod choice second point
              tangent) 1 +
        matterFiberHalfSpinorLinearEquiv (second point) 1 *
          (starRingEnd Complex) (matterFiberHalfSpinorLinearEquiv
            (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point
              tangent) 1))) = _
  rw [d9MatterSpinorHermitianPairing_eq_two_coordinates,
    d9MatterSpinorHermitianPairing_eq_two_coordinates]
  ring

structure ProgramPD9MatterSpinorFlatConnectionHermitianCertificate4D where
  choice : NormalRootChoice
  first : SmoothThroatMatterSpinorLift period hPeriod choice
  second : SmoothThroatMatterSpinorLift period hPeriod choice
  pairingCompatible : ∀ point tangent,
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor => d9MatterSpinorHermitianPairing
          (first anchor) (second anchor)) point tangent =
      d9MatterSpinorHermitianPairing (first point)
          (d9MatterSpinorFlatCoverDerivative period hPeriod choice second point
            tangent) +
        d9MatterSpinorHermitianPairing
          (d9MatterSpinorFlatCoverDerivative period hPeriod choice first point
            tangent)
          (second point)

def programPD9MatterSpinorFlatConnectionHermitianCertificate4D :
    ProgramPD9MatterSpinorFlatConnectionHermitianCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  first := 0
  second := 0
  pairingCompatible :=
    d9MatterSpinorFlatCoverDerivative_pairing_compatible
      period hPeriod .positiveQuarter 0 0

theorem programPD9MatterSpinorFlatConnectionHermitianCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorFlatConnectionHermitianCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorFlatConnectionHermitianCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D
end JanusFormal
