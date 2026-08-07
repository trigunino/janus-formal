import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCConnection4D

/-!
# Hermitian compatibility of the primitive SpinC connection

The flat doubled derivative already satisfies the exact Hermitian Leibniz
identity. The remaining connection terms are algebraic:

* the Levi--Civita spin correction is a real linear combination of products
  `γᵢγⱼ`, `i ≠ j`;
* the monopole correction is a real multiple of the infinitesimal `U(1)`
  action.

The explicit Clifford skew-adjointness proves both corrections are
skew-Hermitian, so they cancel in the derivative of the fiber pairing. This
file packages that cancellation for the full local primitive SpinC connection.
No Stokes theorem, boundary condition, spectral assumption or D10 direction is
used here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCConnectionHermitian4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-! ## Elementary scalar and `U(1)` signs -/

/-- Real scalars may be pulled from the left slot of the doubled Hermitian
pairing. -/
theorem d9DoubledMatterSpinorHermitianPairing_real_smul_left
    (scalar : Real) (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing (scalar • first) second =
      (scalar : Complex) *
        d9DoubledMatterSpinorHermitianPairing first second := by
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    Fin.sum_univ_succ]
  ring

/-- Real scalars may be pulled from the right slot. -/
theorem d9DoubledMatterSpinorHermitianPairing_real_smul_right
    (scalar : Real) (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first (scalar • second) =
      (scalar : Complex) *
        d9DoubledMatterSpinorHermitianPairing first second := by
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    Fin.sum_univ_succ]
  ring

private theorem d9PrimitiveSpinCImaginaryAction_eq_complexI
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction matter =
      d9PrimitiveSpinCComplexActionCLM Complex.I matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCImaginaryPhase_coe]

/-- The infinitesimal primitive `U(1)` action is skew-Hermitian. -/
theorem d9DoubledMatterSpinorHermitianPairing_imaginaryAction
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCImaginaryAction first) second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9PrimitiveSpinCImaginaryAction second) := by
  rw [d9PrimitiveSpinCImaginaryAction_eq_complexI,
    d9PrimitiveSpinCImaginaryAction_eq_complexI,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right]
  simp

/-! ## Levi--Civita spin correction -/

/-- A product of two distinct skew-Hermitian Clifford generators is again
skew-Hermitian because the generators anticommute. -/
theorem d9DoubledMatterSpinorHermitianPairing_gamma_comp
    (firstDirection secondDirection : Fin 3)
    (hDistinct : firstDirection ≠ secondDirection)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma firstDirection
          (d9DoubledMatterFiberCliffordGamma secondDirection first)) second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9DoubledMatterFiberCliffordGamma firstDirection
          (d9DoubledMatterFiberCliffordGamma secondDirection second)) := by
  rw [d9DoubledMatterSpinorHermitianPairing_gamma,
    d9DoubledMatterSpinorHermitianPairing_gamma]
  rw [d9DoubledMatterFiberCliffordGamma_anticommute
    secondDirection firstDirection (Ne.symm hDistinct)]
  simpa using
    (d9DoubledMatterSpinorHermitianPairing_real_smul_right
      (-1) first
      (d9DoubledMatterFiberCliffordGamma firstDirection
        (d9DoubledMatterFiberCliffordGamma secondDirection second)))

/-- The full radial Levi--Civita spin correction in one frame direction is
skew-Hermitian. -/
theorem d9LeviCivitaSpinCorrection_pairing_skew
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9LeviCivitaSpinCorrection period hPeriod direction point first)
        second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9LeviCivitaSpinCorrection period hPeriod direction point second) := by
  fin_cases direction <;>
    simp [d9LeviCivitaSpinCorrection, Fin.sum_univ_succ,
      d9DoubledMatterSpinorHermitianPairing_add_left,
      d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterSpinorHermitianPairing_real_smul_left,
      d9DoubledMatterSpinorHermitianPairing_real_smul_right,
      d9DoubledMatterSpinorHermitianPairing_gamma_comp] <;>
    ring

/-- The local monopole correction is skew-Hermitian for every real potential
and coframe coefficient. -/
theorem d9PrimitiveSpinCMonopoleCorrection_pairing_skew
    (potential azimuthalComponent : Real)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (azimuthalComponent •
          (potential • d9PrimitiveSpinCImaginaryAction first)) second =
      -d9DoubledMatterSpinorHermitianPairing first
        (azimuthalComponent •
          (potential • d9PrimitiveSpinCImaginaryAction second)) := by
  rw [d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9DoubledMatterSpinorHermitianPairing_imaginaryAction,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right]
  ring

/-! ## Doubled flat and full local connection Leibniz identities -/

private theorem d9DoubledMatterSpinorFlatCoverDerivative_fst
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod)
    (tangent : ThroatCoverCoordinates) :
    (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice lift point
      tangent).1 =
      d9MatterSpinorFlatCoverDerivative period hPeriod choice lift.first point
        tangent := by
  have hFirst : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.first point :=
    lift.first.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSecond : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.second point :=
    lift.second.contMDiff_toFun.mdifferentiableAt (by simp)
  have hProduct := mfderiv_prodMk hFirst hSecond
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hProduct
  have hApply := congrArg (fun derivative => derivative tangent) hProduct
  exact congrArg Prod.fst hApply

private theorem d9DoubledMatterSpinorFlatCoverDerivative_snd
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod)
    (tangent : ThroatCoverCoordinates) :
    (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice lift point
      tangent).2 =
      d9MatterSpinorFlatCoverDerivative period hPeriod (oppositeRoot choice)
        lift.second point tangent := by
  have hFirst : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.first point :=
    lift.first.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSecond : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.second point :=
    lift.second.contMDiff_toFun.mdifferentiableAt (by simp)
  have hProduct := mfderiv_prodMk hFirst hSecond
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hProduct
  have hApply := congrArg (fun derivative => derivative tangent) hProduct
  exact congrArg Prod.snd hApply

/-- Flat doubled differentiation obeys the Hermitian Leibniz identity. -/
theorem d9DoubledMatterSpinorFlatCoverDerivative_pairing_compatible
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) (tangent : ThroatCoverCoordinates) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor =>
          d9DoubledMatterSpinorHermitianPairing
            (first anchor) (second anchor)) point tangent =
      d9DoubledMatterSpinorHermitianPairing (first point)
          (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
            second point tangent) +
        d9DoubledMatterSpinorHermitianPairing
          (d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
            first point tangent) (second point) := by
  have hPlusDiff : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Complex)
      (fun anchor => d9MatterSpinorHermitianPairing
        (first.first anchor) (second.first anchor)) point :=
    (d9MatterSpinorSectionPairing_contMDiff period hPeriod choice
      first.first second.first).mdifferentiableAt (by simp)
  have hMinusDiff : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Complex)
      (fun anchor => d9MatterSpinorHermitianPairing
        (first.second anchor) (second.second anchor)) point :=
    (d9MatterSpinorSectionPairing_contMDiff period hPeriod
      (oppositeRoot choice) first.second second.second).mdifferentiableAt
        (by simp)
  change
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        ((fun anchor => d9MatterSpinorHermitianPairing
            (first.first anchor) (second.first anchor)) +
          (fun anchor => d9MatterSpinorHermitianPairing
            (first.second anchor) (second.second anchor))) point tangent = _
  rw [mfderiv_add hPlusDiff hMinusDiff]
  simp only [add_apply]
  rw [d9MatterSpinorFlatCoverDerivative_pairing_compatible period hPeriod choice,
    d9MatterSpinorFlatCoverDerivative_pairing_compatible period hPeriod
      (oppositeRoot choice)]
  rw [d9DoubledMatterSpinorFlatCoverDerivative_fst,
    d9DoubledMatterSpinorFlatCoverDerivative_fst,
    d9DoubledMatterSpinorFlatCoverDerivative_snd,
    d9DoubledMatterSpinorFlatCoverDerivative_snd]
  unfold d9DoubledMatterSpinorHermitianPairing
  ring

/-- The Levi--Civita spin connection retains the same pairing derivative as
the flat derivative because its correction is skew-Hermitian. -/
theorem d9LeviCivitaSpinFrameDerivative_pairing_compatible
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor =>
          d9DoubledMatterSpinorHermitianPairing
            (first anchor) (second anchor)) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      d9DoubledMatterSpinorHermitianPairing (first point)
          (d9LeviCivitaSpinFrameDerivative period hPeriod choice second
            direction point) +
        d9DoubledMatterSpinorHermitianPairing
          (d9LeviCivitaSpinFrameDerivative period hPeriod choice first
            direction point) (second point) := by
  rw [d9DoubledMatterSpinorFlatCoverDerivative_pairing_compatible]
  rw [← d9IntrinsicDoubledMatterFlatFrameDerivative_eq_flatCoverDerivative
      period hPeriod choice second direction point,
    ← d9IntrinsicDoubledMatterFlatFrameDerivative_eq_flatCoverDerivative
      period hPeriod choice first direction point]
  unfold d9LeviCivitaSpinFrameDerivative
  rw [d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9LeviCivitaSpinCorrection_pairing_skew]
  ring

/-- The complete local primitive SpinC derivative, including the monopole
potential, is Hermitian compatible. -/
theorem d9LeviCivitaPrimitiveSpinCLocalFrameDerivative_pairing_compatible
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (charge : Int) (chart : MonopoleChart) (polarAngle : Real)
    (azimuthalComponent : Real)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor =>
          d9DoubledMatterSpinorHermitianPairing
            (first anchor) (second anchor)) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      d9DoubledMatterSpinorHermitianPairing (first point)
          (d9LeviCivitaPrimitiveSpinCLocalFrameDerivative period hPeriod choice
            second charge chart polarAngle azimuthalComponent direction point) +
        d9DoubledMatterSpinorHermitianPairing
          (d9LeviCivitaPrimitiveSpinCLocalFrameDerivative period hPeriod choice
            first charge chart polarAngle azimuthalComponent direction point)
          (second point) := by
  rw [d9LeviCivitaSpinFrameDerivative_pairing_compatible]
  unfold d9LeviCivitaPrimitiveSpinCLocalFrameDerivative
  rw [d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9PrimitiveSpinCMonopoleCorrection_pairing_skew]
  ring

/-- Public algebraic/differential compatibility certificate for the full local
primitive SpinC connection. -/
structure ProgramPPrimitiveSpinCConnectionHermitianCertificate4D : Prop where
  compatible : ∀ choice first second charge chart polarAngle
      azimuthalComponent direction point,
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun anchor =>
          d9DoubledMatterSpinorHermitianPairing
            (first anchor) (second anchor)) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      d9DoubledMatterSpinorHermitianPairing (first point)
          (d9LeviCivitaPrimitiveSpinCLocalFrameDerivative period hPeriod choice
            second charge chart polarAngle azimuthalComponent direction point) +
        d9DoubledMatterSpinorHermitianPairing
          (d9LeviCivitaPrimitiveSpinCLocalFrameDerivative period hPeriod choice
            first charge chart polarAngle azimuthalComponent direction point)
          (second point)

/-- The implemented connection supplies this certificate unconditionally. -/
def programPPrimitiveSpinCConnectionHermitianCertificate4D :
    ProgramPPrimitiveSpinCConnectionHermitianCertificate4D period hPeriod where
  compatible :=
    d9LeviCivitaPrimitiveSpinCLocalFrameDerivative_pairing_compatible
      period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCConnectionHermitian4D
end JanusFormal
