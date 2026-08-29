import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

/-!
# Local primitive SpinC connection on D9

The north/south Dirac potentials are coupled to the doubled matter fiber
through multiplication by `i`.  Their exact gauge relation is proved in the
same representation used by the primitive SpinC vector bundle.  The
Levi--Civita spin derivative and this `U(1)` correction are then combined
without introducing a new axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCConnection4D

set_option autoImplicit false
noncomputable section

open Metric
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

/-- The unit complex phase `i`. -/
def d9PrimitiveSpinCImaginaryPhase : Circle :=
  ⟨Complex.I, by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm]⟩

@[simp]
theorem d9PrimitiveSpinCImaginaryPhase_coe :
    (d9PrimitiveSpinCImaginaryPhase : Complex) = Complex.I :=
  rfl

/-- Infinitesimal `U(1)` generator on the real doubled matter fiber. -/
def d9PrimitiveSpinCImaginaryAction :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  d9PrimitiveSpinCPhaseActionCLM d9PrimitiveSpinCImaginaryPhase

theorem d9PrimitiveSpinCImaginaryAction_commutes_phase
    (phase : Circle) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCImaginaryAction matter) := by
  unfold d9PrimitiveSpinCImaginaryAction
  rw [← d9PrimitiveSpinCPhaseAction_mul,
    ← d9PrimitiveSpinCPhaseAction_mul]
  exact congrArg
    (fun combined =>
      d9PrimitiveSpinCPhaseActionCLM combined matter)
    (mul_comm d9PrimitiveSpinCImaginaryPhase phase)

/-- North/south coefficient of the charge-`charge` Dirac connection. -/
def d9PrimitiveSpinCLocalPotential
    (charge : Int) (chart : MonopoleChart) (polarAngle : Real) : Real :=
  match chart with
  | .north => primitiveMonopoleNorthPotential charge polarAngle
  | .south => primitiveMonopoleSouthPotential charge polarAngle

theorem d9PrimitiveSpinCLocalPotential_gauge_difference
    (charge : Int) (polarAngle : Real) :
    d9PrimitiveSpinCLocalPotential charge .north polarAngle -
        d9PrimitiveSpinCLocalPotential charge .south polarAngle =
      (charge : Real) :=
  primitiveMonopolePotential_gauge_difference charge polarAngle

/-- Local azimuthal SpinC derivative `∂φ + i Aφ`.  The argument
`partialAzimuthal` is the ordinary/Levi--Civita derivative already evaluated
in the local gauge. -/
def d9PrimitiveSpinCLocalAzimuthalDerivative
    (charge : Int) (chart : MonopoleChart) (polarAngle : Real)
    (partialAzimuthal matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  partialAzimuthal +
    d9PrimitiveSpinCLocalPotential charge chart polarAngle •
      d9PrimitiveSpinCImaginaryAction matter

/-- Leibniz transformation of `∂φ(g ψ)` for a transition of winding
`charge`. -/
def d9PrimitiveSpinCGaugeTransformedPartial
    (charge : Int) (phase : Circle)
    (partialAzimuthal matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCPhaseActionCLM phase partialAzimuthal +
    (charge : Real) •
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCPhaseActionCLM phase matter)

/-- Exact north/south gauge compatibility of the local SpinC connection. -/
theorem d9PrimitiveSpinCLocalAzimuthalDerivative_gauge
    (charge : Int) (phase : Circle) (polarAngle : Real)
    (partialAzimuthal matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalAzimuthalDerivative charge .south polarAngle
        (d9PrimitiveSpinCGaugeTransformedPartial
          charge phase partialAzimuthal matter)
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCLocalAzimuthalDerivative
          charge .north polarAngle partialAzimuthal matter) := by
  unfold d9PrimitiveSpinCLocalAzimuthalDerivative
    d9PrimitiveSpinCGaugeTransformedPartial
  rw [map_add, map_smul]
  rw [← d9PrimitiveSpinCImaginaryAction_commutes_phase]
  have hPotential :=
    d9PrimitiveSpinCLocalPotential_gauge_difference
      charge polarAngle
  have hSum :
      (charge : Real) +
          d9PrimitiveSpinCLocalPotential charge .south polarAngle =
        d9PrimitiveSpinCLocalPotential charge .north polarAngle := by
    linarith
  rw [add_assoc, ← add_smul, hSum]

/-- Levi--Civita spin derivative plus the local monopole correction along a
direction whose azimuthal coframe component is supplied explicitly. -/
def d9LeviCivitaPrimitiveSpinCLocalFrameDerivative
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (charge : Int) (chart : MonopoleChart) (polarAngle : Real)
    (azimuthalComponent : Real)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    D9DoubledMatterFiber :=
  d9LeviCivitaSpinFrameDerivative
      period hPeriod choice lift direction point +
    azimuthalComponent •
      (d9PrimitiveSpinCLocalPotential charge chart polarAngle •
        d9PrimitiveSpinCImaginaryAction (lift point))

/-- The combined derivative reduces exactly to Levi--Civita when the
azimuthal component vanishes. -/
@[simp]
theorem d9LeviCivitaPrimitiveSpinCLocalFrameDerivative_zero_azimuthal
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (charge : Int) (chart : MonopoleChart) (polarAngle : Real)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9LeviCivitaPrimitiveSpinCLocalFrameDerivative
        period hPeriod choice lift charge chart polarAngle 0 direction point =
      d9LeviCivitaSpinFrameDerivative
        period hPeriod choice lift direction point := by
  simp [d9LeviCivitaPrimitiveSpinCLocalFrameDerivative]

/-- Concrete connection certificate: the Levi--Civita and primitive
monopole pieces coexist and obey the exact overlap law. -/
structure ProgramPD9PrimitiveSpinCConnectionCertificate4D where
  charge : Int
  charge_eq : charge = 1
  imaginaryGenerator :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber
  imaginaryGeneratorCanonical :
    imaginaryGenerator = d9PrimitiveSpinCImaginaryAction
  gaugeCompatibility :
    ∀ phase polarAngle partialAzimuthal matter,
      d9PrimitiveSpinCLocalAzimuthalDerivative charge .south polarAngle
          (d9PrimitiveSpinCGaugeTransformedPartial
            charge phase partialAzimuthal matter)
          (d9PrimitiveSpinCPhaseActionCLM phase matter) =
        d9PrimitiveSpinCPhaseActionCLM phase
          (d9PrimitiveSpinCLocalAzimuthalDerivative
            charge .north polarAngle partialAzimuthal matter)

def programPD9PrimitiveSpinCConnectionCertificate4D :
    ProgramPD9PrimitiveSpinCConnectionCertificate4D where
  charge := 1
  charge_eq := rfl
  imaginaryGenerator := d9PrimitiveSpinCImaginaryAction
  imaginaryGeneratorCanonical := rfl
  gaugeCompatibility :=
    d9PrimitiveSpinCLocalAzimuthalDerivative_gauge 1

theorem programPD9PrimitiveSpinCConnectionCertificate4D_nonempty :
    Nonempty ProgramPD9PrimitiveSpinCConnectionCertificate4D :=
  ⟨programPD9PrimitiveSpinCConnectionCertificate4D⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
end JanusFormal
