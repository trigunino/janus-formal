import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphFiniteBoundaryOneLoop4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

/-!
# Finite-mode heat dynamics for scalar Lagrangian eigenpackets

A finite spectral packet evolves under the heat equation by multiplying each
mode coefficient by `exp(-t lambda)`.  The construction stays in the genuine
closed operator domain.

This file proves the initial condition, coefficient semigroup law, scalar
coefficient derivatives and the exact generator identity saying that the
ambient image of the formal time-derivative packet is minus the operator image
of the heat packet.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianFiniteModeHeatDynamics4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w} {Mode : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [Fintype Mode] [DecidableEq Mode]

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {hClosable : CanonicalScalarGraphClosable data}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}

/-- Heat-evolved coefficient of one eigenmode. -/
def canonicalScalarFiniteModeHeatCoefficient
    (eigenvalue coefficient : Real) (time : Real) : Real :=
  Real.exp (-time * eigenvalue) * coefficient

@[simp] theorem canonicalScalarFiniteModeHeatCoefficient_zero
    (eigenvalue coefficient : Real) :
    canonicalScalarFiniteModeHeatCoefficient eigenvalue coefficient 0 = coefficient := by
  simp [canonicalScalarFiniteModeHeatCoefficient]

/-- Coefficient semigroup law. -/
theorem canonicalScalarFiniteModeHeatCoefficient_add
    (eigenvalue coefficient firstTime secondTime : Real) :
    canonicalScalarFiniteModeHeatCoefficient eigenvalue coefficient
        (firstTime + secondTime) =
      canonicalScalarFiniteModeHeatCoefficient eigenvalue
        (canonicalScalarFiniteModeHeatCoefficient
          eigenvalue coefficient secondTime) firstTime := by
  unfold canonicalScalarFiniteModeHeatCoefficient
  rw [show -(firstTime + secondTime) * eigenvalue =
      (-firstTime * eigenvalue) + (-secondTime * eigenvalue) by ring,
    Real.exp_add]
  ring

/-- Derivative of one heat coefficient. -/
theorem canonicalScalarFiniteModeHeatCoefficient_hasDerivAt
    (eigenvalue coefficient time : Real) :
    HasDerivAt
      (canonicalScalarFiniteModeHeatCoefficient eigenvalue coefficient)
      (-eigenvalue * canonicalScalarFiniteModeHeatCoefficient
        eigenvalue coefficient time) time := by
  unfold canonicalScalarFiniteModeHeatCoefficient
  convert (((hasDerivAt_neg time).mul_const eigenvalue).exp.mul_const coefficient) using 1
  all_goals first | rfl | ring

/-- Heat coefficient family of a finite spectral packet. -/
def CanonicalScalarFiniteSpectralPacket.heatCoefficient
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) : Mode → Real :=
  fun mode => canonicalScalarFiniteModeHeatCoefficient
    (packet.eigenvalue mode) (initialCoefficient mode) time

/-- Domain-valued finite-mode heat field. -/
def CanonicalScalarFiniteSpectralPacket.heatField
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) :=
  packet.field
    (CanonicalScalarFiniteSpectralPacket.heatCoefficient
      packet initialCoefficient time)

/-- Formal time-derivative packet. -/
def CanonicalScalarFiniteSpectralPacket.heatDerivativeField
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) :=
  packet.field fun mode =>
    -packet.eigenvalue mode *
      CanonicalScalarFiniteSpectralPacket.heatCoefficient
        packet initialCoefficient time mode

/-- Initial condition. -/
theorem CanonicalScalarFiniteSpectralPacket.heatField_zero
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real) :
    CanonicalScalarFiniteSpectralPacket.heatField packet initialCoefficient 0 =
      packet.field initialCoefficient := by
  unfold CanonicalScalarFiniteSpectralPacket.heatField
    CanonicalScalarFiniteSpectralPacket.heatCoefficient
  congr 1
  funext mode
  simp

/-- Heat semigroup law at coefficient level. -/
theorem CanonicalScalarFiniteSpectralPacket.heatCoefficient_add
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (firstTime secondTime : Real) :
    CanonicalScalarFiniteSpectralPacket.heatCoefficient packet initialCoefficient
        (firstTime + secondTime) =
      CanonicalScalarFiniteSpectralPacket.heatCoefficient packet
        (CanonicalScalarFiniteSpectralPacket.heatCoefficient
          packet initialCoefficient secondTime) firstTime := by
  funext mode
  exact canonicalScalarFiniteModeHeatCoefficient_add
    (packet.eigenvalue mode) (initialCoefficient mode) firstTime secondTime

/-- Heat semigroup law for finite domain packets. -/
theorem CanonicalScalarFiniteSpectralPacket.heatField_add
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (firstTime secondTime : Real) :
    CanonicalScalarFiniteSpectralPacket.heatField packet initialCoefficient
        (firstTime + secondTime) =
      CanonicalScalarFiniteSpectralPacket.heatField packet
        (CanonicalScalarFiniteSpectralPacket.heatCoefficient
          packet initialCoefficient secondTime) firstTime := by
  unfold CanonicalScalarFiniteSpectralPacket.heatField
  rw [CanonicalScalarFiniteSpectralPacket.heatCoefficient_add packet]

/-- Each packet coefficient solves its scalar heat ODE. -/
theorem CanonicalScalarFiniteSpectralPacket.heatCoefficient_hasDerivAt
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) (mode : Mode) :
    HasDerivAt
      (fun currentTime => CanonicalScalarFiniteSpectralPacket.heatCoefficient
        packet initialCoefficient currentTime mode)
      (-packet.eigenvalue mode *
        CanonicalScalarFiniteSpectralPacket.heatCoefficient
          packet initialCoefficient time mode) time :=
  canonicalScalarFiniteModeHeatCoefficient_hasDerivAt
    (packet.eigenvalue mode) (initialCoefficient mode) time

/-- Operator image of the heat packet. -/
theorem CanonicalScalarFiniteSpectralPacket.operator_heatField
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (CanonicalScalarFiniteSpectralPacket.heatField
          packet initialCoefficient time) =
      ∑ mode,
        (packet.eigenvalue mode *
          CanonicalScalarFiniteSpectralPacket.heatCoefficient
            packet initialCoefficient time mode) •
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (packet.eigenfield mode) :=
  packet.operator_field
    (CanonicalScalarFiniteSpectralPacket.heatCoefficient
      packet initialCoefficient time)

/-- Exact finite-mode heat generator identity. -/
theorem CanonicalScalarFiniteSpectralPacket.heat_generator_identity
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) :
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (CanonicalScalarFiniteSpectralPacket.heatDerivativeField
          packet initialCoefficient time) =
      -canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (CanonicalScalarFiniteSpectralPacket.heatField
          packet initialCoefficient time) := by
  unfold CanonicalScalarFiniteSpectralPacket.heatDerivativeField
  rw [packet.inclusion_field,
    CanonicalScalarFiniteSpectralPacket.operator_heatField packet]
  unfold CanonicalScalarFiniteSpectralPacket.ambientField
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  module

/-- If all packet eigenvalues are nonnegative and time is nonnegative, every
coefficient magnitude is nonincreasing. -/
theorem CanonicalScalarFiniteSpectralPacket.heatCoefficient_abs_le
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real)
    (time : Real) (hTime : 0 ≤ time)
    (hEigenvalue : ∀ mode, 0 ≤ packet.eigenvalue mode)
    (mode : Mode) :
    |CanonicalScalarFiniteSpectralPacket.heatCoefficient
        packet initialCoefficient time mode| ≤
      |initialCoefficient mode| := by
  unfold CanonicalScalarFiniteSpectralPacket.heatCoefficient
    canonicalScalarFiniteModeHeatCoefficient
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hExponent : -time * packet.eigenvalue mode ≤ 0 := by
    nlinarith [hEigenvalue mode]
  have hExp : Real.exp (-time * packet.eigenvalue mode) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hExponent
  exact mul_le_of_le_one_left (abs_nonneg _) hExp

/-- Finite-mode heat certificate. -/
theorem canonicalScalarFiniteModeHeatDynamics_certificate
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (initialCoefficient : Mode → Real) :
    CanonicalScalarFiniteSpectralPacket.heatField
        packet initialCoefficient 0 = packet.field initialCoefficient ∧
      (∀ firstTime secondTime,
        CanonicalScalarFiniteSpectralPacket.heatField packet initialCoefficient
            (firstTime + secondTime) =
          CanonicalScalarFiniteSpectralPacket.heatField packet
            (CanonicalScalarFiniteSpectralPacket.heatCoefficient
              packet initialCoefficient secondTime) firstTime) ∧
      (∀ time,
        canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition
            (CanonicalScalarFiniteSpectralPacket.heatDerivativeField
              packet initialCoefficient time) =
          -canonicalScalarClosedLagrangianDomainOperator
            data hClosable traceBound condition
            (CanonicalScalarFiniteSpectralPacket.heatField
              packet initialCoefficient time)) :=
  ⟨CanonicalScalarFiniteSpectralPacket.heatField_zero packet initialCoefficient,
    CanonicalScalarFiniteSpectralPacket.heatField_add packet initialCoefficient,
    CanonicalScalarFiniteSpectralPacket.heat_generator_identity
      packet initialCoefficient⟩

end
end P0EFTJanusMappingTorusScalarLagrangianFiniteModeHeatDynamics4D
end JanusFormal
