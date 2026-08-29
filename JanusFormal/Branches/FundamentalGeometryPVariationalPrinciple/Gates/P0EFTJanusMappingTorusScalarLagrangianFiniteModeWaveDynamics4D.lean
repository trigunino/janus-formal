import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarTwoSectorAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

/-!
# Finite-mode wave dynamics for scalar Lagrangian eigenpackets

A finite eigenpacket with nonnegative eigenvalues and chosen frequencies
`omega_n` satisfying `omega_n²=lambda_n` evolves through cosine/sine mode
coefficients.  Position, velocity and acceleration stay in the actual closed
operator domain.

The formal acceleration packet is exactly minus the operator image of the wave
packet.  Scalar coefficient derivatives are also recorded, giving the exact
finite-dimensional wave evolution.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianFiniteModeWaveDynamics4D

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

/-- Frequency data for a nonnegative finite spectral packet. -/
structure CanonicalScalarFiniteWavePacket
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) where
  frequency : Mode → Real
  frequency_nonnegative : ∀ mode, 0 ≤ frequency mode
  frequency_sq : ∀ mode, frequency mode ^ 2 = packet.eigenvalue mode

variable
  {packet : CanonicalScalarFiniteSpectralPacket
    data hClosable traceBound condition Mode}

namespace CanonicalScalarFiniteWavePacket

/-- Scalar wave position coefficient. -/
def positionCoefficient
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) : Real :=
  Real.cos (wave.frequency mode * time) * initialPosition mode +
    Real.sin (wave.frequency mode * time) * initialSine mode

/-- Scalar wave velocity coefficient. -/
def velocityCoefficient
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) : Real :=
  -wave.frequency mode * Real.sin (wave.frequency mode * time) *
      initialPosition mode +
    wave.frequency mode * Real.cos (wave.frequency mode * time) *
      initialSine mode

/-- Scalar wave acceleration coefficient. -/
def accelerationCoefficient
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) : Real :=
  -(wave.frequency mode ^ 2) *
    wave.positionCoefficient initialPosition initialSine time mode

/-- Domain-valued finite wave field. -/
def field
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :=
  packet.field (wave.positionCoefficient initialPosition initialSine time)

/-- Domain-valued velocity packet. -/
def velocityField
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :=
  packet.field (wave.velocityCoefficient initialPosition initialSine time)

/-- Domain-valued acceleration packet. -/
def accelerationField
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :=
  packet.field (wave.accelerationCoefficient initialPosition initialSine time)

/-- Initial position. -/
theorem field_zero
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real) :
    wave.field initialPosition initialSine 0 =
      packet.field initialPosition := by
  unfold field positionCoefficient
  congr 1
  funext mode
  simp

/-- Initial velocity is `omega * initialSine`. -/
theorem velocityField_zero
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real) :
    wave.velocityField initialPosition initialSine 0 =
      packet.field (fun mode => wave.frequency mode * initialSine mode) := by
  unfold velocityField velocityCoefficient
  congr 1
  funext mode
  simp

/-- Derivative of every position coefficient. -/
theorem positionCoefficient_hasDerivAt
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) :
    HasDerivAt
      (fun currentTime =>
        wave.positionCoefficient initialPosition initialSine currentTime mode)
      (wave.velocityCoefficient initialPosition initialSine time mode) time := by
  have hArgument : HasDerivAt
      (fun currentTime : Real => wave.frequency mode * currentTime)
      (wave.frequency mode) time :=
    hasDerivAt_const_mul (wave.frequency mode)
  have hRaw :=
    ((((Real.hasDerivAt_cos
      (wave.frequency mode * time)).comp time
        hArgument).mul_const (initialPosition mode)).add
      (((Real.hasDerivAt_sin
        (wave.frequency mode * time)).comp time
          hArgument).mul_const (initialSine mode)))
  have hDerivative : HasDerivAt
      (fun currentTime =>
        wave.positionCoefficient initialPosition initialSine currentTime mode)
      ((-Real.sin (wave.frequency mode * time) * wave.frequency mode) *
          initialPosition mode +
        (Real.cos (wave.frequency mode * time) * wave.frequency mode) *
          initialSine mode) time :=
    hRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _currentTime => rfl))
  apply hDerivative.congr_deriv
  unfold velocityCoefficient
  ring

/-- Derivative of every velocity coefficient. -/
theorem velocityCoefficient_hasDerivAt
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) :
    HasDerivAt
      (fun currentTime =>
        wave.velocityCoefficient initialPosition initialSine currentTime mode)
      (wave.accelerationCoefficient initialPosition initialSine time mode) time := by
  have hArgument : HasDerivAt
      (fun currentTime : Real => wave.frequency mode * currentTime)
      (wave.frequency mode) time :=
    hasDerivAt_const_mul (wave.frequency mode)
  have hRaw :=
    (((((Real.hasDerivAt_sin
      (wave.frequency mode * time)).comp time
        hArgument).const_mul (-wave.frequency mode)).mul_const
            (initialPosition mode)).add
      ((((Real.hasDerivAt_cos
        (wave.frequency mode * time)).comp time
          hArgument).const_mul (wave.frequency mode)).mul_const
              (initialSine mode)))
  have hDerivative : HasDerivAt
      (fun currentTime =>
        wave.velocityCoefficient initialPosition initialSine currentTime mode)
      (((-wave.frequency mode) *
          (Real.cos (wave.frequency mode * time) * wave.frequency mode)) *
          initialPosition mode +
        (wave.frequency mode *
          (-Real.sin (wave.frequency mode * time) * wave.frequency mode)) *
          initialSine mode) time :=
    hRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _currentTime => rfl))
  apply hDerivative.congr_deriv
  unfold accelerationCoefficient positionCoefficient
  ring

/-- Operator image of the wave packet. -/
theorem operator_field
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (wave.field initialPosition initialSine time) =
      ∑ mode,
        (packet.eigenvalue mode *
          wave.positionCoefficient initialPosition initialSine time mode) •
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (packet.eigenfield mode) :=
  packet.operator_field
    (wave.positionCoefficient initialPosition initialSine time)

/-- Exact finite-mode wave generator identity `u_tt = -A u`. -/
theorem acceleration_generator_identity
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (wave.accelerationField initialPosition initialSine time) =
      -canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (wave.field initialPosition initialSine time) := by
  unfold accelerationField field
  rw [packet.inclusion_field, packet.operator_field]
  unfold CanonicalScalarFiniteSpectralPacket.ambientField
    accelerationCoefficient
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  rw [wave.frequency_sq]
  module

/-- Scalar modal energy. -/
def modalEnergy
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) : Real :=
  (1 / 2 : Real) *
    (wave.velocityCoefficient initialPosition initialSine time mode) ^ 2 +
  (1 / 2 : Real) * packet.eigenvalue mode *
    (wave.positionCoefficient initialPosition initialSine time mode) ^ 2

/-- Each scalar modal energy is constant. -/
theorem modalEnergy_eq_initial
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) (mode : Mode) :
    wave.modalEnergy initialPosition initialSine time mode =
      (1 / 2 : Real) * (wave.frequency mode ^ 2) *
        ((initialPosition mode) ^ 2 + (initialSine mode) ^ 2) := by
  unfold modalEnergy velocityCoefficient positionCoefficient
  rw [← wave.frequency_sq mode]
  have hTrig := Real.sin_sq_add_cos_sq (wave.frequency mode * time)
  calc
    _ = (1 / 2 : Real) * wave.frequency mode ^ 2 *
        (Real.sin (wave.frequency mode * time) ^ 2 +
          Real.cos (wave.frequency mode * time) ^ 2) *
        (initialPosition mode ^ 2 + initialSine mode ^ 2) := by ring
    _ = _ := by rw [hTrig]; ring

/-- Total finite-mode energy. -/
def energy
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) : Real :=
  ∑ mode, wave.modalEnergy initialPosition initialSine time mode

/-- Total finite-mode energy is conserved. -/
theorem energy_conserved
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real)
    (time : Real) :
    wave.energy initialPosition initialSine time =
      ∑ mode, (1 / 2 : Real) * (wave.frequency mode ^ 2) *
        ((initialPosition mode) ^ 2 + (initialSine mode) ^ 2) := by
  unfold energy
  apply Finset.sum_congr rfl
  intro mode _
  exact wave.modalEnergy_eq_initial initialPosition initialSine time mode

/-- Finite-mode wave certificate. -/
theorem canonicalScalarFiniteModeWaveDynamics_certificate
    (wave : CanonicalScalarFiniteWavePacket packet)
    (initialPosition initialSine : Mode → Real) :
    wave.field initialPosition initialSine 0 = packet.field initialPosition ∧
      (∀ time,
        canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition
            (wave.accelerationField initialPosition initialSine time) =
          -canonicalScalarClosedLagrangianDomainOperator
            data hClosable traceBound condition
            (wave.field initialPosition initialSine time)) ∧
      (∀ time,
        wave.energy initialPosition initialSine time =
          ∑ mode, (1 / 2 : Real) * (wave.frequency mode ^ 2) *
            ((initialPosition mode) ^ 2 + (initialSine mode) ^ 2)) :=
  ⟨wave.field_zero initialPosition initialSine,
    wave.acceleration_generator_identity initialPosition initialSine,
    wave.energy_conserved initialPosition initialSine⟩

end CanonicalScalarFiniteWavePacket

end
end P0EFTJanusMappingTorusScalarLagrangianFiniteModeWaveDynamics4D
end JanusFormal
