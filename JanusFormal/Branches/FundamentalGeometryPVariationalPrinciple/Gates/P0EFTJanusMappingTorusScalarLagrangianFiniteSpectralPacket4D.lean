import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarTwoSectorQuadraticDiagonalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

/-!
# Finite Galerkin packets of scalar Lagrangian eigenmodes

A finite orthonormal family of closed-operator eigenfields provides an exact
Galerkin sector.  In coefficient coordinates the ambient mass form is the
Euclidean square norm and the Jacobi quadratic form is diagonal with the
operator eigenvalues.

The Rayleigh quotient of a nonzero packet is therefore a weighted average of
the packet eigenvalues and lies between their minimum and maximum.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w} {Mode : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [Fintype Mode] [DecidableEq Mode]

private abbrev LagrangianDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    data hClosable traceBound condition

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {hClosable : CanonicalScalarGraphClosable data}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}

/-- Finite orthonormal packet of genuine closed-operator eigenfields. -/
structure CanonicalScalarFiniteSpectralPacket
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (Mode : Type z) [Fintype Mode] [DecidableEq Mode] where
  eigenfield : Mode → LagrangianDomain data hClosable traceBound condition
  eigenvalue : Mode → Real
  eigenEquation : ∀ mode,
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition (eigenfield mode) =
      eigenvalue mode • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (eigenfield mode)
  orthonormal : Orthonormal Real fun mode =>
    canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition (eigenfield mode)

namespace CanonicalScalarFiniteSpectralPacket

/-- Domain-valued finite spectral packet. -/
def field
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    LagrangianDomain data hClosable traceBound condition :=
  ∑ mode, coefficient mode • packet.eigenfield mode

/-- Ambient representative of a finite packet. -/
def ambientField
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) : Ambient :=
  ∑ mode, coefficient mode •
    canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition (packet.eigenfield mode)

@[simp] theorem inclusion_field
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (packet.field coefficient) =
      packet.ambientField coefficient := by
  simp [field, ambientField]

/-- Operator on a finite spectral packet is diagonal. -/
theorem operator_field
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition (packet.field coefficient) =
      ∑ mode, (packet.eigenvalue mode * coefficient mode) •
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (packet.eigenfield mode) := by
  simp only [field, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro mode _
  rw [packet.eigenEquation]
  module

/-- Ambient mass of a packet is the Euclidean coefficient norm. -/
theorem mass_eq_sum_sq
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianMassFunctional
        data hClosable traceBound condition (packet.field coefficient) =
      ∑ mode, coefficient mode ^ 2 := by
  unfold canonicalScalarClosedLagrangianMassFunctional
    canonicalScalarClosedLagrangianMassPairing
  rw [packet.inclusion_field]
  unfold ambientField
  simpa [pow_two] using
    (packet.orthonormal.inner_sum coefficient coefficient Finset.univ)

/-- Jacobi quadratic form of a packet is diagonal in the eigenbasis. -/
theorem quadratic_eq_weighted_sum
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition (packet.field coefficient) =
      ∑ mode, packet.eigenvalue mode * coefficient mode ^ 2 := by
  unfold canonicalScalarClosedLagrangianQuadraticFunctional
    canonicalScalarClosedLagrangianJacobiPairing
  rw [packet.operator_field, packet.inclusion_field]
  unfold ambientField
  simpa [pow_two, mul_assoc] using
    (packet.orthonormal.inner_sum
      (fun mode => packet.eigenvalue mode * coefficient mode)
      coefficient Finset.univ)

/-- Nonzero coefficient vector gives nonzero packet. -/
theorem field_ne_zero_of_coefficient
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real)
    (hCoefficient : ∃ mode, coefficient mode ≠ 0) :
    packet.field coefficient ≠ 0 := by
  intro hField
  have hMass := packet.mass_eq_sum_sq coefficient
  rw [hField] at hMass
  simp [canonicalScalarClosedLagrangianMassFunctional,
    canonicalScalarClosedLagrangianMassPairing] at hMass
  rcases hCoefficient with ⟨mode, hMode⟩
  have hNonnegative : ∀ currentMode, 0 ≤ coefficient currentMode ^ 2 :=
    fun currentMode => sq_nonneg _
  have hModeLe : coefficient mode ^ 2 ≤ ∑ currentMode, coefficient currentMode ^ 2 := by
    simpa using (Finset.single_le_sum
      (s := Finset.univ) (f := fun currentMode => coefficient currentMode ^ 2)
      (fun currentMode _ => hNonnegative currentMode) (Finset.mem_univ mode))
  have hModeSquare : coefficient mode ^ 2 = 0 := by
    apply le_antisymm
    · linarith [hModeLe]
    · exact sq_nonneg _
  exact hMode (sq_eq_zero_iff.mp hModeSquare)

/-- Packet Rayleigh quotient. -/
noncomputable def rayleighQuotient
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) : Real :=
  (∑ mode, packet.eigenvalue mode * coefficient mode ^ 2) /
    (∑ mode, coefficient mode ^ 2)

/-- Packet Rayleigh quotient agrees with the operator-domain Rayleigh quotient. -/
theorem rayleighQuotient_eq
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianRayleighQuotient
        data hClosable traceBound condition (packet.field coefficient) =
      packet.rayleighQuotient coefficient := by
  unfold canonicalScalarClosedLagrangianRayleighQuotient
    CanonicalScalarFiniteSpectralPacket.rayleighQuotient
  rw [packet.quadratic_eq_weighted_sum, packet.mass_eq_sum_sq]

/-- Lower bound on a packet Rayleigh quotient. -/
theorem rayleighQuotient_ge
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real)
    (lower : Real)
    (hLower : ∀ mode, lower ≤ packet.eigenvalue mode)
    (hCoefficient : ∃ mode, coefficient mode ≠ 0) :
    lower ≤ packet.rayleighQuotient coefficient := by
  have hDenPositive : 0 < ∑ mode, coefficient mode ^ 2 := by
    have hNonnegative : ∀ mode, 0 ≤ coefficient mode ^ 2 :=
      fun mode => sq_nonneg _
    rcases hCoefficient with ⟨mode, hMode⟩
    have hModePositive : 0 < coefficient mode ^ 2 := sq_pos_of_ne_zero hMode
    exact lt_of_lt_of_le hModePositive (by
      simpa using (Finset.single_le_sum
        (s := Finset.univ) (f := fun currentMode => coefficient currentMode ^ 2)
        (fun currentMode _ => hNonnegative currentMode) (Finset.mem_univ mode)))
  unfold CanonicalScalarFiniteSpectralPacket.rayleighQuotient
  apply (le_div_iff₀ hDenPositive).2
  calc
    lower * ∑ mode, coefficient mode ^ 2 =
        ∑ mode, lower * coefficient mode ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ mode, packet.eigenvalue mode * coefficient mode ^ 2 := by
      gcongr with mode
      exact hLower mode

/-- Upper bound on a packet Rayleigh quotient. -/
theorem rayleighQuotient_le
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real)
    (upper : Real)
    (hUpper : ∀ mode, packet.eigenvalue mode ≤ upper)
    (hCoefficient : ∃ mode, coefficient mode ≠ 0) :
    packet.rayleighQuotient coefficient ≤ upper := by
  have hDenPositive : 0 < ∑ mode, coefficient mode ^ 2 := by
    have hNonnegative : ∀ mode, 0 ≤ coefficient mode ^ 2 :=
      fun mode => sq_nonneg _
    rcases hCoefficient with ⟨mode, hMode⟩
    have hModePositive : 0 < coefficient mode ^ 2 := sq_pos_of_ne_zero hMode
    exact lt_of_lt_of_le hModePositive (by
      simpa using (Finset.single_le_sum
        (s := Finset.univ) (f := fun currentMode => coefficient currentMode ^ 2)
        (fun currentMode _ => hNonnegative currentMode) (Finset.mem_univ mode)))
  unfold CanonicalScalarFiniteSpectralPacket.rayleighQuotient
  apply (div_le_iff₀ hDenPositive).2
  calc
    ∑ mode, packet.eigenvalue mode * coefficient mode ^ 2 ≤
        ∑ mode, upper * coefficient mode ^ 2 := by
      gcongr with mode
      exact hUpper mode
    _ = upper * ∑ mode, coefficient mode ^ 2 := by
      rw [Finset.mul_sum]

/-- Finite spectral-packet certificate. -/
theorem canonicalScalarFiniteSpectralPacket_certificate
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coefficient : Mode → Real) :
    canonicalScalarClosedLagrangianMassFunctional
        data hClosable traceBound condition (packet.field coefficient) =
      ∑ mode, coefficient mode ^ 2 ∧
    canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition (packet.field coefficient) =
      ∑ mode, packet.eigenvalue mode * coefficient mode ^ 2 :=
  ⟨packet.mass_eq_sum_sq coefficient,
    packet.quadratic_eq_weighted_sum coefficient⟩

end CanonicalScalarFiniteSpectralPacket

end
end P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D
end JanusFormal
