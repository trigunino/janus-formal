import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompactResolventSpectrum4D

/-!
# Coercive construction of the compact scalar resolvent

The previous spectral gate accepts a bounded compact resolvent as analytic
input.  This file supplies a standard sufficient mechanism for constructing it.

For one shifted separated realization, assume:

* a positive lower norm bound `c * ‖u‖ ≤ ‖(A - lambda)u‖`;
* surjectivity of the shifted operator.

The lower bound gives injectivity and the canonical algebraic inverse has norm
at most `c⁻¹`.  It therefore upgrades to a continuous linear resolvent.  If the
inclusion of the separated domain into the ambient Hilbert space is compact,
the ambient resolvent is compact and the full spectral package follows.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCoerciveCompactResolvent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
open P0EFTJanusMappingTorusScalarClosedResolvent4D
open P0EFTJanusMappingTorusScalarCompactResolventSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Coercive-surjective analytic data for one shifted separated realization. -/
structure CanonicalScalarClosedCoerciveSurjectiveAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) where
  nondegenerate : a ≠ 0 ∨ b ≠ 0
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b,
    constant * ‖field‖ ≤
      ‖canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter field‖
  surjective : Function.Surjective
    (canonicalScalarClosedSeparatedShiftedOperator
      data hClosable traceBound a b spectralParameter)

/-- A positive lower bound forces injectivity of the shifted operator. -/
theorem CanonicalScalarClosedCoerciveSurjectiveAt.injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (coercive : CanonicalScalarClosedCoerciveSurjectiveAt
      data hClosable traceBound a b spectralParameter) :
    Function.Injective
      (canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter) := by
  intro first second hEqual
  have hZero :
      canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Coercivity plus surjectivity gives a resolvent point. -/
theorem CanonicalScalarClosedCoerciveSurjectiveAt.resolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (coercive : CanonicalScalarClosedCoerciveSurjectiveAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter :=
  ⟨coercive.injective data hClosable traceBound a b spectralParameter,
    coercive.surjective⟩

/-- Quantitative inverse estimate supplied by the coercive lower bound. -/
theorem CanonicalScalarClosedCoerciveSurjectiveAt.resolvent_norm_le
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (coercive : CanonicalScalarClosedCoerciveSurjectiveAt
      data hClosable traceBound a b spectralParameter)
    (source : Ambient) :
    ‖canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter
          (coercive.resolventPoint
            data hClosable traceBound a b spectralParameter) source‖ ≤
      coercive.constant⁻¹ * ‖source‖ := by
  have hBound := coercive.lower_bound
    (canonicalScalarClosedAlgebraicResolvent
      data hClosable traceBound a b spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound a b spectralParameter) source)
  rw [canonicalScalarClosedShiftedOperator_resolvent] at hBound
  calc
    ‖canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter
          (coercive.resolventPoint
            data hClosable traceBound a b spectralParameter) source‖ ≤
        ‖source‖ / coercive.constant :=
      (le_div_iff₀ coercive.constant_pos).2 (by
        simpa [mul_comm] using hBound)
    _ = coercive.constant⁻¹ * ‖source‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Continuous bounded resolvent constructed from coercivity and surjectivity. -/
noncomputable def CanonicalScalarClosedCoerciveSurjectiveAt.boundedResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (coercive : CanonicalScalarClosedCoerciveSurjectiveAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter where
  resolvent :=
    (canonicalScalarClosedAlgebraicResolvent
      data hClosable traceBound a b spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound a b spectralParameter)).mkContinuous
      coercive.constant⁻¹
      (coercive.resolvent_norm_le
        data hClosable traceBound a b spectralParameter)
  left_inverse := by
    intro source
    exact canonicalScalarClosedShiftedOperator_resolvent
      data hClosable traceBound a b spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound a b spectralParameter) source
  right_inverse := by
    intro field
    exact canonicalScalarClosedResolvent_shiftedOperator
      data hClosable traceBound a b spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound a b spectralParameter) field

@[simp] theorem CanonicalScalarClosedCoerciveSurjectiveAt.boundedResolvent_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (coercive : CanonicalScalarClosedCoerciveSurjectiveAt
      data hClosable traceBound a b spectralParameter)
    (source : Ambient) :
    (coercive.boundedResolvent
      data hClosable traceBound a b spectralParameter).resolvent source =
      canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter
          (coercive.resolventPoint
            data hClosable traceBound a b spectralParameter) source :=
  rfl

/-- Coercive data plus compact domain inclusion. -/
structure CanonicalScalarClosedCoerciveCompactEmbeddingAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) where
  coercive : CanonicalScalarClosedCoerciveSurjectiveAt
    data hClosable traceBound a b spectralParameter
  compact_inclusion : IsCompactOperator
    (canonicalScalarClosedSeparatedDomainInclusionCLM
      data hClosable traceBound a b)

/-- Compact ambient resolvent constructed by composing the compact domain
inclusion with the coercively bounded inverse. -/
theorem CanonicalScalarClosedCoerciveCompactEmbeddingAt.compact_ambientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compactData : CanonicalScalarClosedCoerciveCompactEmbeddingAt
      data hClosable traceBound a b spectralParameter) :
    IsCompactOperator
      (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
        data hClosable traceBound a b spectralParameter
          (compactData.coercive.boundedResolvent
            data hClosable traceBound a b spectralParameter)) := by
  simpa [CanonicalScalarClosedBoundedResolventAt.ambientResolvent,
    Function.comp_def] using
    compactData.compact_inclusion.comp_clm
      (compactData.coercive.boundedResolvent
        data hClosable traceBound a b spectralParameter).resolvent

/-- Canonical compact-resolvent spectral package produced by coercivity,
surjectivity and compact embedding. -/
noncomputable def CanonicalScalarClosedCoerciveCompactEmbeddingAt.compactResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compactData : CanonicalScalarClosedCoerciveCompactEmbeddingAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter where
  bounded := compactData.coercive.boundedResolvent
    data hClosable traceBound a b spectralParameter
  nondegenerate := compactData.coercive.nondegenerate
  compact_ambient := compactData.compact_ambientResolvent
    data hClosable traceBound a b spectralParameter

/-- Full coercive-to-spectral certificate. -/
theorem canonicalScalarClosedCoerciveCompactSpectrum_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compactData : CanonicalScalarClosedCoerciveCompactEmbeddingAt
      data hClosable traceBound a b spectralParameter) :
    (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
        data hClosable traceBound a b spectralParameter
          (compactData.coercive.boundedResolvent
            data hClosable traceBound a b spectralParameter)).toLinearMap.IsSymmetric ∧
      IsCompactOperator
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter
            (compactData.coercive.boundedResolvent
              data hClosable traceBound a b spectralParameter)) ∧
      (∀ eigenvalue : Real, eigenvalue ≠ 0 →
        FiniteDimensional Real
          (LinearMap.eigenspace
            (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
              data hClosable traceBound a b spectralParameter
                (compactData.coercive.boundedResolvent
                  data hClosable traceBound a b spectralParameter)).toLinearMap
              eigenvalue)) ∧
      (⨆ eigenvalue : Real,
        LinearMap.eigenspace
          (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
            data hClosable traceBound a b spectralParameter
              (compactData.coercive.boundedResolvent
                data hClosable traceBound a b spectralParameter)).toLinearMap
            eigenvalue)ᗮ = ⊥ :=
  canonicalScalarClosedCompactResolventSpectrum_certificate
    data hClosable traceBound a b spectralParameter
      (compactData.compactResolvent
        data hClosable traceBound a b spectralParameter)

end
end P0EFTJanusMappingTorusScalarCoerciveCompactResolvent4D
end JanusFormal
