import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D

/-!
# Resolvent calculus for the closed scalar realizations

This file develops the algebraic resolvent of every closed separated scalar
realization.  For a real spectral parameter `lambda` it defines the shifted
operator `A - lambda`, the resolvent set and spectrum, the inverse equivalence at
a resolvent point, and the ambient resolvent obtained by including the inverse
back into the Hilbert space.

A second interface packages a bounded resolvent as an actual continuous linear
map.  This keeps the analytic inverse estimate explicit while proving that any
such package agrees with the canonical algebraic inverse.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarClosedResolvent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Shifted closed separated operator `A - lambda I`. -/
noncomputable def canonicalScalarClosedSeparatedShiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) :
    canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b →ₗ[Real] Ambient :=
  canonicalScalarClosedSeparatedDomainOperator
      data hClosable traceBound a b -
    spectralParameter • canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b

@[simp] theorem canonicalScalarClosedSeparatedShiftedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b) :
    canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter field =
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field -
        spectralParameter •
          canonicalScalarClosedSeparatedDomainInclusion
            data hClosable traceBound a b field :=
  rfl

/-- A real spectral parameter belongs to the resolvent set when the shifted
closed separated operator is bijective. -/
def CanonicalScalarClosedResolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) : Prop :=
  Function.Bijective
    (canonicalScalarClosedSeparatedShiftedOperator
      data hClosable traceBound a b spectralParameter)

/-- Real resolvent set of the chosen separated realization. -/
def canonicalScalarClosedResolventSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) : Set Real :=
  {spectralParameter |
    CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter}

/-- Real spectrum, defined as the complement of the real resolvent set. -/
def canonicalScalarClosedSpectrum
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) : Set Real :=
  (canonicalScalarClosedResolventSet
    data hClosable traceBound a b)ᶜ

@[simp] theorem mem_canonicalScalarClosedResolventSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) :
    spectralParameter ∈ canonicalScalarClosedResolventSet
        data hClosable traceBound a b ↔
      CanonicalScalarClosedResolventPoint
        data hClosable traceBound a b spectralParameter :=
  Iff.rfl

@[simp] theorem mem_canonicalScalarClosedSpectrum
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) :
    spectralParameter ∈ canonicalScalarClosedSpectrum
        data hClosable traceBound a b ↔
      ¬ CanonicalScalarClosedResolventPoint
        data hClosable traceBound a b spectralParameter :=
  Iff.rfl

/-- Linear equivalence supplied by a resolvent point. -/
noncomputable def canonicalScalarClosedShiftedOperatorEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b ≃ₗ[Real] Ambient :=
  LinearEquiv.ofBijective
    (canonicalScalarClosedSeparatedShiftedOperator
      data hClosable traceBound a b spectralParameter) hPoint

/-- Canonical algebraic resolvent with values in the operator domain. -/
noncomputable def canonicalScalarClosedAlgebraicResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    Ambient →ₗ[Real]
      canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b :=
  (canonicalScalarClosedShiftedOperatorEquiv
    data hClosable traceBound a b spectralParameter hPoint).symm.toLinearMap

/-- Ambient resolvent obtained by including the domain-valued inverse into the
Hilbert space. -/
noncomputable def canonicalScalarClosedAmbientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    Ambient →ₗ[Real] Ambient :=
  (canonicalScalarClosedSeparatedDomainInclusion
    data hClosable traceBound a b).comp
      (canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter hPoint)

@[simp] theorem canonicalScalarClosedShiftedOperator_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter)
    (source : Ambient) :
    canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter
        (canonicalScalarClosedAlgebraicResolvent
          data hClosable traceBound a b spectralParameter hPoint source) =
      source := by
  change (canonicalScalarClosedShiftedOperatorEquiv
      data hClosable traceBound a b spectralParameter hPoint)
      ((canonicalScalarClosedShiftedOperatorEquiv
        data hClosable traceBound a b spectralParameter hPoint).symm source) = source
  exact LinearEquiv.apply_symm_apply _ source

@[simp] theorem canonicalScalarClosedResolvent_shiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter)
    (field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b) :
    canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter hPoint
        (canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter field) =
      field := by
  change (canonicalScalarClosedShiftedOperatorEquiv
      data hClosable traceBound a b spectralParameter hPoint).symm
      ((canonicalScalarClosedShiftedOperatorEquiv
        data hClosable traceBound a b spectralParameter hPoint) field) = field
  exact LinearEquiv.symm_apply_apply _ field

/-- The canonical domain-valued resolvent is injective. -/
theorem canonicalScalarClosedAlgebraicResolvent_injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    Function.Injective
      (canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter hPoint) :=
  (canonicalScalarClosedShiftedOperatorEquiv
    data hClosable traceBound a b spectralParameter hPoint).symm.injective

/-- The canonical domain-valued resolvent is surjective. -/
theorem canonicalScalarClosedAlgebraicResolvent_surjective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    Function.Surjective
      (canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter hPoint) :=
  (canonicalScalarClosedShiftedOperatorEquiv
    data hClosable traceBound a b spectralParameter hPoint).symm.surjective

/-- Ambient inclusion of every closed separated domain is injective. -/
theorem canonicalScalarClosedSeparatedDomainInclusion_injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    Function.Injective
      (canonicalScalarClosedSeparatedDomainInclusion
        data hClosable traceBound a b) := by
  intro first second hEqual
  apply Subtype.ext
  apply Subtype.ext
  exact hEqual

/-- The ambient resolvent is injective. -/
theorem canonicalScalarClosedAmbientResolvent_injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    Function.Injective
      (canonicalScalarClosedAmbientResolvent
        data hClosable traceBound a b spectralParameter hPoint) := by
  intro first second hEqual
  have hDomain := canonicalScalarClosedSeparatedDomainInclusion_injective
    data hClosable traceBound a b hEqual
  exact canonicalScalarClosedAlgebraicResolvent_injective
    data hClosable traceBound a b spectralParameter hPoint hDomain

/-- At a resolvent point the shifted operator has trivial kernel. -/
theorem canonicalScalarClosedShiftedOperator_ker_eq_bot
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    LinearMap.ker
        (canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter) = ⊥ :=
  LinearMap.ker_eq_bot.mpr hPoint.1

/-- At a resolvent point the shifted operator has full range. -/
theorem canonicalScalarClosedShiftedOperator_range_eq_top
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hPoint : CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter) :
    LinearMap.range
        (canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter) = ⊤ :=
  LinearMap.range_eq_top.mpr hPoint.2

/-- Invertibility package at spectral parameter zero. -/
structure CanonicalScalarClosedZeroResolventData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) where
  nondegenerate : a ≠ 0 ∨ b ≠ 0
  zero_is_resolvent : CanonicalScalarClosedResolventPoint
    data hClosable traceBound a b 0

/-- A zero-resolvent package places zero in the real resolvent set. -/
theorem CanonicalScalarClosedZeroResolventData.zero_mem_resolventSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real)
    (zeroData : CanonicalScalarClosedZeroResolventData
      data hClosable traceBound a b) :
    0 ∈ canonicalScalarClosedResolventSet
      data hClosable traceBound a b :=
  zeroData.zero_is_resolvent

/-- Continuous inclusion of a separated closed domain into the ambient Hilbert
space. -/
def canonicalScalarClosedSeparatedDomainInclusionCLM
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b →L[Real] Ambient :=
  (canonicalScalarClosedOperatorDomain data).subtypeL.comp
    (canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b).subtypeL

/-- Bounded resolvent interface at one spectral parameter. -/
structure CanonicalScalarClosedBoundedResolventAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) where
  resolvent : Ambient →L[Real]
    canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b
  left_inverse : ∀ source : Ambient,
    canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter (resolvent source) = source
  right_inverse : ∀ field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b,
    resolvent (canonicalScalarClosedSeparatedShiftedOperator
      data hClosable traceBound a b spectralParameter field) = field

/-- Every bounded resolvent package supplies an algebraic resolvent point. -/
theorem CanonicalScalarClosedBoundedResolventAt.resolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedResolventPoint
      data hClosable traceBound a b spectralParameter := by
  constructor
  · intro first second hEqual
    calc
      first = bounded.resolvent
          (canonicalScalarClosedSeparatedShiftedOperator
            data hClosable traceBound a b spectralParameter first) :=
        (bounded.right_inverse first).symm
      _ = bounded.resolvent
          (canonicalScalarClosedSeparatedShiftedOperator
            data hClosable traceBound a b spectralParameter second) := by rw [hEqual]
      _ = second := bounded.right_inverse second
  · intro source
    exact ⟨bounded.resolvent source, bounded.left_inverse source⟩

/-- Ambient bounded resolvent. -/
def CanonicalScalarClosedBoundedResolventAt.ambientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) :
    Ambient →L[Real] Ambient :=
  (canonicalScalarClosedSeparatedDomainInclusionCLM
    data hClosable traceBound a b).comp bounded.resolvent

/-- The continuous resolvent agrees with the canonical algebraic inverse. -/
theorem CanonicalScalarClosedBoundedResolventAt.toLinearMap_eq_algebraicResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) :
    bounded.resolvent.toLinearMap =
      canonicalScalarClosedAlgebraicResolvent
        data hClosable traceBound a b spectralParameter
          (bounded.resolventPoint data hClosable traceBound a b spectralParameter) := by
  apply LinearMap.ext
  intro source
  apply (bounded.resolventPoint
    data hClosable traceBound a b spectralParameter).1
  rw [bounded.left_inverse,
    canonicalScalarClosedShiftedOperator_resolvent]

end
end P0EFTJanusMappingTorusScalarClosedResolvent4D
end JanusFormal
