import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Resolvent calculus for arbitrary scalar Lagrangian boundaries

The preceding gate unifies Dirichlet, Neumann, separated Robin and bounded
operator-valued Robin conditions as closed Lagrangian subspaces of the paired
Hilbert trace space.  This file transports the complete resolvent construction
to an arbitrary such condition.

It defines the shifted closed operator, its real resolvent set and spectrum,
constructs the algebraic inverse at a resolvent point, packages bounded
resolvents, proves symmetry of the ambient resolvent, and derives a bounded
inverse directly from a coercive lower bound plus surjectivity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianResolvent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Shifted operator `A_L - lambda I` on an arbitrary closed Lagrangian
boundary domain. -/
noncomputable def canonicalScalarClosedLagrangianShiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →ₗ[Real] Ambient :=
  canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition -
    spectralParameter • canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition

@[simp] theorem canonicalScalarClosedLagrangianShiftedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter field =
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field -
        spectralParameter •
          canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field :=
  rfl

/-- Real resolvent point for an arbitrary Lagrangian realization. -/
def CanonicalScalarClosedLagrangianResolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) : Prop :=
  Function.Bijective
    (canonicalScalarClosedLagrangianShiftedOperator
      data hClosable traceBound condition spectralParameter)

/-- Real resolvent set of an arbitrary Lagrangian realization. -/
def canonicalScalarClosedLagrangianResolventSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) : Set Real :=
  {spectralParameter |
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter}

/-- Real spectrum of an arbitrary Lagrangian realization. -/
def canonicalScalarClosedLagrangianSpectrum
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) : Set Real :=
  (canonicalScalarClosedLagrangianResolventSet
    data hClosable traceBound condition)ᶜ

@[simp] theorem mem_canonicalScalarClosedLagrangianResolventSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    spectralParameter ∈ canonicalScalarClosedLagrangianResolventSet
        data hClosable traceBound condition ↔
      CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition spectralParameter :=
  Iff.rfl

@[simp] theorem mem_canonicalScalarClosedLagrangianSpectrum
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    spectralParameter ∈ canonicalScalarClosedLagrangianSpectrum
        data hClosable traceBound condition ↔
      ¬ CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition spectralParameter :=
  Iff.rfl

/-- Linear equivalence supplied by an abstract Lagrangian resolvent point. -/
noncomputable def canonicalScalarClosedLagrangianShiftedOperatorEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition ≃ₗ[Real] Ambient :=
  LinearEquiv.ofBijective
    (canonicalScalarClosedLagrangianShiftedOperator
      data hClosable traceBound condition spectralParameter) hPoint

/-- Domain-valued algebraic resolvent. -/
noncomputable def canonicalScalarClosedLagrangianAlgebraicResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter) :
    Ambient →ₗ[Real]
      canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :=
  (canonicalScalarClosedLagrangianShiftedOperatorEquiv
    data hClosable traceBound condition spectralParameter hPoint).symm.toLinearMap

/-- Ambient algebraic resolvent. -/
noncomputable def canonicalScalarClosedLagrangianAmbientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter) :
    Ambient →ₗ[Real] Ambient :=
  (canonicalScalarClosedLagrangianDomainInclusion
    data hClosable traceBound condition).comp
      (canonicalScalarClosedLagrangianAlgebraicResolvent
        data hClosable traceBound condition spectralParameter hPoint)

@[simp] theorem canonicalScalarClosedLagrangianShiftedOperator_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter)
    (source : Ambient) :
    canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter
        (canonicalScalarClosedLagrangianAlgebraicResolvent
          data hClosable traceBound condition spectralParameter hPoint source) =
      source := by
  change (canonicalScalarClosedLagrangianShiftedOperatorEquiv
      data hClosable traceBound condition spectralParameter hPoint)
      ((canonicalScalarClosedLagrangianShiftedOperatorEquiv
        data hClosable traceBound condition spectralParameter hPoint).symm source) = source
  exact LinearEquiv.apply_symm_apply _ source

@[simp] theorem canonicalScalarClosedLagrangianResolvent_shiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianAlgebraicResolvent
        data hClosable traceBound condition spectralParameter hPoint
        (canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter field) =
      field := by
  change (canonicalScalarClosedLagrangianShiftedOperatorEquiv
      data hClosable traceBound condition spectralParameter hPoint).symm
      ((canonicalScalarClosedLagrangianShiftedOperatorEquiv
        data hClosable traceBound condition spectralParameter hPoint) field) = field
  exact LinearEquiv.symm_apply_apply _ field

/-- Continuous inclusion of an abstract Lagrangian domain into the ambient
Hilbert space. -/
def canonicalScalarClosedLagrangianDomainInclusionCLM
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →L[Real] Ambient :=
  (canonicalScalarClosedOperatorDomain data).subtypeL.comp
    (canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition).subtypeL

/-- Bounded inverse interface at one real spectral parameter. -/
structure CanonicalScalarClosedLagrangianBoundedResolventAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  resolvent : Ambient →L[Real]
    canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition
  left_inverse : ∀ source : Ambient,
    canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter (resolvent source) = source
  right_inverse : ∀ field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    resolvent (canonicalScalarClosedLagrangianShiftedOperator
      data hClosable traceBound condition spectralParameter field) = field

/-- A bounded inverse supplies a resolvent point. -/
theorem CanonicalScalarClosedLagrangianBoundedResolventAt.resolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter := by
  constructor
  · intro first second hEqual
    calc
      first = bounded.resolvent
          (canonicalScalarClosedLagrangianShiftedOperator
            data hClosable traceBound condition spectralParameter first) :=
        (bounded.right_inverse first).symm
      _ = bounded.resolvent
          (canonicalScalarClosedLagrangianShiftedOperator
            data hClosable traceBound condition spectralParameter second) := by rw [hEqual]
      _ = second := bounded.right_inverse second
  · intro source
    exact ⟨bounded.resolvent source, bounded.left_inverse source⟩

/-- Ambient bounded resolvent. -/
def CanonicalScalarClosedLagrangianBoundedResolventAt.ambientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    Ambient →L[Real] Ambient :=
  (canonicalScalarClosedLagrangianDomainInclusionCLM
    data hClosable traceBound condition).comp bounded.resolvent

/-- Bounded ambient resolvents of Lagrangian realizations are symmetric. -/
theorem canonicalScalarClosedLagrangianAmbientResolvent_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    (bounded.ambientResolvent
      data hClosable traceBound condition spectralParameter).toLinearMap.IsSymmetric := by
  intro source test
  let first := bounded.resolvent source
  let second := bounded.resolvent test
  have hOperatorSymmetric :=
    canonicalScalarClosedLagrangianDomainOperator_symmetric
      data hClosable traceBound condition first second
  have hShiftedSymmetric :
      inner Real
          (canonicalScalarClosedLagrangianShiftedOperator
            data hClosable traceBound condition spectralParameter first)
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition second) =
        inner Real
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition first)
          (canonicalScalarClosedLagrangianShiftedOperator
            data hClosable traceBound condition spectralParameter second) := by
    rw [canonicalScalarClosedLagrangianShiftedOperator_apply,
      canonicalScalarClosedLagrangianShiftedOperator_apply,
      inner_sub_left, inner_sub_right, hOperatorSymmetric]
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [bounded.left_inverse source, bounded.left_inverse test] at hShiftedSymmetric
  exact hShiftedSymmetric.symm

/-- Coercive-surjective data for one abstract Lagrangian shifted operator. -/
structure CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    constant * ‖field‖ ≤
      ‖canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter field‖
  surjective : Function.Surjective
    (canonicalScalarClosedLagrangianShiftedOperator
      data hClosable traceBound condition spectralParameter)

/-- Coercivity forces injectivity. -/
theorem CanonicalScalarClosedLagrangianCoerciveSurjectiveAt.injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
      data hClosable traceBound condition spectralParameter) :
    Function.Injective
      (canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter) := by
  intro first second hEqual
  have hZero :
      canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Coercivity and surjectivity give a resolvent point. -/
theorem CanonicalScalarClosedLagrangianCoerciveSurjectiveAt.resolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
      data hClosable traceBound condition spectralParameter) :
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter :=
  ⟨coercive.injective data hClosable traceBound condition spectralParameter,
    coercive.surjective⟩

/-- Norm estimate for the canonical inverse. -/
theorem CanonicalScalarClosedLagrangianCoerciveSurjectiveAt.resolvent_norm_le
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
      data hClosable traceBound condition spectralParameter)
    (source : Ambient) :
    ‖canonicalScalarClosedLagrangianAlgebraicResolvent
        data hClosable traceBound condition spectralParameter
          (coercive.resolventPoint
            data hClosable traceBound condition spectralParameter) source‖ ≤
      coercive.constant⁻¹ * ‖source‖ := by
  have hBound := coercive.lower_bound
    (canonicalScalarClosedLagrangianAlgebraicResolvent
      data hClosable traceBound condition spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound condition spectralParameter) source)
  rw [canonicalScalarClosedLagrangianShiftedOperator_resolvent] at hBound
  calc
    ‖canonicalScalarClosedLagrangianAlgebraicResolvent
        data hClosable traceBound condition spectralParameter
          (coercive.resolventPoint
            data hClosable traceBound condition spectralParameter) source‖ ≤
        ‖source‖ / coercive.constant :=
      (le_div_iff₀ coercive.constant_pos).2 (by
        simpa [mul_comm] using hBound)
    _ = coercive.constant⁻¹ * ‖source‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Bounded resolvent constructed from a coercive-surjective package. -/
noncomputable def CanonicalScalarClosedLagrangianCoerciveSurjectiveAt.boundedResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
      data hClosable traceBound condition spectralParameter) :
    CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter where
  resolvent :=
    (canonicalScalarClosedLagrangianAlgebraicResolvent
      data hClosable traceBound condition spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound condition spectralParameter)).mkContinuous
      coercive.constant⁻¹
      (coercive.resolvent_norm_le
        data hClosable traceBound condition spectralParameter)
  left_inverse := by
    intro source
    exact canonicalScalarClosedLagrangianShiftedOperator_resolvent
      data hClosable traceBound condition spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound condition spectralParameter) source
  right_inverse := by
    intro field
    exact canonicalScalarClosedLagrangianResolvent_shiftedOperator
      data hClosable traceBound condition spectralParameter
        (coercive.resolventPoint
          data hClosable traceBound condition spectralParameter) field

/-- Resolvent closure certificate for an arbitrary Lagrangian condition. -/
theorem canonicalScalarLagrangianResolvent_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition spectralParameter ∧
      (bounded.ambientResolvent
        data hClosable traceBound condition spectralParameter).toLinearMap.IsSymmetric :=
  ⟨bounded.resolventPoint
      data hClosable traceBound condition spectralParameter,
    canonicalScalarClosedLagrangianAmbientResolvent_isSymmetric
      data hClosable traceBound condition spectralParameter bounded⟩

end
end P0EFTJanusMappingTorusScalarLagrangianResolvent4D
end JanusFormal
