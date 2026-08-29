import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D

/-!
# Direct resolvent calculus on a completed scalar boundary triple

The corrected physical architecture already has a complete maximal graph and a
surjective completed Cauchy trace.  There is no analytic need to close that graph
a second time before defining the resolvent.

This file therefore develops the shifted operator and bounded resolvent directly
on a completed Lagrangian submodule.  Coercivity and surjectivity construct the
inverse with the reciprocal norm estimate, while the Green identity proves
symmetry of the ambient resolvent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Direct shifted operator `A_L - lambda I` on the completed Lagrangian
submodule. -/
def lagrangianShiftedOperator
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    triple.lagrangianDomainSubmodule condition →L[Real] Ambient :=
  triple.lagrangianOperator condition +
    (-spectralParameter) • triple.lagrangianInclusion condition

@[simp] theorem lagrangianShiftedOperator_apply
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (field : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianShiftedOperator condition spectralParameter field =
      triple.lagrangianOperator condition field -
        spectralParameter • triple.lagrangianInclusion condition field :=
  by
    simp [lagrangianShiftedOperator, sub_eq_add_neg]

/-- Direct real resolvent point. -/
def LagrangianResolventPoint
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) : Prop :=
  Function.Bijective
    (triple.lagrangianShiftedOperator condition spectralParameter)

/-- Direct real resolvent set. -/
def lagrangianResolventSet
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set Real :=
  {spectralParameter |
    triple.LagrangianResolventPoint condition spectralParameter}

/-- Direct real spectrum. -/
def lagrangianSpectrum
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set Real :=
  (triple.lagrangianResolventSet condition)ᶜ

/-- Linear equivalence at a direct resolvent point. -/
noncomputable def lagrangianShiftedEquiv
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : triple.LagrangianResolventPoint
      condition spectralParameter) :
    triple.lagrangianDomainSubmodule condition ≃ₗ[Real] Ambient :=
  LinearEquiv.ofBijective
    (triple.lagrangianShiftedOperator
      condition spectralParameter).toLinearMap hPoint

/-- Domain-valued algebraic resolvent. -/
noncomputable def lagrangianAlgebraicResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : triple.LagrangianResolventPoint
      condition spectralParameter) :
    Ambient →ₗ[Real] triple.lagrangianDomainSubmodule condition :=
  (triple.lagrangianShiftedEquiv
    condition spectralParameter hPoint).symm.toLinearMap

@[simp] theorem shifted_algebraicResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : triple.LagrangianResolventPoint
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianShiftedOperator condition spectralParameter
        (triple.lagrangianAlgebraicResolvent
          condition spectralParameter hPoint source) = source :=
  LinearEquiv.apply_symm_apply
    (triple.lagrangianShiftedEquiv
      condition spectralParameter hPoint) source

@[simp] theorem algebraicResolvent_shifted
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (hPoint : triple.LagrangianResolventPoint
      condition spectralParameter)
    (field : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianAlgebraicResolvent condition spectralParameter hPoint
        (triple.lagrangianShiftedOperator
          condition spectralParameter field) = field :=
  LinearEquiv.symm_apply_apply
    (triple.lagrangianShiftedEquiv
      condition spectralParameter hPoint) field

/-- Bounded direct resolvent. -/
structure LagrangianBoundedResolventAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  resolvent : Ambient →L[Real]
    triple.lagrangianDomainSubmodule condition
  left_inverse : ∀ source : Ambient,
    triple.lagrangianShiftedOperator condition spectralParameter
      (resolvent source) = source
  right_inverse : ∀ field : triple.lagrangianDomainSubmodule condition,
    resolvent
      (triple.lagrangianShiftedOperator
        condition spectralParameter field) = field

/-- A bounded direct inverse gives a resolvent point. -/
theorem LagrangianBoundedResolventAt.resolventPoint
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    triple.LagrangianResolventPoint condition spectralParameter := by
  constructor
  · intro first second hEqual
    calc
      first = bounded.resolvent
          (triple.lagrangianShiftedOperator
            condition spectralParameter first) :=
        (bounded.right_inverse first).symm
      _ = bounded.resolvent
          (triple.lagrangianShiftedOperator
            condition spectralParameter second) := by rw [hEqual]
      _ = second := bounded.right_inverse second
  · intro source
    exact ⟨bounded.resolvent source, bounded.left_inverse source⟩

/-- Ambient direct resolvent. -/
def LagrangianBoundedResolventAt.ambientResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    Ambient →L[Real] Ambient :=
  (triple.lagrangianInclusion condition).comp bounded.resolvent

/-- The direct ambient resolvent is symmetric. -/
theorem LagrangianBoundedResolventAt.ambient_isSymmetric
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    (bounded.ambientResolvent
      triple condition spectralParameter).toLinearMap.IsSymmetric := by
  intro source test
  let first := bounded.resolvent source
  let second := bounded.resolvent test
  have hOperator := triple.lagrangianOperator_symmetric
    condition first second
  have hShifted :
      inner Real
          (triple.lagrangianShiftedOperator
            condition spectralParameter first)
          (triple.lagrangianInclusion condition second) =
        inner Real
          (triple.lagrangianInclusion condition first)
          (triple.lagrangianShiftedOperator
            condition spectralParameter second) := by
    rw [triple.lagrangianShiftedOperator_apply,
      triple.lagrangianShiftedOperator_apply,
      inner_sub_left, inner_sub_right, hOperator]
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [bounded.left_inverse source, bounded.left_inverse test] at hShifted
  exact hShifted.symm

/-- Coercive-surjective data for a direct completed-triple realization. -/
structure LagrangianCoerciveSurjectiveAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ field : triple.lagrangianDomainSubmodule condition,
    constant * ‖field‖ ≤
      ‖triple.lagrangianShiftedOperator
        condition spectralParameter field‖
  surjective : Function.Surjective
    (triple.lagrangianShiftedOperator condition spectralParameter)

/-- Coercivity gives injectivity. -/
theorem LagrangianCoerciveSurjectiveAt.injective
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianCoerciveSurjectiveAt
      condition spectralParameter) :
    Function.Injective
      (triple.lagrangianShiftedOperator
        condition spectralParameter) := by
  intro first second hEqual
  have hZero :
      triple.lagrangianShiftedOperator condition spectralParameter
        (first - second) = 0 := by
    calc
      triple.lagrangianShiftedOperator condition spectralParameter
          (first - second) =
          triple.lagrangianShiftedOperator condition spectralParameter first -
            triple.lagrangianShiftedOperator condition spectralParameter second :=
        (triple.lagrangianShiftedOperator
          condition spectralParameter).map_sub first second
      _ = 0 := by rw [hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Coercivity and surjectivity give a direct resolvent point. -/
theorem LagrangianCoerciveSurjectiveAt.resolventPoint
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianCoerciveSurjectiveAt
      condition spectralParameter) :
    triple.LagrangianResolventPoint condition spectralParameter :=
  ⟨coercive.injective triple condition spectralParameter,
    coercive.surjective⟩

/-- Reciprocal norm estimate for the direct algebraic inverse. -/
theorem LagrangianCoerciveSurjectiveAt.resolvent_norm_le
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianCoerciveSurjectiveAt
      condition spectralParameter)
    (source : Ambient) :
    ‖triple.lagrangianAlgebraicResolvent condition spectralParameter
        (coercive.resolventPoint triple condition spectralParameter) source‖ ≤
      coercive.constant⁻¹ * ‖source‖ := by
  have hBound := coercive.lower_bound
    (triple.lagrangianAlgebraicResolvent condition spectralParameter
      (coercive.resolventPoint triple condition spectralParameter) source)
  rw [triple.shifted_algebraicResolvent] at hBound
  calc
    ‖triple.lagrangianAlgebraicResolvent condition spectralParameter
        (coercive.resolventPoint triple condition spectralParameter) source‖ ≤
        ‖source‖ / coercive.constant :=
      (le_div_iff₀ coercive.constant_pos).2 (by
        simpa [mul_comm] using hBound)
    _ = coercive.constant⁻¹ * ‖source‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Bounded direct resolvent constructed from coercivity and surjectivity. -/
noncomputable def LagrangianCoerciveSurjectiveAt.boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianCoerciveSurjectiveAt
      condition spectralParameter) :
    triple.LagrangianBoundedResolventAt condition spectralParameter where
  resolvent :=
    by
      let algebraic : Ambient →ₗ[Real]
          triple.lagrangianDomainSubmodule condition :=
        triple.lagrangianAlgebraicResolvent condition spectralParameter
          (coercive.resolventPoint triple condition spectralParameter)
      refine ⟨algebraic, AddMonoidHomClass.continuous_of_bound
        algebraic coercive.constant⁻¹ ?_⟩
      intro source
      change ‖triple.lagrangianAlgebraicResolvent condition spectralParameter
          (coercive.resolventPoint triple condition spectralParameter) source‖ ≤
        coercive.constant⁻¹ * ‖source‖
      exact coercive.resolvent_norm_le
        triple condition spectralParameter source
  left_inverse := by
    intro source
    exact triple.shifted_algebraicResolvent condition spectralParameter
      (coercive.resolventPoint triple condition spectralParameter) source
  right_inverse := by
    intro field
    exact triple.algebraicResolvent_shifted condition spectralParameter
      (coercive.resolventPoint triple condition spectralParameter) field

/-- Direct resolvent certificate. -/
theorem directLagrangianResolvent_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    triple.LagrangianResolventPoint condition spectralParameter ∧
      (bounded.ambientResolvent
        triple condition spectralParameter).toLinearMap.IsSymmetric :=
  ⟨bounded.resolventPoint triple condition spectralParameter,
    bounded.ambient_isSymmetric triple condition spectralParameter⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
