import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D

/-!
# Coercive construction of the graph Dirichlet resolvent

The completed graph carries a closed Dirichlet submodule, namely the kernel of
the completed value trace.  Restricting the shifted graph relation to this
submodule gives the Dirichlet boundary-value operator.

A positive lower norm bound and surjectivity make this restricted operator
bijective.  Its inverse is bounded by the reciprocal coercivity constant and
therefore supplies the full `CanonicalScalarGraphDirichletResolventData` used by
the Poisson, Weyl and Krein constructions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Shifted graph relation restricted to the completed Dirichlet domain. -/
def canonicalScalarGraphDirichletShiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real) :
    canonicalScalarCompletedDirichletDomainSubmodule
        data traceBound →L[Real] Ambient :=
  (canonicalScalarGraphShiftedOperator data spectralParameter).comp
    (canonicalScalarCompletedDirichletDomainSubmodule
      data traceBound).subtypeL

@[simp] theorem canonicalScalarGraphDirichletShiftedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (field : canonicalScalarCompletedDirichletDomainSubmodule data traceBound) :
    canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter field =
      canonicalScalarGraphShiftedOperator data spectralParameter field.1 :=
  rfl

/-- Coercive-surjective Dirichlet graph problem. -/
structure CanonicalScalarGraphDirichletCoerciveSurjectiveData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real) where
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ field : canonicalScalarCompletedDirichletDomainSubmodule
      data traceBound,
    constant * ‖field‖ ≤
      ‖canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter field‖
  surjective : Function.Surjective
    (canonicalScalarGraphDirichletShiftedOperator
      data traceBound spectralParameter)

/-- Coercivity gives injectivity of the Dirichlet shifted operator. -/
theorem CanonicalScalarGraphDirichletCoerciveSurjectiveData.injective
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Function.Injective
      (canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter) := by
  intro first second hEqual
  have hZero : canonicalScalarGraphDirichletShiftedOperator
      data traceBound spectralParameter (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Bijectivity of the restricted Dirichlet shifted operator. -/
theorem CanonicalScalarGraphDirichletCoerciveSurjectiveData.bijective
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Function.Bijective
      (canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter) :=
  ⟨coercive.injective, coercive.surjective⟩

/-- Dirichlet shifted operator as a linear equivalence. -/
noncomputable def CanonicalScalarGraphDirichletCoerciveSurjectiveData.equiv
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    canonicalScalarCompletedDirichletDomainSubmodule data traceBound ≃ₗ[Real]
      Ambient :=
  LinearEquiv.ofBijective
    (canonicalScalarGraphDirichletShiftedOperator
      data traceBound spectralParameter).toLinearMap coercive.bijective

/-- Algebraic Dirichlet inverse. -/
noncomputable def CanonicalScalarGraphDirichletCoerciveSurjectiveData.algebraicResolvent
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Ambient →ₗ[Real]
      canonicalScalarCompletedDirichletDomainSubmodule data traceBound :=
  coercive.equiv.symm.toLinearMap

@[simp] theorem CanonicalScalarGraphDirichletCoerciveSurjectiveData.shift_resolvent
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter)
    (source : Ambient) :
    canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter
        (coercive.algebraicResolvent source) = source :=
  coercive.equiv.apply_symm_apply source

@[simp] theorem CanonicalScalarGraphDirichletCoerciveSurjectiveData.resolvent_shift
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter)
    (field : canonicalScalarCompletedDirichletDomainSubmodule data traceBound) :
    coercive.algebraicResolvent
        (canonicalScalarGraphDirichletShiftedOperator
          data traceBound spectralParameter field) = field :=
  coercive.equiv.symm_apply_apply field

/-- Reciprocal inverse bound. -/
theorem CanonicalScalarGraphDirichletCoerciveSurjectiveData.resolvent_norm_le
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter)
    (source : Ambient) :
    ‖coercive.algebraicResolvent source‖ ≤
      coercive.constant⁻¹ * ‖source‖ := by
  have hBound := coercive.lower_bound (coercive.algebraicResolvent source)
  rw [coercive.shift_resolvent] at hBound
  calc
    ‖coercive.algebraicResolvent source‖ ≤ ‖source‖ / coercive.constant :=
      (le_div_iff₀ coercive.constant_pos).2 (by
        simpa [mul_comm] using hBound)
    _ = coercive.constant⁻¹ * ‖source‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Continuous Dirichlet inverse with values in the Dirichlet submodule. -/
noncomputable def CanonicalScalarGraphDirichletCoerciveSurjectiveData.resolvent
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Ambient →L[Real]
      canonicalScalarCompletedDirichletDomainSubmodule data traceBound :=
  coercive.algebraicResolvent.mkContinuous
    coercive.constant⁻¹ coercive.resolvent_norm_le

/-- Continuous graph-valued Dirichlet resolvent. -/
noncomputable def CanonicalScalarGraphDirichletCoerciveSurjectiveData.graphResolvent
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Ambient →L[Real] CanonicalScalarOperatorGraphSpace data :=
  (canonicalScalarCompletedDirichletDomainSubmodule
    data traceBound).subtypeL.comp coercive.resolvent

/-- Construction of the complete graph Dirichlet resolvent package. -/
noncomputable def CanonicalScalarGraphDirichletCoerciveSurjectiveData.toDirichletResolventData
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter where
  resolvent := coercive.graphResolvent
  equation := by
    intro source
    exact coercive.shift_resolvent source
  value_zero := by
    intro source
    exact (coercive.resolvent source).2
  unique := by
    intro field source hEquation hValue
    let dirichletField : canonicalScalarCompletedDirichletDomainSubmodule
        data traceBound := ⟨field,
      (mem_canonicalScalarCompletedDirichletDomainSubmodule
        data traceBound field).2 hValue⟩
    apply Subtype.ext_iff.mp
    have hInverse := coercive.resolvent_shift dirichletField
    rw [show canonicalScalarGraphDirichletShiftedOperator
        data traceBound spectralParameter dirichletField = source by
      exact hEquation] at hInverse
    exact congrArg Subtype.val hInverse

/-- Coercive Dirichlet resolvent certificate. -/
theorem canonicalScalarGraphDirichletCoerciveResolvent_certificate
    (coercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
      data traceBound spectralParameter) :
    Function.Bijective
        (canonicalScalarGraphDirichletShiftedOperator
          data traceBound spectralParameter) ∧
      (∀ source : Ambient,
        canonicalScalarGraphShiftedOperator data spectralParameter
          ((coercive.toDirichletResolventData).resolvent source) = source) ∧
      (∀ source : Ambient,
        canonicalScalarCompletedValueTrace data traceBound
          ((coercive.toDirichletResolventData).resolvent source) = 0) :=
  ⟨coercive.bijective,
    (coercive.toDirichletResolventData).equation,
    (coercive.toDirichletResolventData).value_zero⟩

end
end P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
end JanusFormal
