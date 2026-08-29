import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalGraphFredholm4D

/-!
# Real realization of a complex diagonal Fredholm operator

The spectral coefficients are complex, while the physical variational
Hessian is real.  A real diagonal complex-linear multiplier therefore has a
canonical restriction to the underlying real Hilbert space.  This file proves
that maximal-domain self-adjointness and the finite-zero Fredholm criterion
survive that restriction of scalars.
-/

namespace JanusFormal
namespace P0EFTJanusComplexDiagonalRealFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D

variable (Mode : Type*) [DecidableEq Mode]

local instance complexDiagonalHilbertRealInnerProductSpace :
    InnerProductSpace Real (ComplexDiagonalHilbert Mode) :=
  InnerProductSpace.complexToReal

local instance complexDiagonalHilbertRealLinearPMapStar :
    Star (ComplexDiagonalHilbert Mode →ₗ.[Real]
      ComplexDiagonalHilbert Mode) :=
  LinearPMap.instStar

/-- The complex maximal domain regarded as a real submodule. -/
abbrev ComplexDiagonalRealDomain
    (weight : Mode → Real) :=
  (complexDiagonalDomain Mode weight).restrictScalars Real

/-- Forgetting the scalar restriction does not change a domain element. -/
def complexDiagonalRealToComplexDomain
    (weight : Mode → Real)
    (state : ComplexDiagonalRealDomain Mode weight) :
    complexDiagonalDomain Mode weight :=
  ⟨state.1, state.property⟩

/-- The same real-weighted multiplier on the underlying real Hilbert space. -/
def complexDiagonalRealOperator
    (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →ₗ.[Real]
      ComplexDiagonalHilbert Mode where
  domain := ComplexDiagonalRealDomain Mode weight
  toFun :=
    { toFun := fun state =>
        complexDiagonalOperator Mode weight
          (complexDiagonalRealToComplexDomain Mode weight state)
      map_add' := by
        intro first second
        ext mode
        simp [complexDiagonalRealToComplexDomain,
          complexDiagonalOperator_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [complexDiagonalRealToComplexDomain,
          complexDiagonalOperator_apply]
        ring }

@[simp]
theorem complexDiagonalRealOperator_apply
    (weight : Mode → Real)
    (state : (complexDiagonalRealOperator Mode weight).domain)
    (mode : Mode) :
    complexDiagonalRealOperator Mode weight state mode =
      (weight mode : Complex) * state.1 mode :=
  complexDiagonalOperator_apply Mode weight
    (complexDiagonalRealToComplexDomain Mode weight state) mode

theorem complexDiagonalRealDomain_dense
    (weight : Mode → Real) :
    Dense
      (ComplexDiagonalRealDomain Mode weight :
        Set (ComplexDiagonalHilbert Mode)) := by
  exact complexDiagonalDomain_dense Mode weight

theorem complexDiagonalRealOperator_isFormalAdjoint_self
    (weight : Mode → Real) :
    (complexDiagonalRealOperator Mode weight).IsFormalAdjoint
      (complexDiagonalRealOperator Mode weight) := by
  intro first second
  change
    (inner Complex
      (complexDiagonalOperator Mode weight
        (complexDiagonalRealToComplexDomain Mode weight first))
      (second : ComplexDiagonalHilbert Mode)).re =
    (inner Complex
      (first : ComplexDiagonalHilbert Mode)
      (complexDiagonalOperator Mode weight
        (complexDiagonalRealToComplexDomain Mode weight second))).re
  exact congrArg Complex.re
    (complexDiagonalOperator_isFormalAdjoint_self Mode weight
      (complexDiagonalRealToComplexDomain Mode weight first)
      (complexDiagonalRealToComplexDomain Mode weight second))

/-- Maximality is preserved after restricting the complex multiplier to real
scalars. -/
theorem complexDiagonalRealOperator_isSelfAdjoint
    (weight : Mode → Real) :
    IsSelfAdjoint (complexDiagonalRealOperator Mode weight) := by
  let realOperator := complexDiagonalRealOperator Mode weight
  let complexOperator := complexDiagonalOperator Mode weight
  have hDense :
      Dense
        (realOperator.domain :
          Set (ComplexDiagonalHilbert Mode)) :=
    complexDiagonalRealDomain_dense Mode weight
  have hSymmetric : realOperator.IsFormalAdjoint realOperator :=
    complexDiagonalRealOperator_isFormalAdjoint_self Mode weight
  have hOperatorLeAdjoint : realOperator ≤ realOperator.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjointDomain :
      realOperator.adjoint.domain ≤ realOperator.domain := by
    intro state hState
    let adjointState : realOperator.adjoint.domain := ⟨state, hState⟩
    let image : ComplexDiagonalHilbert Mode :=
      realOperator.adjoint adjointState
    have hComplexRelation :
        ∀ domainState : complexOperator.domain,
          inner Complex (complexOperator domainState) state =
            inner Complex
              (domainState : ComplexDiagonalHilbert Mode) image := by
      intro domainState
      let realDomainState : realOperator.domain :=
        ⟨domainState.1, domainState.property⟩
      have hReal :=
        (LinearPMap.adjoint_isFormalAdjoint hDense).symm
          realDomainState adjointState
      have hRealPart :
          (inner Complex (complexOperator domainState) state).re =
            (inner Complex
              (domainState : ComplexDiagonalHilbert Mode) image).re := by
        exact hReal
      let iDomainState : complexOperator.domain :=
        Complex.I • domainState
      let iRealDomainState : realOperator.domain :=
        ⟨(iDomainState : ComplexDiagonalHilbert Mode),
          iDomainState.property⟩
      have hImaginaryReal :=
        (LinearPMap.adjoint_isFormalAdjoint hDense).symm
          iRealDomainState adjointState
      have hImaginaryPart :
          (inner Complex (complexOperator domainState) state).im =
            (inner Complex
              (domainState : ComplexDiagonalHilbert Mode) image).im := by
        change
          (inner Complex
            (complexOperator iDomainState) state).re =
          (inner Complex
            (iDomainState : ComplexDiagonalHilbert Mode) image).re at hImaginaryReal
        rw [show complexOperator iDomainState =
            Complex.I • complexOperator domainState by
          exact LinearPMap.map_smul complexOperator Complex.I domainState]
          at hImaginaryReal
        simpa [iDomainState, inner_smul_left] using hImaginaryReal
      apply Complex.ext <;> assumption
    have hComplexAdjoint :
        state ∈ complexOperator.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨image, ?_⟩
      intro domainState
      have hRelation := hComplexRelation domainState
      calc
        inner Complex image
            (domainState : ComplexDiagonalHilbert Mode) =
            star (inner Complex
              (domainState : ComplexDiagonalHilbert Mode) image) :=
          (inner_conj_symm image
            (domainState : ComplexDiagonalHilbert Mode)).symm
        _ = star
            (inner Complex (complexOperator domainState) state) :=
          congrArg star hRelation.symm
        _ = inner Complex state (complexOperator domainState) :=
          inner_conj_symm state (complexOperator domainState)
    have hComplexSelf :
        complexOperator.adjoint = complexOperator :=
      LinearPMap.isSelfAdjoint_def.mp
        (complexDiagonalOperator_isSelfAdjoint Mode weight)
    rw [hComplexSelf] at hComplexAdjoint
    change state ∈ complexDiagonalDomain Mode weight
    exact hComplexAdjoint
  change realOperator.adjoint = realOperator
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

theorem complexDiagonalRealOperator_isClosed
    (weight : Mode → Real) :
    (complexDiagonalRealOperator Mode weight).IsClosed :=
  (complexDiagonalRealOperator_isSelfAdjoint Mode weight).isClosed

/-- Restriction of scalars does not change the ambient range. -/
theorem complexDiagonalRealOperator_range_eq_restrictScalars
    (weight : Mode → Real) :
    LinearMap.range (complexDiagonalRealOperator Mode weight).toFun =
      (LinearMap.range
        (complexDiagonalOperator Mode weight).toFun).restrictScalars Real := by
  ext output
  constructor
  · rintro ⟨state, hState⟩
    exact
      ⟨complexDiagonalRealToComplexDomain Mode weight state, hState⟩
  · rintro ⟨state, hState⟩
    exact ⟨⟨state.1, state.property⟩, hState⟩

theorem complexDiagonalRealOperator_range_isClosed_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
      (LinearMap.range (complexDiagonalRealOperator Mode weight).toFun :
        Set (ComplexDiagonalHilbert Mode)) := by
  rw [complexDiagonalRealOperator_range_eq_restrictScalars Mode weight]
  exact
    complexDiagonalOperator_range_isClosed_of_finiteZeroGap
      Mode weight data

/-- Real-linear zero-mode restriction on the real maximal kernel. -/
def complexDiagonalRealOperatorKernelZeroRestriction
    (weight : Mode → Real) :
    LinearMap.ker (complexDiagonalRealOperator Mode weight).toFun →ₗ[Real]
      (ComplexDiagonalZeroMode Mode weight → Complex) where
  toFun state mode := state.1.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexDiagonalRealOperatorKernelZeroRestriction_injective
    (weight : Mode → Real) :
    Function.Injective
      (complexDiagonalRealOperatorKernelZeroRestriction Mode weight) := by
  intro first second hCoordinates
  apply Subtype.ext
  apply Subtype.ext
  ext mode
  by_cases hZero : weight mode = 0
  · exact congrFun hCoordinates
      (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
  · have hFirstAt :
        (complexDiagonalRealOperator Mode weight first.1) mode = 0 := by
      have hImage :
          complexDiagonalRealOperator Mode weight first.1 = 0 :=
        first.property
      exact congrArg
        (fun state : ComplexDiagonalHilbert Mode => state mode) hImage
    have hSecondAt :
        (complexDiagonalRealOperator Mode weight second.1) mode = 0 := by
      have hImage :
          complexDiagonalRealOperator Mode weight second.1 = 0 :=
        second.property
      exact congrArg
        (fun state : ComplexDiagonalHilbert Mode => state mode) hImage
    rw [complexDiagonalRealOperator_apply] at hFirstAt hSecondAt
    have hWeight : (weight mode : Complex) ≠ 0 := by
      exact_mod_cast hZero
    exact
      ((mul_eq_zero.mp hFirstAt).resolve_left hWeight).trans
        ((mul_eq_zero.mp hSecondAt).resolve_left hWeight).symm

theorem complexDiagonalRealOperator_kernel_finite_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Real
      (LinearMap.ker (complexDiagonalRealOperator Mode weight).toFun) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  exact FiniteDimensional.of_injective
    (complexDiagonalRealOperatorKernelZeroRestriction Mode weight)
    (complexDiagonalRealOperatorKernelZeroRestriction_injective Mode weight)

/-- Real algebraic cokernel of the maximal multiplier. -/
abbrev ComplexDiagonalRealOperatorCokernel
    (weight : Mode → Real) :=
  ComplexDiagonalHilbert Mode ⧸
    LinearMap.range (complexDiagonalRealOperator Mode weight).toFun

theorem complexDiagonalRealOperator_cokernel_finite_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Real
      (ComplexDiagonalRealOperatorCokernel Mode weight) := by
  let complexRange :=
    LinearMap.range (complexDiagonalOperator Mode weight).toFun
  have hRange :
      LinearMap.range (complexDiagonalRealOperator Mode weight).toFun =
        complexRange.restrictScalars Real :=
    complexDiagonalRealOperator_range_eq_restrictScalars Mode weight
  let realRange :=
    LinearMap.range (complexDiagonalRealOperator Mode weight).toFun
  letI : FiniteDimensional Complex
      (ComplexDiagonalHilbert Mode ⧸ complexRange) :=
    complexDiagonalOperator_cokernel_finite_of_finiteZeroGap
      Mode weight data
  letI : FiniteDimensional Real
      (ComplexDiagonalHilbert Mode ⧸ complexRange) :=
    FiniteDimensional.complexToReal _
  let rangeQuotientEquiv :
      (ComplexDiagonalHilbert Mode ⧸ realRange) ≃ₗ[Real]
        (ComplexDiagonalHilbert Mode ⧸
          complexRange.restrictScalars Real) :=
    Submodule.quotEquivOfEq _ _ hRange
  let scalarEquiv :
      (ComplexDiagonalHilbert Mode ⧸
          complexRange.restrictScalars Real) ≃ₗ[Real]
        (ComplexDiagonalHilbert Mode ⧸ complexRange) :=
    Submodule.Quotient.restrictScalarsEquiv Real complexRange
  exact (rangeQuotientEquiv.trans scalarEquiv).symm.finiteDimensional

/-- Complete real Fredholm criterion for the maximal complex coefficient
multiplier. -/
theorem complexDiagonalRealOperator_fredholm_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
        (LinearMap.range (complexDiagonalRealOperator Mode weight).toFun :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Real
        (LinearMap.ker (complexDiagonalRealOperator Mode weight).toFun) ∧
      FiniteDimensional Real
        (ComplexDiagonalRealOperatorCokernel Mode weight) :=
  ⟨complexDiagonalRealOperator_range_isClosed_of_finiteZeroGap
      Mode weight data,
    complexDiagonalRealOperator_kernel_finite_of_finiteZeroGap
      Mode weight data,
    complexDiagonalRealOperator_cokernel_finite_of_finiteZeroGap
      Mode weight data⟩

end
end P0EFTJanusComplexDiagonalRealFredholm4D
end JanusFormal
