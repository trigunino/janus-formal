import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalRealFredholm4D

/-!
# Native real self-adjointness of the complex diagonal operator

The native real inner product on complex `ℓ²` is the sum of the coordinate
real inner products.  It equals the real part of the complex `ℓ²` inner
product, although Mathlib intentionally does not make the two structures
definitionally equal.
-/

namespace JanusFormal
namespace P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalRealFredholm4D

variable (Mode : Type*) [DecidableEq Mode]

local instance complexDiagonalNativeRealLinearPMapStar :
    Star (ComplexDiagonalHilbert Mode →ₗ.[Real]
      ComplexDiagonalHilbert Mode) :=
  LinearPMap.instStar

theorem complexDiagonalNativeReal_inner_eq_re
    (first second : ComplexDiagonalHilbert Mode) :
    inner Real first second = (inner Complex first second).re := by
  change (∑' mode, inner Real (first mode) (second mode)) =
    (∑' mode, inner Complex (first mode) (second mode)).re
  calc
    (∑' mode, inner Real (first mode) (second mode)) =
        ∑' mode, (inner Complex (first mode) (second mode)).re := by
      congr 1
    _ = (∑' mode, inner Complex (first mode) (second mode)).re :=
      (RCLike.reCLM.map_tsum
        (lp.summable_inner (𝕜 := Complex) first second)).symm

theorem complexDiagonalNativeRealOperator_isFormalAdjoint_self
    (weight : Mode → Real) :
    (complexDiagonalRealOperator Mode weight).IsFormalAdjoint
      (complexDiagonalRealOperator Mode weight) := by
  intro first second
  rw [complexDiagonalNativeReal_inner_eq_re,
    complexDiagonalNativeReal_inner_eq_re]
  exact congrArg Complex.re
    (complexDiagonalOperator_isFormalAdjoint_self Mode weight
      (complexDiagonalRealToComplexDomain Mode weight first)
      (complexDiagonalRealToComplexDomain Mode weight second))

theorem complexDiagonalNativeRealOperator_isSelfAdjoint
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
    complexDiagonalNativeRealOperator_isFormalAdjoint_self Mode weight
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
        rw [← complexDiagonalNativeReal_inner_eq_re,
          ← complexDiagonalNativeReal_inner_eq_re]
        exact hReal
      let iDomainState : complexOperator.domain :=
        Complex.I • domainState
      let iRealDomainState : realOperator.domain :=
        ⟨(iDomainState : ComplexDiagonalHilbert Mode),
          iDomainState.property⟩
      have hImaginaryReal :=
        (LinearPMap.adjoint_isFormalAdjoint hDense).symm
          iRealDomainState adjointState
      have hImaginaryRealPart :
          (inner Complex (complexOperator iDomainState) state).re =
            (inner Complex
              (iDomainState : ComplexDiagonalHilbert Mode) image).re := by
        rw [← complexDiagonalNativeReal_inner_eq_re,
          ← complexDiagonalNativeReal_inner_eq_re]
        exact hImaginaryReal
      have hImaginaryPart :
          (inner Complex (complexOperator domainState) state).im =
            (inner Complex
              (domainState : ComplexDiagonalHilbert Mode) image).im := by
        rw [show complexOperator iDomainState =
            Complex.I • complexOperator domainState by
          exact LinearPMap.map_smul complexOperator Complex.I domainState]
          at hImaginaryRealPart
        simpa [iDomainState, inner_smul_left] using hImaginaryRealPart
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

end
end P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D
end JanusFormal
