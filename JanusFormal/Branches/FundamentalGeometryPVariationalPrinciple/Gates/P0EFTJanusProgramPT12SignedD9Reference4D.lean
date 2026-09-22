import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalProperShiftFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D

/-! Signed doubling of the reference D9 multiplier and the exact Abelian
nonminimal symbol pairing. This is not a geometric actual-to-modal map. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12SignedD9Reference4D

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
open P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D

attribute [local instance]
  complexDiagonalHilbertRealInnerProductSpace
  complexDiagonalHilbertRealLinearPMapStar

abbrev SignedD9Mode (iota : Type*) := (iota × Fin 8) ⊕ (iota × Fin 8)

def signedD9Weight {iota : Type*} (covector : iota → TangentVector3) :
    SignedD9Mode iota → Real :=
  complexDiagonalSumWeight (d9GaugeGhostUnboundedWeight covector)
    (fun mode => -d9GaugeGhostUnboundedWeight covector mode)

@[simp] theorem signedD9Weight_positive {iota : Type*}
    (covector : iota → TangentVector3) (mode : iota × Fin 8) :
    signedD9Weight covector (.inl mode) = normSquared (covector mode.1) := rfl

@[simp] theorem signedD9Weight_negative {iota : Type*}
    (covector : iota → TangentVector3) (mode : iota × Fin 8) :
    signedD9Weight covector (.inr mode) = -normSquared (covector mode.1) := rfl

private def negFiniteZeroGap {Mode : Type*} {weight : Mode → Real}
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    ComplexDiagonalFiniteZeroGap Mode (fun mode => -weight mode) where
  gap := data.gap
  gap_pos := data.gap_pos
  gap_le := by
    intro mode hNonzero
    simpa only [abs_neg] using data.gap_le mode (by
      intro hZero
      exact hNonzero (by simp [hZero]))
  zeroModeFinite := by
    letI := data.zeroModeFinite
    let forget : ComplexDiagonalZeroMode Mode (fun mode => -weight mode) →
        ComplexDiagonalZeroMode Mode weight :=
      fun mode => ⟨mode.1, neg_eq_zero.mp mode.2⟩
    exact Finite.of_injective forget (by
      intro first second hEqual
      exact Subtype.ext (congrArg
        (fun mode : ComplexDiagonalZeroMode Mode weight => mode.1) hEqual))

/-- Sign doubling keeps the same absolute gap and a finite doubled kernel. -/
def signedD9FiniteZeroGap {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    ComplexDiagonalFiniteZeroGap (SignedD9Mode iota) (signedD9Weight covector) :=
  complexDiagonalFiniteZeroGap_sum _ _ ellipticity.toFiniteZeroGap
    (negFiniteZeroGap ellipticity.toFiniteZeroGap)

abbrev signedD9Operator {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :=
  complexDiagonalRealOperator (SignedD9Mode iota) (signedD9Weight covector)

theorem signedD9Operator_dense {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    Dense ((signedD9Operator covector).domain :
      Set (ComplexDiagonalHilbert (SignedD9Mode iota))) :=
  complexDiagonalRealDomain_dense _ _

theorem signedD9Operator_selfAdjoint {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    IsSelfAdjoint (signedD9Operator covector) :=
  complexDiagonalRealOperator_isSelfAdjoint _ _

theorem signedD9Operator_closed {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    (signedD9Operator covector).IsClosed :=
  complexDiagonalRealOperator_isClosed _ _

theorem signedD9Operator_fredholm {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsClosed (LinearMap.range (signedD9Operator covector).toFun :
      Set (ComplexDiagonalHilbert (SignedD9Mode iota))) ∧
    FiniteDimensional Real (LinearMap.ker (signedD9Operator covector).toFun) ∧
    FiniteDimensional Real (ComplexDiagonalRealOperatorCokernel
      (SignedD9Mode iota) (signedD9Weight covector)) :=
  complexDiagonalRealOperator_fredholm_of_finiteZeroGap _ _
    (signedD9FiniteZeroGap ellipticity)

/-- The real nonminimal Abelian symbol has both signs. Neither B nor either
ghost coefficient is discarded by completing these squares. -/
theorem d9AbelianHessian_signed_pairing (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionHessian covector first second =
      divergenceSymbol covector first.potential *
        divergenceSymbol covector second.potential -
      (first.nakanishiLautrup.coefficient - divergenceSymbol covector first.potential) *
        (second.nakanishiLautrup.coefficient - divergenceSymbol covector second.potential) +
      (normSquared covector / 2) *
        ((first.antighost.coefficient + first.ghost.coefficient) *
            (second.antighost.coefficient + second.ghost.coefficient) -
          (first.antighost.coefficient - first.ghost.coefficient) *
            (second.antighost.coefficient - second.ghost.coefficient)) := by
  unfold d9AbelianGaugeFermionHessian
  ring

end
end P0EFTJanusProgramPT12SignedD9Reference4D
end JanusFormal
