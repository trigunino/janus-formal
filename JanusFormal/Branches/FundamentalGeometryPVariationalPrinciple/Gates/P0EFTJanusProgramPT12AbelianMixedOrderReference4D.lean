import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalProperShiftFredholm4D

/-! Maximal mixed-order reference for the signed nonminimal Abelian symbol.
The auxiliary multiplier is -1, not a second-order Laplacian. The paired
reference retains twelve complex mode coordinates. No geometric Fourier
transform or global H11 identification is assumed or asserted here. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianMixedOrderReference4D

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D

attribute [local instance]
  complexDiagonalHilbertRealInnerProductSpace
  complexDiagonalHilbertRealLinearPMapStar

def abelianMixedOrderWeight {iota : Type*} (covector : iota → TangentVector3)
    (mode : iota × Fin 6) : Real :=
  abelianNonminimalSignedWeight (covector mode.1) mode.2

theorem abelianNonminimalSignedWeight_zero_iff (covector : TangentVector3)
    (component : Fin 6) :
    abelianNonminimalSignedWeight covector component = 0 ↔
      component ≠ 3 ∧ normSquared covector = 0 := by
  fin_cases component <;> simp [abelianNonminimalSignedWeight]

/-- The five differential coordinates can vanish at characteristic modes;
the auxiliary coordinate never contributes a kernel vector. -/
def abelianMixedOrderFiniteZeroGap {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    ComplexDiagonalFiniteZeroGap (iota × Fin 6) (abelianMixedOrderWeight covector) where
  gap := min 1 (ellipticity.gap / 2)
  gap_pos := lt_min (by norm_num) (half_pos ellipticity.gap_pos)
  gap_le := by
    rintro ⟨mode, component⟩ hNonzero
    fin_cases component <;>
      simp [abelianMixedOrderWeight, abelianNonminimalSignedWeight, abs_div] at hNonzero ⊢
    all_goals first
      | exact min_le_left _ _
      | have hGap := ellipticity.gap_le mode hNonzero
        apply Or.inr
        linarith [ellipticity.gap_pos]
  zeroModeFinite := by
    letI := ellipticity.characteristicFinite
    let embedZero : ComplexDiagonalZeroMode (iota × Fin 6) (abelianMixedOrderWeight covector) →
        ComplexDiagonalZeroMode (iota × Fin 8) (d9GaugeGhostUnboundedWeight covector) :=
      fun mode => ⟨(mode.1.1, Fin.castLE (by decide) mode.1.2),
        ((abelianNonminimalSignedWeight_zero_iff _ _).mp mode.2).2⟩
    apply Finite.of_injective embedZero
    intro first second hEqual
    apply Subtype.ext
    have hPair := congrArg (fun mode : ComplexDiagonalZeroMode
      (iota × Fin 8) (d9GaugeGhostUnboundedWeight covector) => mode.1) hEqual
    apply Prod.ext
    · exact congrArg (fun mode : iota × Fin 8 => mode.1) hPair
    · apply Fin.ext
      exact congrArg (fun mode : iota × Fin 8 => mode.2.val) hPair

abbrev PairedAbelianMixedOrderMode (iota : Type*) := Fin 2 × (iota × Fin 6)

def pairedAbelianMixedOrderWeight {iota : Type*} (covector : iota → TangentVector3)
    (mode : PairedAbelianMixedOrderMode iota) : Real :=
  abelianMixedOrderWeight covector mode.2

def pairedAbelianMixedOrderFiniteZeroGap {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    ComplexDiagonalFiniteZeroGap (PairedAbelianMixedOrderMode iota)
      (pairedAbelianMixedOrderWeight covector) :=
  complexDiagonalFiniteZeroGap_finiteProduct _ _ (abelianMixedOrderFiniteZeroGap ellipticity)

abbrev pairedAbelianMixedOrderOperator {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :=
  complexDiagonalRealOperator (PairedAbelianMixedOrderMode iota)
    (pairedAbelianMixedOrderWeight covector)

theorem pairedAbelianMixedOrderOperator_dense {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    Dense ((pairedAbelianMixedOrderOperator covector).domain :
      Set (ComplexDiagonalHilbert (PairedAbelianMixedOrderMode iota))) :=
  complexDiagonalRealDomain_dense _ _

theorem pairedAbelianMixedOrderOperator_selfAdjoint {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    IsSelfAdjoint (pairedAbelianMixedOrderOperator covector) :=
  complexDiagonalRealOperator_isSelfAdjoint _ _

theorem pairedAbelianMixedOrderOperator_closed {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    (pairedAbelianMixedOrderOperator covector).IsClosed :=
  complexDiagonalRealOperator_isClosed _ _

theorem pairedAbelianMixedOrderOperator_fredholm {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsClosed (LinearMap.range (pairedAbelianMixedOrderOperator covector).toFun :
      Set (ComplexDiagonalHilbert (PairedAbelianMixedOrderMode iota))) ∧
    FiniteDimensional Real (LinearMap.ker (pairedAbelianMixedOrderOperator covector).toFun) ∧
    FiniteDimensional Real (ComplexDiagonalRealOperatorCokernel
      (PairedAbelianMixedOrderMode iota) (pairedAbelianMixedOrderWeight covector)) :=
  complexDiagonalRealOperator_fredholm_of_finiteZeroGap _ _
    (pairedAbelianMixedOrderFiniteZeroGap ellipticity)

end
end P0EFTJanusProgramPT12AbelianMixedOrderReference4D
end JanusFormal
