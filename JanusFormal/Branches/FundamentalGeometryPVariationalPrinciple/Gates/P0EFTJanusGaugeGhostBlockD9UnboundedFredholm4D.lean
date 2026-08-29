import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalGraphFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketHilbertFredholm4D

/-!
# Maximal unbounded Fredholm realization of the D9 gauge--ghost block

The complete D9 symbol is a differential multiplier and therefore need not
be bounded above.  This gate realizes it on its maximal `ℓ²` domain.  A
positive lower spectral gap is the only ellipticity hypothesis: it gives a
bounded inverse while allowing the symbol to grow without bound.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- Eight complexified D9 gauge--ghost coordinates over every mode. -/
abbrev D9GaugeGhostUnboundedHilbert (ι : Type*) :=
  ComplexDiagonalHilbert (ι × Fin 8)

/-- Exact D9 diagonal weight. -/
def d9GaugeGhostUnboundedWeight
    {ι : Type*} (covector : ι → TangentVector3)
    (index : ι × Fin 8) : Real :=
  normSquared (covector index.1)

/-- Maximal graph domain of the complete D9 differential symbol. -/
abbrev D9GaugeGhostUnboundedDomain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :=
  complexDiagonalDomain (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

/-- Complete maximal-domain D9 gauge--ghost operator. -/
abbrev d9GaugeGhostUnboundedOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :=
  complexDiagonalOperator (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

@[simp]
theorem d9GaugeGhostUnboundedOperator_apply
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (state : D9GaugeGhostUnboundedDomain covector)
    (index : ι × Fin 8) :
    d9GaugeGhostUnboundedOperator covector state index =
      (normSquared (covector index.1) : Complex) * state.1 index :=
  complexDiagonalOperator_apply (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector) state index

/-- Honest ellipticity condition for the unbounded D9 symbol.  No upper
bound is imposed. -/
structure D9GaugeGhostUnboundedEllipticity
    {ι : Type*} (covector : ι → TangentVector3) where
  gap : Real
  gap_pos : 0 < gap
  weight_gap :
    ∀ mode, gap ≤ |normSquared (covector mode)|

theorem d9GaugeGhostUnbounded_weight_gap
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector)
    (index : ι × Fin 8) :
    ellipticity.gap ≤
      |d9GaugeGhostUnboundedWeight covector index| :=
  ellipticity.weight_gap index.1

theorem d9GaugeGhostUnboundedDomain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :
    Dense
      (D9GaugeGhostUnboundedDomain covector :
        Set (D9GaugeGhostUnboundedHilbert ι)) :=
  complexDiagonalDomain_dense (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

theorem d9GaugeGhostUnboundedOperator_isSelfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :
    IsSelfAdjoint (d9GaugeGhostUnboundedOperator covector) :=
  complexDiagonalOperator_isSelfAdjoint (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

theorem d9GaugeGhostUnboundedOperator_isClosed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :
    (d9GaugeGhostUnboundedOperator covector).IsClosed :=
  complexDiagonalOperator_isClosed (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

/-- Bounded inverse of the maximal D9 operator. -/
abbrev d9GaugeGhostUnboundedInverse
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :=
  complexDiagonalInverseCLM (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

theorem d9GaugeGhostUnboundedInverse_norm_le
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    ‖d9GaugeGhostUnboundedInverse ellipticity‖ ≤ ellipticity.gap⁻¹ :=
  complexDiagonalInverseCLM_norm_le (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

theorem d9GaugeGhostUnboundedOperator_injective
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    Function.Injective (d9GaugeGhostUnboundedOperator covector) :=
  complexDiagonalOperator_injective_of_gap (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

theorem d9GaugeGhostUnboundedOperator_surjective
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    Function.Surjective (d9GaugeGhostUnboundedOperator covector) :=
  complexDiagonalOperator_surjective_of_gap (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

theorem d9GaugeGhostUnboundedOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    IsClosed
        (LinearMap.range
          (d9GaugeGhostUnboundedOperator covector).toFun :
          Set (D9GaugeGhostUnboundedHilbert ι)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (d9GaugeGhostUnboundedOperator covector).toFun) ∧
      FiniteDimensional Complex
        (D9GaugeGhostUnboundedHilbert ι ⧸
          LinearMap.range
            (d9GaugeGhostUnboundedOperator covector).toFun) :=
  complexDiagonalOperator_fredholm_of_gap (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

theorem d9GaugeGhostUnboundedOperator_index_zero
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    (d9GaugeGhostUnboundedOperator covector).toFun.index = 0 :=
  complexDiagonalOperatorIndex_zero_of_gap (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.gap ellipticity.gap_pos
    (d9GaugeGhostUnbounded_weight_gap ellipticity)

/-- Consolidated maximal-domain D9 Fredholm certificate. -/
structure D9GaugeGhostUnboundedFredholmCertificate
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) : Prop where
  domainDense :
    Dense
      (D9GaugeGhostUnboundedDomain covector :
        Set (D9GaugeGhostUnboundedHilbert ι))
  selfAdjoint :
    IsSelfAdjoint (d9GaugeGhostUnboundedOperator covector)
  closed :
    (d9GaugeGhostUnboundedOperator covector).IsClosed
  inverseNorm :
    ‖d9GaugeGhostUnboundedInverse ellipticity‖ ≤ ellipticity.gap⁻¹
  injective :
    Function.Injective (d9GaugeGhostUnboundedOperator covector)
  surjective :
    Function.Surjective (d9GaugeGhostUnboundedOperator covector)
  indexZero :
    (d9GaugeGhostUnboundedOperator covector).toFun.index = 0

def d9GaugeGhostUnboundedFredholmCertificate
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostUnboundedEllipticity covector) :
    D9GaugeGhostUnboundedFredholmCertificate ellipticity where
  domainDense := d9GaugeGhostUnboundedDomain_dense covector
  selfAdjoint := d9GaugeGhostUnboundedOperator_isSelfAdjoint covector
  closed := d9GaugeGhostUnboundedOperator_isClosed covector
  inverseNorm := d9GaugeGhostUnboundedInverse_norm_le ellipticity
  injective := d9GaugeGhostUnboundedOperator_injective ellipticity
  surjective := d9GaugeGhostUnboundedOperator_surjective ellipticity
  indexZero := d9GaugeGhostUnboundedOperator_index_zero ellipticity

/-- Ellipticity modulo finitely many characteristic D9 coordinates.  This is
the Fredholm hypothesis needed when genuine zero modes are retained. -/
structure D9GaugeGhostFiniteCharacteristicEllipticity
    {ι : Type*} (covector : ι → TangentVector3) where
  gap : Real
  gap_pos : 0 < gap
  gap_le :
    ∀ mode, normSquared (covector mode) ≠ 0 →
      gap ≤ |normSquared (covector mode)|
  characteristicFinite :
    Finite
      {index : ι × Fin 8 //
        d9GaugeGhostUnboundedWeight covector index = 0}

def D9GaugeGhostFiniteCharacteristicEllipticity.toFiniteZeroGap
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    ComplexDiagonalFiniteZeroGap (ι × Fin 8)
      (d9GaugeGhostUnboundedWeight covector) where
  gap := ellipticity.gap
  gap_pos := ellipticity.gap_pos
  gap_le := by
    intro index hNonzero
    exact ellipticity.gap_le index.1 hNonzero
  zeroModeFinite := ellipticity.characteristicFinite

/-- Graph-norm D9 domain, valid with a finite characteristic kernel. -/
abbrev D9GaugeGhostGraphDomain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :=
  ComplexDiagonalGraphDomain (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

/-- Bounded graph realization of the same unbounded D9 multiplier. -/
abbrev d9GaugeGhostGraphOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3) :=
  complexDiagonalGraphOperatorCLM (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)

@[simp]
theorem d9GaugeGhostGraphOperator_apply
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (state : D9GaugeGhostGraphDomain covector) :
    d9GaugeGhostGraphOperator covector state = state.1.2 :=
  rfl

theorem d9GaugeGhostGraphOperator_range_isClosed
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsClosed
      (LinearMap.range
        (d9GaugeGhostGraphOperator covector).toLinearMap :
        Set (D9GaugeGhostUnboundedHilbert ι)) :=
  complexDiagonalGraphOperator_range_isClosed (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.toFiniteZeroGap

theorem d9GaugeGhostGraphOperator_kernel_finite
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    FiniteDimensional Complex
      (LinearMap.ker
        (d9GaugeGhostGraphOperator covector).toLinearMap) :=
  complexDiagonalGraphOperator_kernel_finite (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.toFiniteZeroGap

theorem d9GaugeGhostGraphOperator_cokernel_finite
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    FiniteDimensional Complex
      (D9GaugeGhostUnboundedHilbert ι ⧸
        LinearMap.range
          (d9GaugeGhostGraphOperator covector).toLinearMap) :=
  complexDiagonalGraphOperator_cokernel_finite (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.toFiniteZeroGap

/-- Terminal D9 Fredholm theorem with finite kernel and cokernel. -/
theorem d9GaugeGhostGraphOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsClosed
        (LinearMap.range
          (d9GaugeGhostGraphOperator covector).toLinearMap :
          Set (D9GaugeGhostUnboundedHilbert ι)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (d9GaugeGhostGraphOperator covector).toLinearMap) ∧
      FiniteDimensional Complex
        (D9GaugeGhostUnboundedHilbert ι ⧸
          LinearMap.range
            (d9GaugeGhostGraphOperator covector).toLinearMap) :=
  complexDiagonalGraphOperator_fredholm (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.toFiniteZeroGap

/-- The genuine maximal D9 operator is Fredholm even when the finite
characteristic kernel is retained. -/
theorem d9GaugeGhostUnboundedOperator_fredholm_of_finiteCharacteristic
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsClosed
        (LinearMap.range
          (d9GaugeGhostUnboundedOperator covector).toFun :
          Set (D9GaugeGhostUnboundedHilbert ι)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (d9GaugeGhostUnboundedOperator covector).toFun) ∧
      FiniteDimensional Complex
        (D9GaugeGhostUnboundedHilbert ι ⧸
          LinearMap.range
            (d9GaugeGhostUnboundedOperator covector).toFun) :=
  complexDiagonalOperator_fredholm_of_finiteZeroGap (ι × Fin 8)
    (d9GaugeGhostUnboundedWeight covector)
    ellipticity.toFiniteZeroGap

end
end P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
end JanusFormal
