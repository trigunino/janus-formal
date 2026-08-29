import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketCokernelEquiv4D

/-!
# Hilbert--Fredholm realization of the finite D9 gauge--ghost packet

The algebraic finite-packet symbol is conjugated to an operator on the genuine
finite Hilbert sum of its eight real coordinates.  The resulting operator is
self-adjoint, has closed range, finite kernel and cokernel, and index zero.
This is a finite Galerkin block, not the global gauge-fixed Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketHilbertFredholm4D

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketFredholmIndex4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketCokernelEquiv4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- The eight real gauge--ghost coordinates with their Euclidean norm. -/
abbrev D9GaugeGhostHilbertCoordinate :=
  EuclideanSpace Real (Fin 8)

/-- Flatten the existing `3 + 5` D9 coordinate without changing its data. -/
def d9GaugeGhostLinearCoordinateEquivHilbert :
    D9GaugeGhostLinearCoordinate ≃ₗ[Real] D9GaugeGhostHilbertCoordinate where
  toFun coordinate :=
    WithLp.toLp 2
      ![coordinate.1.1, coordinate.1.2.1, coordinate.1.2.2,
        coordinate.2.1, coordinate.2.2.1, coordinate.2.2.2.1,
        coordinate.2.2.2.2.1, coordinate.2.2.2.2.2]
  invFun coordinate :=
    ((coordinate 0, coordinate 1, coordinate 2),
      (coordinate 3,
        (coordinate 4, coordinate 5, coordinate 6, coordinate 7)))
  left_inv coordinate := by
    rfl
  right_inv coordinate := by
    apply PiLp.ext
    intro index
    fin_cases index <;> rfl
  map_add' first second := by
    apply PiLp.ext
    intro index
    fin_cases index <;> rfl
  map_smul' scalar coordinate := by
    apply PiLp.ext
    intro index
    fin_cases index <;> rfl

/-- Finite Hilbert sum of all D9 packet coordinates. -/
abbrev D9GaugeGhostFinitePacketHilbert (ι : Type*) [Fintype ι] :=
  EuclideanSpace Real (ι × Fin 8)

/-- The canonical linear identification of the algebraic packet with its
finite Hilbert renorming. -/
def d9GaugeGhostFinitePacketEquivHilbert
    (ι : Type*) [Fintype ι] :
    D9GaugeGhostFinitePacket ι ≃ₗ[Real]
      D9GaugeGhostFinitePacketHilbert ι where
  toFun packet :=
    WithLp.toLp 2
      (fun index =>
        d9GaugeGhostLinearCoordinateEquivHilbert
          (packet index.1) index.2)
  invFun packet mode :=
    d9GaugeGhostLinearCoordinateEquivHilbert.symm
      (WithLp.toLp 2 (fun coordinate => packet (mode, coordinate)))
  left_inv packet := by
    funext mode
    exact d9GaugeGhostLinearCoordinateEquivHilbert.left_inv (packet mode)
  right_inv packet := by
    apply PiLp.ext
    intro index
    simp only [LinearEquiv.apply_symm_apply]
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact congrArg
      (fun coordinate : D9GaugeGhostHilbertCoordinate => coordinate index.2)
      (map_add d9GaugeGhostLinearCoordinateEquivHilbert
        (first index.1) (second index.1))
  map_smul' scalar packet := by
    apply PiLp.ext
    intro index
    exact congrArg
      (fun coordinate : D9GaugeGhostHilbertCoordinate => coordinate index.2)
      (map_smul d9GaugeGhostLinearCoordinateEquivHilbert
        scalar (packet index.1))

/-- Algebraic packet symbol conjugated to the finite Hilbert sum. -/
def d9GaugeGhostFinitePacketHilbertLinearMap
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketHilbert ι →ₗ[Real]
      D9GaugeGhostFinitePacketHilbert ι where
  toFun packet :=
    WithLp.toLp 2
      (fun index => normSquared (covector index.1) • packet index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact smul_add _ _ _
  map_smul' scalar packet := by
    apply PiLp.ext
    intro index
    simp only [PiLp.smul_apply, smul_smul, RingHom.id_apply]
    rw [mul_comm]

/-- Continuous Hilbert realization of the finite D9 packet symbol. -/
def d9GaugeGhostFinitePacketHilbertOperator
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketHilbert ι →L[Real]
      D9GaugeGhostFinitePacketHilbert ι :=
  LinearMap.toContinuousLinearMap
    (d9GaugeGhostFinitePacketHilbertLinearMap covector)

@[simp]
theorem d9GaugeGhostFinitePacketHilbertOperator_apply
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacketHilbert ι) (index : ι × Fin 8) :
    d9GaugeGhostFinitePacketHilbertOperator covector packet index =
      normSquared (covector index.1) • packet index := by
  rfl

/-- The Hilbert operator is exactly the old packet operator after the
canonical renorming. -/
theorem d9GaugeGhostFinitePacketHilbertOperator_conjugates
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketHilbertOperator covector
        (d9GaugeGhostFinitePacketEquivHilbert ι packet) =
      d9GaugeGhostFinitePacketEquivHilbert ι
        (d9GaugeGhostFinitePacketSymbol covector packet) := by
  apply PiLp.ext
  intro index
  exact congrArg
    (fun coordinate : D9GaugeGhostHilbertCoordinate => coordinate index.2)
    (map_smul d9GaugeGhostLinearCoordinateEquivHilbert
      (normSquared (covector index.1)) (packet index.1)).symm

/-- Real diagonal multiplication makes the finite packet self-adjoint. -/
theorem d9GaugeGhostFinitePacketHilbertOperator_isSelfAdjoint
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    IsSelfAdjoint
      (d9GaugeGhostFinitePacketHilbertOperator covector) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro index _
  change
    ⟪normSquared (covector index.1) • first index, second index⟫_Real =
      ⟪first index, normSquared (covector index.1) • second index⟫_Real
  rw [real_inner_smul_left, real_inner_smul_right]

/-- The range is closed because it is a subspace of a finite-dimensional
Hilbert packet. -/
theorem d9GaugeGhostFinitePacketHilbertOperator_range_isClosed
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    IsClosed
      (LinearMap.range
        (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap :
        Set (D9GaugeGhostFinitePacketHilbert ι)) :=
  (LinearMap.range
    (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap
    ).closed_of_finiteDimensional

/-- Every endomorphism of this finite Hilbert packet has Fredholm index zero. -/
theorem d9GaugeGhostFinitePacketHilbertOperator_index_zero
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap.index = 0 := by
  rw [LinearMap.index_eq_of_finiteDimensional]
  simp

/-- Exact finite Hilbert--Fredholm certificate used by the Hessian frontier. -/
structure D9GaugeGhostFinitePacketHilbertFredholmCertificate
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) : Prop where
  conjugatesAlgebraic :
    ∀ packet,
      d9GaugeGhostFinitePacketHilbertOperator covector
          (d9GaugeGhostFinitePacketEquivHilbert ι packet) =
        d9GaugeGhostFinitePacketEquivHilbert ι
          (d9GaugeGhostFinitePacketSymbol covector packet)
  selfAdjoint :
    IsSelfAdjoint (d9GaugeGhostFinitePacketHilbertOperator covector)
  rangeClosed :
    IsClosed
      (LinearMap.range
        (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap :
        Set (D9GaugeGhostFinitePacketHilbert ι))
  kernelFinite :
    FiniteDimensional Real
      (LinearMap.ker
        (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap)
  cokernelFinite :
    FiniteDimensional Real
      (D9GaugeGhostFinitePacketHilbert ι ⧸
        LinearMap.range
          (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap)
  indexZero :
    (d9GaugeGhostFinitePacketHilbertOperator covector).toLinearMap.index = 0

def d9GaugeGhostFinitePacketHilbertFredholmCertificate
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketHilbertFredholmCertificate covector where
  conjugatesAlgebraic :=
    d9GaugeGhostFinitePacketHilbertOperator_conjugates covector
  selfAdjoint :=
    d9GaugeGhostFinitePacketHilbertOperator_isSelfAdjoint covector
  rangeClosed :=
    d9GaugeGhostFinitePacketHilbertOperator_range_isClosed covector
  kernelFinite := inferInstance
  cokernelFinite := inferInstance
  indexZero :=
    d9GaugeGhostFinitePacketHilbertOperator_index_zero covector

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketHilbertFredholm4D
end JanusFormal
