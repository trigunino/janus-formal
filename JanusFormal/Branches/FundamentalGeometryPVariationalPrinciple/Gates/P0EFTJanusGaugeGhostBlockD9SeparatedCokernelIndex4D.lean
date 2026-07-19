import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SeparatedFinrank4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
open P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D
open P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D
open P0EFTJanusGaugeGhostBlockD9SeparatedFinrank4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

abbrev D9GaugeCokernel (covector : TangentVector3) :=
  D9GaugeLinearCoordinate ⧸ LinearMap.range (d9GaugeLinearSymbol covector)

abbrev D9GhostCokernel (covector : TangentVector3) :=
  D9PairedGhostCoordinateSpace ⧸ LinearMap.range (d9GhostLinearSymbol covector)

private theorem cokernel_finrank_nonzero
    {V : Type*} [AddCommGroup V] [Module Real V]
    (symbol : V →ₗ[Real] V) (hRange : LinearMap.range symbol = ⊤) :
    Module.finrank Real (V ⧸ LinearMap.range symbol) = 0 := by
  rw [hRange]
  exact Module.finrank_zero_of_subsingleton

private theorem cokernel_finrank_zero
    {V : Type*} [AddCommGroup V] [Module Real V] [Module.Finite Real V]
    (symbol : V →ₗ[Real] V) (hRange : LinearMap.range symbol = ⊥) :
    Module.finrank Real (V ⧸ LinearMap.range symbol) = Module.finrank Real V := by
  rw [hRange]
  have h := (⊥ : Submodule Real V).finrank_quotient_add_finrank
  simpa using h

theorem d9GaugeCokernel_finrank_nonzero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    Module.finrank Real (D9GaugeCokernel covector) = 0 :=
  cokernel_finrank_nonzero _ (d9GaugeLinearSymbol_range_nonzero covector hCovector)

theorem d9GhostCokernel_finrank_nonzero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    Module.finrank Real (D9GhostCokernel covector) = 0 :=
  cokernel_finrank_nonzero _ (d9GhostLinearSymbol_range_nonzero covector hCovector)

theorem d9GaugeCokernel_finrank_zero :
    Module.finrank Real (D9GaugeCokernel zeroTangent) =
      Module.finrank Real D9GaugeLinearCoordinate :=
  cokernel_finrank_zero _ d9GaugeLinearSymbol_range_zero

theorem d9GhostCokernel_finrank_zero :
    Module.finrank Real (D9GhostCokernel zeroTangent) =
      Module.finrank Real D9PairedGhostCoordinateSpace :=
  cokernel_finrank_zero _ d9GhostLinearSymbol_range_zero

def d9GaugePointwiseIndex (covector : TangentVector3) : Int :=
  (Module.finrank Real (LinearMap.ker (d9GaugeLinearSymbol covector)) : Int) -
    (Module.finrank Real (D9GaugeCokernel covector) : Int)

def d9GhostPointwiseIndex (covector : TangentVector3) : Int :=
  (Module.finrank Real (LinearMap.ker (d9GhostLinearSymbol covector)) : Int) -
    (Module.finrank Real (D9GhostCokernel covector) : Int)

theorem d9GaugePointwiseIndex_zero (covector : TangentVector3) :
    d9GaugePointwiseIndex covector = 0 := by
  by_cases h : covector = zeroTangent
  · subst covector
    rw [d9GaugePointwiseIndex, d9GaugeCokernel_finrank_zero,
      d9GaugeLinearSymbol_ker_zero]
    simp
  · rw [d9GaugePointwiseIndex, d9GaugeCokernel_finrank_nonzero covector h,
      d9GaugeLinearSymbol_ker_nonzero covector h]
    simp

theorem d9GhostPointwiseIndex_zero (covector : TangentVector3) :
    d9GhostPointwiseIndex covector = 0 := by
  by_cases h : covector = zeroTangent
  · subst covector
    rw [d9GhostPointwiseIndex, d9GhostCokernel_finrank_zero,
      d9GhostLinearSymbol_ker_zero]
    simp
  · rw [d9GhostPointwiseIndex, d9GhostCokernel_finrank_nonzero covector h,
      d9GhostLinearSymbol_ker_nonzero covector h]
    simp

theorem combinedCokernel_finrank_additive (covector : TangentVector3) :
    Module.finrank Real (D9GaugeGhostBlockCokernel covector) =
      Module.finrank Real (D9GaugeCokernel covector) +
        Module.finrank Real (D9GhostCokernel covector) := by
  by_cases h : covector = zeroTangent
  · subst covector
    rw [d9GaugeGhostBlock_zero_cokernel_finrank, d9GaugeCokernel_finrank_zero,
      d9GhostCokernel_finrank_zero]
    exact Module.finrank_prod
  · rw [d9GaugeGhostBlock_nonzero_cokernel_finrank covector h,
      d9GaugeCokernel_finrank_nonzero covector h,
      d9GhostCokernel_finrank_nonzero covector h]

theorem combinedPointwiseIndex_additive (covector : TangentVector3) :
    d9GaugeGhostBlockPointwiseIndex covector =
      d9GaugePointwiseIndex covector + d9GhostPointwiseIndex covector := by
  rw [d9GaugeGhostBlockPointwiseIndex, d9GaugePointwiseIndex, d9GhostPointwiseIndex,
    combinedSymbol_ker_finrank_additive, combinedCokernel_finrank_additive]
  omega

end
end P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
end JanusFormal
