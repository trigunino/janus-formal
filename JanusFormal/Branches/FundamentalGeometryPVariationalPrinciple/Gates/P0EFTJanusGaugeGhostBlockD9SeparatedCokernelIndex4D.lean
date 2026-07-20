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

/-- Total pointwise index of a finite family of combined gauge--ghost blocks.
This models finite field, internal-space or regulator multiplicities without
introducing a global differential operator. -/
def d9GaugeGhostFinitePointwiseIndex {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Int :=
  modes.sum fun mode => d9GaugeGhostBlockPointwiseIndex (covector mode)

/-- The same finite total computed after separating each gauge and ghost
symbol block. -/
def d9SeparatedFinitePointwiseIndex {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Int :=
  modes.sum fun mode =>
    d9GaugePointwiseIndex (covector mode) +
      d9GhostPointwiseIndex (covector mode)

/-- Pointwise gauge--ghost additivity commutes with every finite multiplicity
sum, including mixtures of zero and nonzero covectors. -/
theorem d9GaugeGhostFinitePointwiseIndex_additive {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex modes covector =
      d9SeparatedFinitePointwiseIndex modes covector := by
  unfold d9GaugeGhostFinitePointwiseIndex d9SeparatedFinitePointwiseIndex
  apply Finset.sum_congr rfl
  intro mode _
  exact combinedPointwiseIndex_additive (covector mode)

/-- Every finite collection of combined gauge--ghost pointwise symbols has
zero total index, even when some members lie at the zero covector. -/
theorem d9GaugeGhostFinitePointwiseIndex_zero {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex modes covector = 0 := by
  simp [d9GaugeGhostFinitePointwiseIndex,
    d9GaugeGhostBlock_pointwise_index_zero]

/-- The separated gauge and ghost computation has the same zero total. -/
theorem d9SeparatedFinitePointwiseIndex_zero {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) :
    d9SeparatedFinitePointwiseIndex modes covector = 0 := by
  simp [d9SeparatedFinitePointwiseIndex, d9GaugePointwiseIndex_zero,
    d9GhostPointwiseIndex_zero]

/-- Consequently the finite total is independent of all pointwise covector
regimes and may be transported between finite regulator or field packets. -/
theorem d9GaugeGhostFinitePointwiseIndex_stable {ι : Type*}
    (modes : Finset ι) (first second : ι → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex modes first =
      d9GaugeGhostFinitePointwiseIndex modes second := by
  calc
    d9GaugeGhostFinitePointwiseIndex modes first = 0 :=
      d9GaugeGhostFinitePointwiseIndex_zero modes first
    _ = d9GaugeGhostFinitePointwiseIndex modes second :=
      (d9GaugeGhostFinitePointwiseIndex_zero modes second).symm

/-- Reusable finite-multiplicity closure certificate for the D9 gauge--ghost
pointwise block. -/
theorem d9GaugeGhostFiniteMultiplicityIndex_certificate {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex modes covector =
        d9SeparatedFinitePointwiseIndex modes covector ∧
      d9GaugeGhostFinitePointwiseIndex modes covector = 0 ∧
      d9SeparatedFinitePointwiseIndex modes covector = 0 := by
  refine ⟨d9GaugeGhostFinitePointwiseIndex_additive modes covector, ?_⟩
  exact ⟨d9GaugeGhostFinitePointwiseIndex_zero modes covector,
    d9SeparatedFinitePointwiseIndex_zero modes covector⟩

end
end P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
end JanusFormal
