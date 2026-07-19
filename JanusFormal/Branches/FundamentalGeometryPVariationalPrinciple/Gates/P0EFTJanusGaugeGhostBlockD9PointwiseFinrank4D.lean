import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseDichotomy4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D

theorem d9GaugeGhostBlock_nonzero_ker_finrank
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Module.finrank Real (LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector)) = 0 := by
  rw [d9GaugeGhostBlockLinearSymbol_ker_nonzero covector hCovector]
  simp

theorem d9GaugeGhostBlock_nonzero_range_finrank
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Module.finrank Real (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)) =
      Module.finrank Real D9GaugeGhostLinearCoordinate := by
  rw [d9GaugeGhostBlockLinearSymbol_range_nonzero covector hCovector]
  simp

theorem d9GaugeGhostBlock_nonzero_cokernel_finrank
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Module.finrank Real (D9GaugeGhostBlockCokernel covector) = 0 := by
  letI : Subsingleton (D9GaugeGhostBlockCokernel covector) :=
    ⟨fun first second =>
      (d9GaugeGhostBlockCokernel_eq_zero covector hCovector first).trans
        (d9GaugeGhostBlockCokernel_eq_zero covector hCovector second).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem d9GaugeGhostBlock_zero_ker_finrank :
    Module.finrank Real (LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent)) =
      Module.finrank Real D9GaugeGhostLinearCoordinate := by
  rw [d9GaugeGhostBlockLinearSymbol_ker_zero]
  simp

theorem d9GaugeGhostBlock_zero_range_finrank :
    Module.finrank Real (LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent)) = 0 := by
  rw [d9GaugeGhostBlockLinearSymbol_range_zero]
  simp

theorem d9GaugeGhostBlock_zero_cokernel_finrank :
    Module.finrank Real (D9GaugeGhostBlockCokernel zeroTangent) =
      Module.finrank Real D9GaugeGhostLinearCoordinate :=
  (d9GaugeGhostZeroCokernelEquiv).finrank_eq.symm

/-- Rank-nullity for the pointwise symbol, proved by its zero/nonzero
dichotomy rather than by introducing any global operator. -/
theorem d9GaugeGhostBlock_pointwise_rank_nullity (covector : TangentVector3) :
    Module.finrank Real (LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector)) +
      Module.finrank Real (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)) =
    Module.finrank Real D9GaugeGhostLinearCoordinate := by
  by_cases hCovector : covector = zeroTangent
  · subst covector
    rw [d9GaugeGhostBlock_zero_ker_finrank, d9GaugeGhostBlock_zero_range_finrank]
    simp
  · rw [d9GaugeGhostBlock_nonzero_ker_finrank covector hCovector,
      d9GaugeGhostBlock_nonzero_range_finrank covector hCovector]
    simp

end
end P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
end JanusFormal
