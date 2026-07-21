import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9PointwiseEuler4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D

/-- Alternating dimension of the pointwise three-term sequence
`V --symbol--> V --quotient--> cokernel`. -/
def d9GaugeGhostBlockPointwiseEuler (covector : TangentVector3) : Int :=
  (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) -
    (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) +
    (Module.finrank Real (D9GaugeGhostBlockCokernel covector) : Int)

theorem d9GaugeGhostBlockPointwiseEuler_eq_cokernel_finrank
    (covector : TangentVector3) :
    d9GaugeGhostBlockPointwiseEuler covector =
      (Module.finrank Real (D9GaugeGhostBlockCokernel covector) : Int) := by
  simp [d9GaugeGhostBlockPointwiseEuler]

theorem d9GaugeGhostBlock_nonzero_pointwiseEuler
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    d9GaugeGhostBlockPointwiseEuler covector = 0 := by
  rw [d9GaugeGhostBlockPointwiseEuler_eq_cokernel_finrank,
    d9GaugeGhostBlock_nonzero_cokernel_finrank covector hCovector]
  rfl

theorem d9GaugeGhostBlock_zero_pointwiseEuler :
    d9GaugeGhostBlockPointwiseEuler zeroTangent =
      (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) := by
  rw [d9GaugeGhostBlockPointwiseEuler_eq_cokernel_finrank,
    d9GaugeGhostBlock_zero_cokernel_finrank]

/-- Alternating dimension of the completed zero-mode pointwise sequence
`V --id--> V --symbol(0)--> V --quotient--> cokernel(0)`. -/
def d9GaugeGhostBlockZeroCompletedEuler : Int :=
  (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) -
    (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) +
    (Module.finrank Real D9GaugeGhostLinearCoordinate : Int) -
    (Module.finrank Real (D9GaugeGhostBlockCokernel zeroTangent) : Int)

theorem d9GaugeGhostBlock_zero_completedEuler :
    d9GaugeGhostBlockZeroCompletedEuler = 0 := by
  rw [d9GaugeGhostBlockZeroCompletedEuler,
    d9GaugeGhostBlock_zero_cokernel_finrank]
  omega

/-- The Euler value of the three-term pointwise sequence is stable between
any two nonzero covectors. -/
theorem d9GaugeGhostBlock_nonzero_pointwiseEuler_stable
    (first second : TangentVector3)
    (hFirst : first ≠ zeroTangent) (hSecond : second ≠ zeroTangent) :
    d9GaugeGhostBlockPointwiseEuler first =
      d9GaugeGhostBlockPointwiseEuler second := by
  rw [d9GaugeGhostBlock_nonzero_pointwiseEuler first hFirst,
    d9GaugeGhostBlock_nonzero_pointwiseEuler second hSecond]

end
end P0EFTJanusGaugeGhostBlockD9PointwiseEuler4D
end JanusFormal
