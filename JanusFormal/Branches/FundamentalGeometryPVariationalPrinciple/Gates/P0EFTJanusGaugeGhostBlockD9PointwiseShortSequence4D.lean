import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9PointwiseShortSequence4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D

/-- Exactness at the middle term of the pointwise two-arrow sequence
`coordinate --symbol--> coordinate --quotient--> cokernel`. -/
theorem d9GaugeGhostBlock_pointwise_exact_at_coordinate
    (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
      LinearMap.ker (d9GaugeGhostBlockCokernelProjection covector) := by
  rw [d9GaugeGhostBlockCokernelProjection, Submodule.ker_mkQ]

/-- The quotient arrow is pointwise surjective. -/
theorem d9GaugeGhostBlock_pointwise_quotient_surjective
    (covector : TangentVector3) :
    Function.Surjective (d9GaugeGhostBlockCokernelProjection covector) :=
  Submodule.mkQ_surjective _

/-- Explicit linear splitting of the symbol away from the zero covector. -/
def d9GaugeGhostBlockLinearSymbolInverse (covector : TangentVector3) :
    D9GaugeGhostLinearCoordinate →ₗ[Real] D9GaugeGhostLinearCoordinate :=
  (normSquared covector)⁻¹ • LinearMap.id

theorem d9GaugeGhostBlockLinearSymbolInverse_left
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    (d9GaugeGhostBlockLinearSymbolInverse covector).comp
        (d9GaugeGhostBlockLinearSymbol covector) = LinearMap.id := by
  have hn : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  apply LinearMap.ext
  intro coordinate
  simp [d9GaugeGhostBlockLinearSymbolInverse, d9GaugeGhostBlockLinearSymbol, hn]

theorem d9GaugeGhostBlockLinearSymbolInverse_right
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    (d9GaugeGhostBlockLinearSymbol covector).comp
        (d9GaugeGhostBlockLinearSymbolInverse covector) = LinearMap.id := by
  have hn : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  apply LinearMap.ext
  intro coordinate
  simp [d9GaugeGhostBlockLinearSymbolInverse, d9GaugeGhostBlockLinearSymbol, hn]

/-- At nonzero covector the pointwise short sequence is split at its middle
term and its quotient term is trivial. -/
theorem d9GaugeGhostBlock_nonzero_pointwise_split_certificate
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
        LinearMap.ker (d9GaugeGhostBlockCokernelProjection covector) ∧
      (d9GaugeGhostBlockLinearSymbolInverse covector).comp
          (d9GaugeGhostBlockLinearSymbol covector) = LinearMap.id ∧
      (d9GaugeGhostBlockLinearSymbol covector).comp
          (d9GaugeGhostBlockLinearSymbolInverse covector) = LinearMap.id ∧
      ∀ c : D9GaugeGhostBlockCokernel covector, c = 0 :=
  ⟨d9GaugeGhostBlock_pointwise_exact_at_coordinate covector,
    d9GaugeGhostBlockLinearSymbolInverse_left covector hCovector,
    d9GaugeGhostBlockLinearSymbolInverse_right covector hCovector,
    d9GaugeGhostBlockCokernel_eq_zero covector hCovector⟩

end
end P0EFTJanusGaugeGhostBlockD9PointwiseShortSequence4D
end JanusFormal
