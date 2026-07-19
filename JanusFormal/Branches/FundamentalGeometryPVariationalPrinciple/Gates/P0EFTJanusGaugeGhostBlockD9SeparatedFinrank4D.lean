import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SeparatedFinrank4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

private theorem scalarSymbol_ker_nonzero
    {V : Type*} [AddCommGroup V] [Module Real V]
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (normSquared covector • (LinearMap.id : V →ₗ[Real] V)) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro value hValue
  have hn : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  simpa [hn] using hValue

private theorem scalarSymbol_range_nonzero
    {V : Type*} [AddCommGroup V] [Module Real V]
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (normSquared covector • (LinearMap.id : V →ₗ[Real] V)) = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro value
  have hn : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  exact ⟨(normSquared covector)⁻¹ • value, by simp [hn]⟩

theorem d9GaugeLinearSymbol_ker_nonzero (covector) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9GaugeLinearSymbol covector) = ⊥ :=
  scalarSymbol_ker_nonzero covector hCovector

theorem d9GaugeLinearSymbol_range_nonzero (covector) (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (d9GaugeLinearSymbol covector) = ⊤ :=
  scalarSymbol_range_nonzero covector hCovector

theorem d9GhostLinearSymbol_ker_nonzero (covector) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9GhostLinearSymbol covector) = ⊥ :=
  scalarSymbol_ker_nonzero covector hCovector

theorem d9GhostLinearSymbol_range_nonzero (covector) (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (d9GhostLinearSymbol covector) = ⊤ :=
  scalarSymbol_range_nonzero covector hCovector

theorem d9GaugeLinearSymbol_ker_zero :
    LinearMap.ker (d9GaugeLinearSymbol zeroTangent) = ⊤ := by
  simp [d9GaugeLinearSymbol, normSquared, tangentDot, zeroTangent]

theorem d9GaugeLinearSymbol_range_zero :
    LinearMap.range (d9GaugeLinearSymbol zeroTangent) = ⊥ := by
  simp [d9GaugeLinearSymbol, normSquared, tangentDot, zeroTangent]

theorem d9GhostLinearSymbol_ker_zero :
    LinearMap.ker (d9GhostLinearSymbol zeroTangent) = ⊤ := by
  simp [d9GhostLinearSymbol, normSquared, tangentDot, zeroTangent]

theorem d9GhostLinearSymbol_range_zero :
    LinearMap.range (d9GhostLinearSymbol zeroTangent) = ⊥ := by
  simp [d9GhostLinearSymbol, normSquared, tangentDot, zeroTangent]

private def submoduleProdEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module Real M] [Module Real N] (p : Submodule Real M) (q : Submodule Real N) :
    p.prod q ≃ₗ[Real] p × q where
  toFun value := (⟨value.1.1, value.2.1⟩, ⟨value.1.2, value.2.2⟩)
  invFun value := ⟨(value.1.1, value.2.1), ⟨value.1.2, value.2.2⟩⟩
  left_inv value := rfl
  right_inv value := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem combinedSymbol_range_finrank_additive (covector : TangentVector3) :
    Module.finrank Real (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)) =
      Module.finrank Real (LinearMap.range (d9GaugeLinearSymbol covector)) +
        Module.finrank Real (LinearMap.range (d9GhostLinearSymbol covector)) := by
  rw [combinedSymbol_range_prod]
  exact (submoduleProdEquiv (LinearMap.range (d9GaugeLinearSymbol covector))
    (LinearMap.range (d9GhostLinearSymbol covector))).finrank_eq.trans
      (Module.finrank_prod (R := Real))

theorem combinedSymbol_ker_finrank_additive (covector : TangentVector3) :
    Module.finrank Real (LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector)) =
      Module.finrank Real (LinearMap.ker (d9GaugeLinearSymbol covector)) +
        Module.finrank Real (LinearMap.ker (d9GhostLinearSymbol covector)) := by
  rw [combinedSymbol_ker_prod]
  exact (submoduleProdEquiv (LinearMap.ker (d9GaugeLinearSymbol covector))
    (LinearMap.ker (d9GhostLinearSymbol covector))).finrank_eq.trans
      (Module.finrank_prod (R := Real))

end
end P0EFTJanusGaugeGhostBlockD9SeparatedFinrank4D
end JanusFormal
