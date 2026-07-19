import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryQuotients4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeSplitExactSequences4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryImages4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryQuotients4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

theorem gaugeInclusion_then_ghostProjection_zero :
    zeroCokernelGhostProjection.comp zeroCokernelGaugeInclusion = 0 := by
  apply LinearMap.ext
  intro gauge
  exact zeroCokernelGhostProjection_gaugeInclusion gauge

theorem ghostInclusion_then_gaugeProjection_zero :
    zeroCokernelGaugeProjection.comp zeroCokernelGhostInclusion = 0 := by
  apply LinearMap.ext
  intro ghost
  exact zeroCokernelGaugeProjection_ghostInclusion ghost

theorem gaugeInclusion_range_eq_ghostProjection_ker :
    LinearMap.range zeroCokernelGaugeInclusion =
      LinearMap.ker zeroCokernelGhostProjection := by
  rw [zeroCokernelGhostProjection_ker]
  rfl

theorem ghostInclusion_range_eq_gaugeProjection_ker :
    LinearMap.range zeroCokernelGhostInclusion =
      LinearMap.ker zeroCokernelGaugeProjection := by
  rw [zeroCokernelGaugeProjection_ker]
  rfl

theorem gaugeProjection_retracts_gaugeInclusion :
    zeroCokernelGaugeProjection.comp zeroCokernelGaugeInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro gauge
  exact zeroCokernelGaugeProjection_inclusion gauge

theorem ghostProjection_retracts_ghostInclusion :
    zeroCokernelGhostProjection.comp zeroCokernelGhostInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro ghost
  exact zeroCokernelGhostProjection_inclusion ghost

/-- Split exact pointwise zero-mode sequence
`gauge³ → cokernel → paired ghost`. -/
theorem gauge_to_cokernel_to_ghost_split_exact :
    zeroCokernelGhostProjection.comp zeroCokernelGaugeInclusion = 0 ∧
      LinearMap.range zeroCokernelGaugeInclusion =
        LinearMap.ker zeroCokernelGhostProjection ∧
      zeroCokernelGaugeProjection.comp zeroCokernelGaugeInclusion = LinearMap.id ∧
      zeroCokernelGhostProjection.comp zeroCokernelGhostInclusion = LinearMap.id :=
  ⟨gaugeInclusion_then_ghostProjection_zero,
    gaugeInclusion_range_eq_ghostProjection_ker,
    gaugeProjection_retracts_gaugeInclusion,
    ghostProjection_retracts_ghostInclusion⟩

/-- Split exact pointwise zero-mode sequence
`paired ghost → cokernel → gauge³`. -/
theorem ghost_to_cokernel_to_gauge_split_exact :
    zeroCokernelGaugeProjection.comp zeroCokernelGhostInclusion = 0 ∧
      LinearMap.range zeroCokernelGhostInclusion =
        LinearMap.ker zeroCokernelGaugeProjection ∧
      zeroCokernelGhostProjection.comp zeroCokernelGhostInclusion = LinearMap.id ∧
      zeroCokernelGaugeProjection.comp zeroCokernelGaugeInclusion = LinearMap.id :=
  ⟨ghostInclusion_then_gaugeProjection_zero,
    ghostInclusion_range_eq_gaugeProjection_ker,
    ghostProjection_retracts_ghostInclusion,
    gaugeProjection_retracts_gaugeInclusion⟩

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeSplitExactSequences4D
end JanusFormal
