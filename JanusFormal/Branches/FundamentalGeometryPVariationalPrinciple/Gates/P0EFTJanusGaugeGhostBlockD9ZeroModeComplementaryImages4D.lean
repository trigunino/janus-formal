import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSumEquiv4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryImages4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSumEquiv4D
open P0EFTJanusGaugeFixedPrincipalSymbols

def zeroCokernelGaugeImage :
    Submodule Real (D9GaugeGhostBlockCokernel zeroTangent) :=
  LinearMap.range zeroCokernelGaugeInclusion

def zeroCokernelGhostImage :
    Submodule Real (D9GaugeGhostBlockCokernel zeroTangent) :=
  LinearMap.range zeroCokernelGhostInclusion

theorem zeroCokernelGaugeImage_inf_zeroCokernelGhostImage :
    zeroCokernelGaugeImage ⊓ zeroCokernelGhostImage = ⊥ := by
  apply le_antisymm
  · intro c hc
    obtain ⟨gauge, hGauge⟩ := hc.1
    obtain ⟨ghost, hGhost⟩ := hc.2
    have hSum : zeroCokernelGaugeInclusion gauge +
        zeroCokernelGhostInclusion (-ghost) = 0 := by
      rw [map_neg, hGauge, hGhost]
      simp
    have hComponents :=
      (zeroCokernel_gauge_ghost_sum_eq_zero_iff gauge (-ghost)).mp hSum
    rw [Submodule.mem_bot, ← hGauge, hComponents.1]
    exact map_zero zeroCokernelGaugeInclusion
  · exact bot_le

theorem zeroCokernelGaugeImage_sup_zeroCokernelGhostImage :
    zeroCokernelGaugeImage ⊔ zeroCokernelGhostImage = ⊤ := by
  apply le_antisymm le_top
  intro c _
  rw [← zeroCokernel_gauge_add_ghost c]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left ⟨zeroCokernelGaugeProjection c, rfl⟩)
    (Submodule.mem_sup_right ⟨zeroCokernelGhostProjection c, rfl⟩)

/-- The two image submodules give an internal direct-sum decomposition of
the pointwise zero-mode cokernel. -/
theorem zeroCokernelGaugeGhostImages_complementary :
    zeroCokernelGaugeImage ⊓ zeroCokernelGhostImage = ⊥ ∧
      zeroCokernelGaugeImage ⊔ zeroCokernelGhostImage = ⊤ :=
  ⟨zeroCokernelGaugeImage_inf_zeroCokernelGhostImage,
    zeroCokernelGaugeImage_sup_zeroCokernelGhostImage⟩

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryImages4D
end JanusFormal
