import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryImages4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryQuotients4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryImages4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

theorem zeroCokernelGhostProjection_ker :
    LinearMap.ker zeroCokernelGhostProjection = zeroCokernelGaugeImage := by
  apply le_antisymm
  · intro c hc
    rw [← zeroCokernel_gauge_add_ghost c, hc, map_zero, add_zero]
    exact ⟨zeroCokernelGaugeProjection c, rfl⟩
  · rintro c ⟨gauge, rfl⟩
    exact zeroCokernelGhostProjection_gaugeInclusion gauge

theorem zeroCokernelGaugeProjection_ker :
    LinearMap.ker zeroCokernelGaugeProjection = zeroCokernelGhostImage := by
  apply le_antisymm
  · intro c hc
    rw [← zeroCokernel_gauge_add_ghost c, hc, map_zero, zero_add]
    exact ⟨zeroCokernelGhostProjection c, rfl⟩
  · rintro c ⟨ghost, rfl⟩
    exact zeroCokernelGaugeProjection_ghostInclusion ghost

theorem zeroCokernelGhostProjection_surjective :
    Function.Surjective zeroCokernelGhostProjection := by
  intro ghost
  exact ⟨zeroCokernelGhostInclusion ghost,
    zeroCokernelGhostProjection_inclusion ghost⟩

theorem zeroCokernelGaugeProjection_surjective :
    Function.Surjective zeroCokernelGaugeProjection := by
  intro gauge
  exact ⟨zeroCokernelGaugeInclusion gauge,
    zeroCokernelGaugeProjection_inclusion gauge⟩

/-- Quotienting the zero-mode cokernel by its gauge image leaves exactly the
paired ghost coordinate space. -/
def zeroCokernelQuotientGaugeEquivGhost :
    (D9GaugeGhostBlockCokernel zeroTangent ⧸ zeroCokernelGaugeImage) ≃ₗ[Real]
      D9PairedGhostCoordinateSpace :=
  (Submodule.quotEquivOfEq zeroCokernelGaugeImage
    (LinearMap.ker zeroCokernelGhostProjection)
    zeroCokernelGhostProjection_ker.symm).trans
    (zeroCokernelGhostProjection.quotKerEquivOfSurjective
      zeroCokernelGhostProjection_surjective)

/-- Quotienting by the ghost image leaves exactly the gauge coordinate
space. -/
def zeroCokernelQuotientGhostEquivGauge :
    (D9GaugeGhostBlockCokernel zeroTangent ⧸ zeroCokernelGhostImage) ≃ₗ[Real]
      D9GaugeLinearCoordinate :=
  (Submodule.quotEquivOfEq zeroCokernelGhostImage
    (LinearMap.ker zeroCokernelGaugeProjection)
    zeroCokernelGaugeProjection_ker.symm).trans
    (zeroCokernelGaugeProjection.quotKerEquivOfSurjective
      zeroCokernelGaugeProjection_surjective)

theorem zeroCokernelQuotientGaugeEquivGhost_mk
    (c : D9GaugeGhostBlockCokernel zeroTangent) :
    zeroCokernelQuotientGaugeEquivGhost (Submodule.Quotient.mk c) =
      zeroCokernelGhostProjection c := by
  simp [zeroCokernelQuotientGaugeEquivGhost, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem zeroCokernelQuotientGhostEquivGauge_mk
    (c : D9GaugeGhostBlockCokernel zeroTangent) :
    zeroCokernelQuotientGhostEquivGauge (Submodule.Quotient.mk c) =
      zeroCokernelGaugeProjection c := by
  simp [zeroCokernelQuotientGhostEquivGauge, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeComplementaryQuotients4D
end JanusFormal
