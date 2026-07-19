import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSumEquiv4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

/-- Explicit forward map: take the gauge and ghost projections of a
zero-mode cokernel class. -/
def zeroCokernelToGaugeGhost :
    D9GaugeGhostBlockCokernel zeroTangent →ₗ[Real]
      D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace :=
  (zeroCokernelGaugeProjection).prod zeroCokernelGhostProjection

/-- Explicit inverse map: add the included gauge and ghost components. -/
def gaugeGhostToZeroCokernel :
    D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace →ₗ[Real]
      D9GaugeGhostBlockCokernel zeroTangent :=
  zeroCokernelGaugeInclusion.comp
      (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) +
    zeroCokernelGhostInclusion.comp
      (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)

theorem zeroCokernelToGaugeGhost_apply
    (c : D9GaugeGhostBlockCokernel zeroTangent) :
    zeroCokernelToGaugeGhost c =
      (zeroCokernelGaugeProjection c, zeroCokernelGhostProjection c) := rfl

theorem gaugeGhostToZeroCokernel_apply
    (coordinate : D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace) :
    gaugeGhostToZeroCokernel coordinate =
      zeroCokernelGaugeInclusion coordinate.1 +
        zeroCokernelGhostInclusion coordinate.2 := rfl

theorem zeroCokernelToGaugeGhost_left_inverse
    (c : D9GaugeGhostBlockCokernel zeroTangent) :
    gaugeGhostToZeroCokernel (zeroCokernelToGaugeGhost c) = c :=
  zeroCokernel_gauge_add_ghost c

theorem zeroCokernelToGaugeGhost_right_inverse
    (coordinate : D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace) :
    zeroCokernelToGaugeGhost (gaugeGhostToZeroCokernel coordinate) = coordinate := by
  apply Prod.ext
  · simp [zeroCokernelToGaugeGhost, gaugeGhostToZeroCokernel,
      zeroCokernelGaugeProjection_inclusion, zeroCokernelGaugeProjection_ghostInclusion]
  · simp [zeroCokernelToGaugeGhost, gaugeGhostToZeroCokernel,
      zeroCokernelGhostProjection_inclusion, zeroCokernelGhostProjection_gaugeInclusion]

/-- The requested explicit direct-sum equivalence. -/
def zeroCokernelGaugeGhostDirectSumEquiv :
    D9GaugeGhostBlockCokernel zeroTangent ≃ₗ[Real]
      D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace where
  toLinearMap := zeroCokernelToGaugeGhost
  invFun := gaugeGhostToZeroCokernel
  left_inv := zeroCokernelToGaugeGhost_left_inverse
  right_inv := zeroCokernelToGaugeGhost_right_inverse

@[simp] theorem zeroCokernelGaugeGhostDirectSumEquiv_apply
    (c : D9GaugeGhostBlockCokernel zeroTangent) :
    zeroCokernelGaugeGhostDirectSumEquiv c =
      (zeroCokernelGaugeProjection c, zeroCokernelGhostProjection c) := rfl

@[simp] theorem zeroCokernelGaugeGhostDirectSumEquiv_symm_apply
    (coordinate : D9GaugeLinearCoordinate × D9PairedGhostCoordinateSpace) :
    (zeroCokernelGaugeGhostDirectSumEquiv).symm coordinate =
      zeroCokernelGaugeInclusion coordinate.1 +
        zeroCokernelGhostInclusion coordinate.2 := rfl

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSumEquiv4D
end JanusFormal
