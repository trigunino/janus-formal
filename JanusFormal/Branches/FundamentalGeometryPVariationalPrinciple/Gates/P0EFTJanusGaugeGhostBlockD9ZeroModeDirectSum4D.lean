import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeDecomposition4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

abbrev D9GaugeLinearCoordinate := Real × Real × Real

def zeroCokernelGaugeInclusion :
    D9GaugeLinearCoordinate →ₗ[Real] D9GaugeGhostBlockCokernel zeroTangent :=
  (d9GaugeGhostZeroCokernelEquiv).toLinearMap.comp
    (LinearMap.inl Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)

def zeroCokernelGhostInclusion :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9GaugeGhostBlockCokernel zeroTangent :=
  (d9GaugeGhostZeroCokernelEquiv).toLinearMap.comp
    (LinearMap.inr Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)

def zeroCokernelGaugeProjection :
    D9GaugeGhostBlockCokernel zeroTangent →ₗ[Real] D9GaugeLinearCoordinate :=
  (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
    (d9GaugeGhostZeroCokernelEquiv).symm.toLinearMap

def zeroCokernelGhostProjection :
    D9GaugeGhostBlockCokernel zeroTangent →ₗ[Real] D9PairedGhostCoordinateSpace :=
  (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
    (d9GaugeGhostZeroCokernelEquiv).symm.toLinearMap

theorem zeroCokernelGaugeProjection_inclusion (gauge : D9GaugeLinearCoordinate) :
    zeroCokernelGaugeProjection (zeroCokernelGaugeInclusion gauge) = gauge := by
  simp [zeroCokernelGaugeProjection, zeroCokernelGaugeInclusion]

theorem zeroCokernelGhostProjection_inclusion (ghost : D9PairedGhostCoordinateSpace) :
    zeroCokernelGhostProjection (zeroCokernelGhostInclusion ghost) = ghost := by
  simp [zeroCokernelGhostProjection, zeroCokernelGhostInclusion]

theorem zeroCokernelGaugeProjection_ghostInclusion (ghost : D9PairedGhostCoordinateSpace) :
    zeroCokernelGaugeProjection (zeroCokernelGhostInclusion ghost) = 0 := by
  simp [zeroCokernelGaugeProjection, zeroCokernelGhostInclusion]

theorem zeroCokernelGhostProjection_gaugeInclusion (gauge : D9GaugeLinearCoordinate) :
    zeroCokernelGhostProjection (zeroCokernelGaugeInclusion gauge) = 0 := by
  simp [zeroCokernelGhostProjection, zeroCokernelGaugeInclusion]

/-- Every zero-mode cokernel class is the sum of its gauge and ghost
components. -/
theorem zeroCokernel_gauge_add_ghost (c : D9GaugeGhostBlockCokernel zeroTangent) :
    zeroCokernelGaugeInclusion (zeroCokernelGaugeProjection c) +
      zeroCokernelGhostInclusion (zeroCokernelGhostProjection c) = c := by
  apply (d9GaugeGhostZeroCokernelEquiv).symm.injective
  simp [zeroCokernelGaugeProjection, zeroCokernelGhostProjection,
    zeroCokernelGaugeInclusion, zeroCokernelGhostInclusion]

/-- The displayed decomposition is direct: a vanishing gauge+ghost sum has
both components zero. -/
theorem zeroCokernel_gauge_ghost_sum_eq_zero_iff
    (gauge : D9GaugeLinearCoordinate) (ghost : D9PairedGhostCoordinateSpace) :
    zeroCokernelGaugeInclusion gauge + zeroCokernelGhostInclusion ghost = 0 ↔
      gauge = 0 ∧ ghost = 0 := by
  constructor
  · intro h
    constructor
    · have := congrArg zeroCokernelGaugeProjection h
      simpa [map_add, zeroCokernelGaugeProjection_inclusion,
        zeroCokernelGaugeProjection_ghostInclusion] using this
    · have := congrArg zeroCokernelGhostProjection h
      simpa [map_add, zeroCokernelGhostProjection_inclusion,
        zeroCokernelGhostProjection_gaugeInclusion] using this
  · rintro ⟨rfl, rfl⟩
    simp

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
end JanusFormal
