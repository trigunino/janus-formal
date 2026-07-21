import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeSplitExactSequences4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

def d9GaugeLinearSymbol (covector : TangentVector3) :
    D9GaugeLinearCoordinate →ₗ[Real] D9GaugeLinearCoordinate :=
  normSquared covector • LinearMap.id

def d9GhostLinearSymbol (covector : TangentVector3) :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9PairedGhostCoordinateSpace :=
  normSquared covector • LinearMap.id

theorem combinedSymbol_gaugeProjection (covector) :
    (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
        (d9GaugeGhostBlockLinearSymbol covector) =
      (d9GaugeLinearSymbol covector).comp
        (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) := by
  apply LinearMap.ext
  intro coordinate
  simp [d9GaugeGhostBlockLinearSymbol, d9GaugeLinearSymbol]

theorem combinedSymbol_ghostProjection (covector) :
    (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
        (d9GaugeGhostBlockLinearSymbol covector) =
      (d9GhostLinearSymbol covector).comp
        (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) := by
  apply LinearMap.ext
  intro coordinate
  simp [d9GaugeGhostBlockLinearSymbol, d9GhostLinearSymbol]

theorem combinedSymbol_gaugeInclusion (covector) :
    (d9GaugeGhostBlockLinearSymbol covector).comp
        (LinearMap.inl Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) =
      (LinearMap.inl Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
        (d9GaugeLinearSymbol covector) := by
  apply LinearMap.ext
  intro gauge
  simp [d9GaugeGhostBlockLinearSymbol, d9GaugeLinearSymbol]

theorem combinedSymbol_ghostInclusion (covector) :
    (d9GaugeGhostBlockLinearSymbol covector).comp
        (LinearMap.inr Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) =
      (LinearMap.inr Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace).comp
        (d9GhostLinearSymbol covector) := by
  apply LinearMap.ext
  intro ghost
  simp [d9GaugeGhostBlockLinearSymbol, d9GhostLinearSymbol]

theorem combinedSymbol_ker_prod (covector : TangentVector3) :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector) =
      (LinearMap.ker (d9GaugeLinearSymbol covector)).prod
        (LinearMap.ker (d9GhostLinearSymbol covector)) := by
  ext coordinate
  by_cases hn : normSquared covector = 0
  · simp [d9GaugeGhostBlockLinearSymbol, d9GaugeLinearSymbol, d9GhostLinearSymbol, hn]
  · simp [d9GaugeGhostBlockLinearSymbol, d9GaugeLinearSymbol, d9GhostLinearSymbol, hn,
      Prod.ext_iff]

theorem combinedSymbol_range_prod (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
      (LinearMap.range (d9GaugeLinearSymbol covector)).prod
        (LinearMap.range (d9GhostLinearSymbol covector)) := by
  ext coordinate
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨⟨source.1, rfl⟩, ⟨source.2, rfl⟩⟩
  · rintro ⟨⟨gauge, hGauge⟩, ⟨ghost, hGhost⟩⟩
    refine ⟨(gauge, ghost), ?_⟩
    apply Prod.ext
    · exact hGauge
    · exact hGhost

/-- Combined pointwise block certificate: both coordinate projections and
inclusions intertwine the symbols, while kernel and image split as products. -/
theorem combinedSymbol_separated_blocks_certificate (covector : TangentVector3) :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector) =
        (LinearMap.ker (d9GaugeLinearSymbol covector)).prod
          (LinearMap.ker (d9GhostLinearSymbol covector)) ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
        (LinearMap.range (d9GaugeLinearSymbol covector)).prod
          (LinearMap.range (d9GhostLinearSymbol covector)) :=
  ⟨combinedSymbol_ker_prod covector, combinedSymbol_range_prod covector⟩

end
end P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D
end JanusFormal
