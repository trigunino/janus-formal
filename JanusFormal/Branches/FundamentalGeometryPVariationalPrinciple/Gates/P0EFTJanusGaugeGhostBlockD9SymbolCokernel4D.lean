import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SymbolBridge4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
open P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
open P0EFTJanusGaugeGhostBlockD9SymbolBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Linear coordinate version of the pointwise gauge+ghost block. -/
abbrev D9GaugeGhostLinearCoordinate :=
  (Real × Real × Real) × D9PairedGhostCoordinateSpace

def packGaugeGhostCoordinate (coordinate : D9GaugeGhostCoordinate) :
    D9GaugeGhostLinearCoordinate :=
  ((coordinate.1.x, coordinate.1.y, coordinate.1.z), coordinate.2)

def d9GaugeGhostBlockLinearSymbol (covector : TangentVector3) :
    D9GaugeGhostLinearCoordinate →ₗ[Real] D9GaugeGhostLinearCoordinate :=
  normSquared covector • LinearMap.id

@[simp] theorem d9GaugeGhostBlockLinearSymbol_apply (covector) (coordinate) :
    d9GaugeGhostBlockLinearSymbol covector coordinate = normSquared covector • coordinate := rfl

theorem packGaugeGhostCoordinate_symbol (covector) (coordinate) :
    packGaugeGhostCoordinate (d9GaugeGhostBlockSymbol covector coordinate) =
      d9GaugeGhostBlockLinearSymbol covector (packGaugeGhostCoordinate coordinate) := by
  rw [d9GaugeGhostBlockSymbol_formula]
  rfl

theorem d9GaugeGhostBlockLinearSymbol_range_nonzero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro coordinate
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  refine ⟨(normSquared covector)⁻¹ • coordinate, ?_⟩
  simp [d9GaugeGhostBlockLinearSymbol, hn]

theorem d9GaugeGhostBlockLinearSymbol_range_zero :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent) = ⊥ := by
  have hz : d9GaugeGhostBlockLinearSymbol zeroTangent = 0 := by
    apply LinearMap.ext
    intro coordinate
    simp [d9GaugeGhostBlockLinearSymbol, normSquared, tangentDot, zeroTangent]
  rw [hz, LinearMap.range_zero]

theorem d9GaugeGhostBlockLinearSymbol_ker_nonzero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro coordinate hCoordinate
  have hn : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  simpa [d9GaugeGhostBlockLinearSymbol, hn] using hCoordinate

theorem d9GaugeGhostBlockLinearSymbol_ker_zero :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) = ⊤ := by
  have hz : d9GaugeGhostBlockLinearSymbol zeroTangent = 0 := by
    apply LinearMap.ext
    intro coordinate
    simp [d9GaugeGhostBlockLinearSymbol, normSquared, tangentDot, zeroTangent]
  rw [hz, LinearMap.ker_zero]

abbrev D9GaugeGhostBlockCokernel (covector : TangentVector3) :=
  (D9GaugeGhostLinearCoordinate ⧸
    (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)))

def d9GaugeGhostBlockCokernelProjection (covector : TangentVector3) :
    D9GaugeGhostLinearCoordinate →ₗ[Real] D9GaugeGhostBlockCokernel covector :=
  (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)).mkQ

theorem d9GaugeGhostBlockCokernelClass_zero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (coordinate : D9GaugeGhostLinearCoordinate) :
    d9GaugeGhostBlockCokernelProjection covector coordinate = 0 := by
  change (Submodule.Quotient.mk coordinate : D9GaugeGhostBlockCokernel covector) = 0
  rw [Submodule.Quotient.mk_eq_zero, d9GaugeGhostBlockLinearSymbol_range_nonzero covector hCovector]
  trivial

theorem d9GaugeGhostBlockCokernel_eq_zero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (c : D9GaugeGhostBlockCokernel covector) : c = 0 := by
  obtain ⟨coordinate, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)) c
  exact d9GaugeGhostBlockCokernelClass_zero covector hCovector coordinate

/-- Complete pointwise nonzero-covector certificate for this single block
symbol: trivial kernel, total image, and trivial cokernel. -/
theorem d9GaugeGhostBlock_nonzero_pointwise_exactness
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector) = ⊥ ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) = ⊤ ∧
      ∀ c : D9GaugeGhostBlockCokernel covector, c = 0 :=
  ⟨d9GaugeGhostBlockLinearSymbol_ker_nonzero covector hCovector,
    d9GaugeGhostBlockLinearSymbol_range_nonzero covector hCovector,
    d9GaugeGhostBlockCokernel_eq_zero covector hCovector⟩

def d9GaugeGhostZeroCokernelEquiv :
    D9GaugeGhostLinearCoordinate ≃ₗ[Real] D9GaugeGhostBlockCokernel zeroTangent := by
  apply LinearEquiv.ofBijective (d9GaugeGhostBlockCokernelProjection zeroTangent)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [d9GaugeGhostBlockCokernelProjection, Submodule.ker_mkQ,
      d9GaugeGhostBlockLinearSymbol_range_zero]
  · exact Submodule.mkQ_surjective _

/-- Complete isolated zero-symbol certificate: total kernel, zero image, and
the cokernel canonically equivalent to the whole coordinate space. -/
theorem d9GaugeGhostBlock_zero_pointwise_cohomology :
    LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) = ⊤ ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent) = ⊥ ∧
      Function.Bijective (d9GaugeGhostBlockCokernelProjection zeroTangent) := by
  refine ⟨d9GaugeGhostBlockLinearSymbol_ker_zero,
    d9GaugeGhostBlockLinearSymbol_range_zero, ?_⟩
  exact (d9GaugeGhostZeroCokernelEquiv).bijective

variable (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber)
  (ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber)

theorem fullGaugeGhostD9Reading_cokernel_nonzero
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9GaugeGhostBlockCokernelProjection covector
        (packGaugeGhostCoordinate
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) = 0 :=
  d9GaugeGhostBlockCokernelClass_zero covector hCovector _

theorem fullGaugeGhostD9Reading_zeroCokernel_representative
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9GaugeGhostZeroCokernelEquiv).symm
        (d9GaugeGhostBlockCokernelProjection zeroTangent
          (packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point))) =
      packGaugeGhostCoordinate
        (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) :=
  (d9GaugeGhostZeroCokernelEquiv).left_inv _

theorem fullGaugeGhostD9Reading_zero_mem_kernel
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    packGaugeGhostCoordinate
        (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) ∈
      LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) := by
  rw [d9GaugeGhostBlockLinearSymbol_ker_zero]
  trivial

/-- The concrete full reading realizes the two pointwise regimes: it is in
the total image and has zero cokernel class away from zero; at zero it lies
in the total kernel and its class retains the complete packed coordinate. -/
theorem fullGaugeGhostD9Reading_pointwise_regimes
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9GaugeGhostBlockCokernelProjection covector
        (packGaugeGhostCoordinate
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) = 0 ∧
      packGaugeGhostCoordinate
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) ∈
        LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) ∧
      (d9GaugeGhostZeroCokernelEquiv).symm
          (d9GaugeGhostBlockCokernelProjection zeroTangent
            (packGaugeGhostCoordinate
              (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point))) =
        packGaugeGhostCoordinate
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) :=
  ⟨fullGaugeGhostD9Reading_cokernel_nonzero period hPeriod gauge ghost covector hCovector
      sector column geometricGhost point,
    fullGaugeGhostD9Reading_zero_mem_kernel period hPeriod gauge ghost sector column geometricGhost point,
    fullGaugeGhostD9Reading_zeroCokernel_representative period hPeriod gauge ghost sector column
      geometricGhost point⟩

end
end P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
end JanusFormal
