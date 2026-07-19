import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPureGaugeFullDirectionD9SymbolBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostFullDirectionPairedD9SymbolBridge4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SymbolBridge4D
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
open P0EFTJanusPureGaugeFullDirectionD9SymbolBridge4D
open P0EFTJanusGhostFullDirectionPairedD9SymbolBridge4D
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

abbrev D9GaugeGhostCoordinate := TangentVector3 × D9PairedGhostCoordinateSpace

def zeroD9GaugeGhostCoordinate : D9GaugeGhostCoordinate :=
  (zeroTangent, 0)

/-- Pointwise block-diagonal product of the existing Maxwell gauge-fixed and
paired ghost symbols. -/
def d9GaugeGhostBlockSymbol (covector : TangentVector3)
    (coordinate : D9GaugeGhostCoordinate) : D9GaugeGhostCoordinate :=
  (maxwellGaugeFixedSymbol covector coordinate.1,
    d9PairedGhostPrincipalSymbol covector coordinate.2)

def d9GaugeGhostBlockInverse (covector : TangentVector3)
    (coordinate : D9GaugeGhostCoordinate) : D9GaugeGhostCoordinate :=
  (d9GaugeSymbolInverse covector coordinate.1,
    d9PairedGhostPrincipalSymbolInverse covector coordinate.2)

theorem d9GaugeGhostBlockSymbol_formula (covector : TangentVector3)
    (coordinate : D9GaugeGhostCoordinate) :
    d9GaugeGhostBlockSymbol covector coordinate =
      (scaleTangent (normSquared covector) coordinate.1,
        normSquared covector • coordinate.2) := by
  rw [d9GaugeGhostBlockSymbol, maxwell_gauge_fixed_symbol_is_laplacian,
    d9PairedGhostPrincipalSymbol_apply]

private theorem gaugeInverse_right (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (field : TangentVector3) :
    maxwellGaugeFixedSymbol covector (d9GaugeSymbolInverse covector field) = field := by
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [d9GaugeSymbolInverse, scaleTangent, hn]

private theorem gaugeInverse_left (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (field : TangentVector3) :
    d9GaugeSymbolInverse covector (maxwellGaugeFixedSymbol covector field) = field := by
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [d9GaugeSymbolInverse, scaleTangent, hn]

theorem d9GaugeGhostBlockInverse_left (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (coordinate : D9GaugeGhostCoordinate) :
    d9GaugeGhostBlockInverse covector (d9GaugeGhostBlockSymbol covector coordinate) = coordinate := by
  apply Prod.ext
  · exact gaugeInverse_left covector hCovector coordinate.1
  · exact d9PairedGhostPrincipalSymbolInverse_left covector hCovector coordinate.2

theorem d9GaugeGhostBlockInverse_right (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (coordinate : D9GaugeGhostCoordinate) :
    d9GaugeGhostBlockSymbol covector (d9GaugeGhostBlockInverse covector coordinate) = coordinate := by
  apply Prod.ext
  · exact gaugeInverse_right covector hCovector coordinate.1
  · exact d9PairedGhostPrincipalSymbolInverse_right covector hCovector coordinate.2

theorem d9GaugeGhostBlockSymbol_eq_zero_iff (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) (coordinate : D9GaugeGhostCoordinate) :
    d9GaugeGhostBlockSymbol covector coordinate = zeroD9GaugeGhostCoordinate ↔
      coordinate = zeroD9GaugeGhostCoordinate := by
  constructor
  · intro hs
    have hi := congrArg (d9GaugeGhostBlockInverse covector) hs
    rw [d9GaugeGhostBlockInverse_left covector hCovector coordinate] at hi
    simpa [zeroD9GaugeGhostCoordinate, d9GaugeGhostBlockInverse, d9GaugeSymbolInverse,
      scaleTangent, zeroTangent] using hi
  · intro h
    rw [h]
    apply Prod.ext
    · change maxwellGaugeFixedSymbol covector zeroTangent = zeroTangent
      rw [maxwell_gauge_fixed_symbol_is_laplacian]
      ext <;> simp [scaleTangent, zeroTangent]
    · change d9PairedGhostPrincipalSymbol covector 0 = 0
      exact map_zero _

theorem d9GaugeGhostBlockSymbol_surjective (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    Function.Surjective (d9GaugeGhostBlockSymbol covector) := by
  intro coordinate
  exact ⟨d9GaugeGhostBlockInverse covector coordinate,
    d9GaugeGhostBlockInverse_right covector hCovector coordinate⟩

theorem d9GaugeGhostBlockSymbol_zero (coordinate : D9GaugeGhostCoordinate) :
    d9GaugeGhostBlockSymbol zeroTangent coordinate = zeroD9GaugeGhostCoordinate := by
  rw [d9GaugeGhostBlockSymbol_formula]
  apply Prod.ext
  · ext <;> simp [zeroD9GaugeGhostCoordinate, scaleTangent, normSquared, tangentDot, zeroTangent]
  · simp [zeroD9GaugeGhostCoordinate, normSquared, tangentDot, zeroTangent]

theorem d9GaugeGhostBlockSymbol_zero_image_iff (output : D9GaugeGhostCoordinate) :
    (∃ input, d9GaugeGhostBlockSymbol zeroTangent input = output) ↔
      output = zeroD9GaugeGhostCoordinate := by
  constructor
  · rintro ⟨input, rfl⟩
    exact d9GaugeGhostBlockSymbol_zero input
  · rintro rfl
    exact ⟨zeroD9GaugeGhostCoordinate,
      d9GaugeGhostBlockSymbol_zero zeroD9GaugeGhostCoordinate⟩

variable (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber)
  (ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber)

def fullGaugeGhostD9Reading (sector : Sector) (column : Fin 2)
    (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) : D9GaugeGhostCoordinate :=
  (d9GaugeOneForm period hPeriod
      (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
      sector column point,
    d9PairedProgramGhostCoordinateFull period hPeriod
      (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
      column geometricGhost point)

theorem fullGaugeGhostD9Reading_symbol_formula (covector : TangentVector3)
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9GaugeGhostBlockSymbol covector
        (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) =
      (scaleTangent (normSquared covector)
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point).1,
        normSquared covector •
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point).2) :=
  d9GaugeGhostBlockSymbol_formula covector _

end
end P0EFTJanusGaugeGhostBlockD9SymbolBridge4D
end JanusFormal
