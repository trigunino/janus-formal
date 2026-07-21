import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D

namespace JanusFormal
namespace P0EFTJanusPureGaugeFullDirectionD9SymbolBridge4D
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
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

variable (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber)

/-- Exact D9 spatial gauge reading of the full pure-gauge direction. -/
theorem pureGaugeFullDirection_d9GaugeOneForm
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    d9GaugeOneForm period hPeriod
        (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
        sector column point =
      { x := (match sector with | .plus => gauge.1 | .minus => gauge.2)
          (fixedThroatQuotientInclusion period hPeriod point) (1, column)
        y := (match sector with | .plus => gauge.1 | .minus => gauge.2)
          (fixedThroatQuotientInclusion period hPeriod point) (2, column)
        z := (match sector with | .plus => gauge.1 | .minus => gauge.2)
          (fixedThroatQuotientInclusion period hPeriod point) (3, column) } := by
  rw [pureGaugeFullDirection_realizes_common_gaugeOnly]
  exact d9GaugeOneForm_gaugeOnlyIndependentVariation period hPeriod gauge sector column point

/-- The existing gauge-fixed Maxwell symbol on the exact D9 gauge reading. -/
theorem pureGaugeFullDirection_d9GaugeSymbol
    (covector : TangentVector3) (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    maxwellGaugeFixedSymbol covector
        (d9GaugeOneForm period hPeriod
          (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
          sector column point) =
      scaleTangent (normSquared covector)
        (d9GaugeOneForm period hPeriod
          (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
          sector column point) :=
  maxwell_gauge_fixed_symbol_is_laplacian _ _

/-- At nonzero covector the symbol kills this D9 reading iff the reading
itself vanishes. -/
theorem pureGaugeFullDirection_d9GaugeSymbol_eq_zero_iff
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    maxwellGaugeFixedSymbol covector
        (d9GaugeOneForm period hPeriod
          (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
          sector column point) = zeroTangent ↔
      d9GaugeOneForm period hPeriod
        (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
        sector column point = zeroTangent := by
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  constructor
  · intro hs
    apply TangentVector3.ext
    · simpa [scaleTangent, zeroTangent, hn] using congrArg (fun v => v.x) hs
    · simpa [scaleTangent, zeroTangent, hn] using congrArg (fun v => v.y) hs
    · simpa [scaleTangent, zeroTangent, hn] using congrArg (fun v => v.z) hs
  · intro h
    rw [h]
    ext <;> simp [scaleTangent, zeroTangent]

/-- Explicit pointwise inverse for the nonzero gauge-fixed symbol. -/
def d9GaugeSymbolInverse (covector field : TangentVector3) : TangentVector3 :=
  scaleTangent (normSquared covector)⁻¹ field

theorem pureGaugeFullDirection_d9GaugeSymbolInverse_recovers
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    d9GaugeSymbolInverse covector
        (maxwellGaugeFixedSymbol covector
          (d9GaugeOneForm period hPeriod
            (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
            sector column point)) =
      d9GaugeOneForm period hPeriod
        (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
        sector column point := by
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [d9GaugeSymbolInverse, scaleTangent, hn]

/-- The exact D9 reading lies in the pointwise image, with the displayed
inverse as a preimage. -/
theorem pureGaugeFullDirection_d9GaugeReading_in_image
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    ∃ preimage : TangentVector3,
      maxwellGaugeFixedSymbol covector preimage =
        d9GaugeOneForm period hPeriod
          (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
          sector column point := by
  refine ⟨d9GaugeSymbolInverse covector
    (d9GaugeOneForm period hPeriod
      (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
      sector column point), ?_⟩
  have hn : normSquared covector ≠ 0 := ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [d9GaugeSymbolInverse, scaleTangent, hn]

/-- At the zero covector, the Maxwell symbol of the exact pure-gauge D9
reading vanishes. -/
theorem pureGaugeFullDirection_d9GaugeSymbol_zero
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    maxwellGaugeFixedSymbol zeroTangent
        (d9GaugeOneForm period hPeriod
          (fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge)).1
          sector column point) = zeroTangent := by
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [scaleTangent, normSquared, tangentDot, zeroTangent]

/-- The pointwise zero-covector symbol has total kernel, expressed without
introducing a new global operator domain. -/
theorem d9GaugeSymbol_zero_kernel_total (field : TangentVector3) :
    maxwellGaugeFixedSymbol zeroTangent field = zeroTangent := by
  rw [maxwell_gauge_fixed_symbol_is_laplacian]
  ext <;> simp [scaleTangent, normSquared, tangentDot, zeroTangent]

/-- The pointwise image at zero covector consists exactly of the zero
vector. -/
theorem d9GaugeSymbol_zero_image_iff (output : TangentVector3) :
    (∃ input : TangentVector3,
      maxwellGaugeFixedSymbol zeroTangent input = output) ↔ output = zeroTangent := by
  constructor
  · rintro ⟨input, rfl⟩
    exact d9GaugeSymbol_zero_kernel_total input
  · rintro rfl
    exact ⟨zeroTangent, d9GaugeSymbol_zero_kernel_total zeroTangent⟩

end
end P0EFTJanusPureGaugeFullDirectionD9SymbolBridge4D
end JanusFormal
