import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9LinearBRSTBlock4D

/-! # U(1)^2 symbol complex for the common linear D9 BRST block -/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9U1SymbolComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9U1GhostPrincipalSymbolBridge4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D
open P0EFTJanusCommonPairedD9GhostPacket4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The actual common variation carried by the ghost slots after one BRST
step.  Gauge potentials are deliberately not reinterpreted as variations. -/
def commonPairedD9AfterBRSTVariation
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    IndependentFieldVariation period hPeriod :=
  ((commonPairedD9LinearBRSTDifferential period hPeriod state).toGhostPacket
    period hPeriod).independentVariation period hPeriod

theorem commonPairedD9AfterBRSTVariation_u1Ghost_zero
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    d9U1Ghost period hPeriod
        (commonPairedD9AfterBRSTVariation period hPeriod state)
        sector column point = 0 := by
  cases sector <;> rfl

/-- Each genuine U(1) D9 ghost symbol kills the BRST image pointwise. -/
theorem ghostPrincipalSymbol_commonPairedD9AfterBRST_zero
    (covector : TangentVector3)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    ghostPrincipalSymbol covector
        (d9U1OnlyGhostField period hPeriod
          (commonPairedD9AfterBRSTVariation period hPeriod state)
          sector column point) = zeroGhostField := by
  apply GaugeFixedGhostField.ext
  · rw [ghostPrincipalSymbol_d9U1Only_u1Ghost,
      commonPairedD9AfterBRSTVariation_u1Ghost_zero]
    simp [zeroGhostField]
  · exact ghostPrincipalSymbol_d9U1Only_diffeomorphismGhost
      period hPeriod covector _ sector column point

/-- Before differentiation, the two projections of the paired D9 symbol are
exactly the two existing single-sector U(1) ghost symbols. -/
theorem commonPairedD9_u1Symbol_projections
    (covector : TangentVector3)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    d9PairedGhostFirstU1
        (d9PairedGhostPrincipalSymbol covector
          (commonPairedD9GhostCoordinate period hPeriod
            (state.toGhostPacket period hPeriod) column point)) =
        (ghostPrincipalSymbol covector
          (d9U1OnlyGhostField period hPeriod
            ((state.toGhostPacket period hPeriod).independentVariation
              period hPeriod) .plus column point)).u1Ghost ∧
      d9PairedGhostSecondU1
        (d9PairedGhostPrincipalSymbol covector
          (commonPairedD9GhostCoordinate period hPeriod
            (state.toGhostPacket period hPeriod) column point)) =
        (ghostPrincipalSymbol covector
          (d9U1OnlyGhostField period hPeriod
            ((state.toGhostPacket period hPeriod).independentVariation
              period hPeriod) .minus column point)).u1Ghost := by
  exact d9PairedProgramGhostPrincipalSymbol_u1_projections period hPeriod
    covector ((state.toGhostPacket period hPeriod).independentVariation
      period hPeriod) column state.diffeomorphismGhost point

end
end P0EFTJanusCommonPairedD9U1SymbolComplex4D
end JanusFormal
