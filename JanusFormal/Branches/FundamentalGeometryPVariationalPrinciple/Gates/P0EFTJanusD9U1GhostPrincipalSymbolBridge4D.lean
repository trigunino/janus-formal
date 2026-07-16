import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-!
# D9 U(1)-only ghost principal-symbol bridge

This gate inserts the genuine Program-P `d9U1Ghost` into the D9 ghost field.
Its diffeomorphism component is explicitly zero; it does not claim to supply
the complete D9 diffeomorphism ghost.
-/

namespace JanusFormal
namespace P0EFTJanusD9U1GhostPrincipalSymbolBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- The actual D9 U(1) ghost, embedded with no diffeomorphism-ghost claim. -/
def d9U1OnlyGhostField
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) : GaugeFixedGhostField :=
  { u1Ghost := d9U1Ghost period hPeriod variation sector column point
    diffeomorphismGhost := zeroTangent }

@[simp] theorem d9U1OnlyGhostField_u1Ghost
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (d9U1OnlyGhostField period hPeriod variation sector column point).u1Ghost =
      d9U1Ghost period hPeriod variation sector column point := rfl

@[simp] theorem d9U1OnlyGhostField_diffeomorphismGhost
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (d9U1OnlyGhostField period hPeriod variation sector column point).diffeomorphismGhost =
      zeroTangent := rfl

@[simp] theorem ghostPrincipalSymbol_d9U1Only_u1Ghost
    (covector : TangentVector3)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (ghostPrincipalSymbol covector
      (d9U1OnlyGhostField period hPeriod variation sector column point)).u1Ghost =
      normSquared covector *
        d9U1Ghost period hPeriod variation sector column point := rfl

@[simp] theorem ghostPrincipalSymbol_d9U1Only_diffeomorphismGhost
    (covector : TangentVector3)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (ghostPrincipalSymbol covector
      (d9U1OnlyGhostField period hPeriod variation sector column point)).diffeomorphismGhost =
      zeroTangent := by
  simp [ghostPrincipalSymbol, d9U1OnlyGhostField, ghostLaplacianSymbol]

theorem d9U1Ghost_eq_zero_of_principalSymbol_eq_zero
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (hSymbol : ghostPrincipalSymbol covector
      (d9U1OnlyGhostField period hPeriod variation sector column point) =
        zeroGhostField) :
    d9U1Ghost period hPeriod variation sector column point = 0 := by
  have hProduct : normSquared covector *
      d9U1Ghost period hPeriod variation sector column point = 0 :=
    congrArg GaugeFixedGhostField.u1Ghost hSymbol
  exact (mul_eq_zero.mp hProduct).resolve_left
    (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector))

end
end P0EFTJanusD9U1GhostPrincipalSymbolBridge4D
end JanusFormal
