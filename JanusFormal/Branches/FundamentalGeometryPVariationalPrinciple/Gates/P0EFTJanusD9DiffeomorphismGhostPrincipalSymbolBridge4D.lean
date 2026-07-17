import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9U1GhostPrincipalSymbolBridge4D

/-!
# D8 throat diffeomorphism ghost in the D9 principal symbol

This gate converts the genuine smooth tangent ghosts on the effective D8
throat to the three real components used by D9.  It records the intrinsic Lie
bracket under the same conversion and computes the complete D9 ghost symbol
for this diffeomorphism-only sector.  No zero-mode or global BRST cohomology
claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The model coordinates of a throat tangent vector, packaged in D9's
three-component tangent type. -/
def throatTangentToD9 (vector : ThroatCoverCoordinates) : TangentVector3 :=
  { x := vector.1 0
    y := vector.1 1
    z := vector.2 }

@[simp] theorem throatTangentToD9_zero :
    throatTangentToD9 (0 : ThroatCoverCoordinates) = zeroTangent := by
  ext <;> rfl

theorem throatTangentToD9_injective :
    Function.Injective throatTangentToD9 := by
  intro first second hEqual
  rcases first with ⟨firstSpatial, firstTime⟩
  rcases second with ⟨secondSpatial, secondTime⟩
  have hx := congrArg TangentVector3.x hEqual
  have hy := congrArg TangentVector3.y hEqual
  have hz := congrArg TangentVector3.z hEqual
  congr
  ext index
  fin_cases index
  · exact hx
  · exact hy

/-- Pointwise typed insertion of a genuine smooth D8 throat ghost into the D9
ghost field, with no `U(1)` component. -/
def d9DiffeomorphismGhostField
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) : GaugeFixedGhostField :=
  { u1Ghost := 0
    diffeomorphismGhost := throatTangentToD9 (ghost point) }

@[simp] theorem d9DiffeomorphismGhostField_u1Ghost
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9DiffeomorphismGhostField period hPeriod ghost point).u1Ghost = 0 := rfl

@[simp] theorem d9DiffeomorphismGhostField_diffeomorphismGhost
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9DiffeomorphismGhostField period hPeriod ghost point).diffeomorphismGhost =
      throatTangentToD9 (ghost point) := rfl

/-- The insertion is faithful as a map from global smooth throat ghosts to
pointwise D9 fields. -/
theorem d9DiffeomorphismGhostField_injective
    {first second : CInfinityThroatGhost period hPeriod}
    (hEqual : ∀ point,
      d9DiffeomorphismGhostField period hPeriod first point =
        d9DiffeomorphismGhostField period hPeriod second point) :
    first = second := by
  apply ContMDiffSection.ext
  intro point
  apply throatTangentToD9_injective
  exact congrArg GaugeFixedGhostField.diffeomorphismGhost (hEqual point)

/-- Compatibility with the already constructed intrinsic throat Lie bracket:
the D9 value is the three-coordinate image of that bracket. -/
theorem d9DiffeomorphismGhostField_lieBracket
    (first second : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9DiffeomorphismGhostField period hPeriod
      (throatGhostLieBracket period hPeriod first second) point).diffeomorphismGhost =
      throatTangentToD9
        (VectorField.mlieBracket throatCoverModelWithCorners first second point) := by
  rw [d9DiffeomorphismGhostField_diffeomorphismGhost,
    throatGhostLieBracket_apply]

@[simp] theorem ghostPrincipalSymbol_d9Diffeomorphism_u1Ghost
    (covector : TangentVector3)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (ghostPrincipalSymbol covector
      (d9DiffeomorphismGhostField period hPeriod ghost point)).u1Ghost = 0 := by
  simp [ghostPrincipalSymbol, d9DiffeomorphismGhostField]

/-- Exact principal symbol on the genuine diffeomorphism ghost value. -/
theorem ghostPrincipalSymbol_d9Diffeomorphism_diffeomorphismGhost
    (covector : TangentVector3)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (ghostPrincipalSymbol covector
      (d9DiffeomorphismGhostField period hPeriod ghost point)).diffeomorphismGhost =
      scaleTangent (normSquared covector) (throatTangentToD9 (ghost point)) :=
  rfl

/-- At a nonzero covector, the D9 principal symbol vanishes exactly when the
genuine throat ghost vanishes at the inspected point. -/
theorem ghostPrincipalSymbol_d9Diffeomorphism_eq_zero_iff
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ghostPrincipalSymbol covector
        (d9DiffeomorphismGhostField period hPeriod ghost point) = zeroGhostField ↔
      ghost point = 0 := by
  constructor
  · intro hSymbol
    have hField := ghost_principal_symbol_kernel_trivial covector hCovector
      (d9DiffeomorphismGhostField period hPeriod ghost point) hSymbol
    apply throatTangentToD9_injective
    exact (congrArg GaugeFixedGhostField.diffeomorphismGhost hField).trans
      throatTangentToD9_zero.symm
  · intro hGhost
    apply GaugeFixedGhostField.ext
    · simp [ghostPrincipalSymbol, d9DiffeomorphismGhostField, zeroGhostField]
    · change scaleTangent (normSquared covector)
          (throatTangentToD9 (ghost point)) = zeroTangent
      have hPacked : throatTangentToD9 (ghost point) = zeroTangent := by
        change (ghost point : ThroatCoverCoordinates) =
          (0 : ThroatCoverCoordinates) at hGhost
        exact (congrArg throatTangentToD9 hGhost).trans throatTangentToD9_zero
      rw [hPacked]
      exact scale_zero_tangent (normSquared covector)

end
end P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
end JanusFormal
