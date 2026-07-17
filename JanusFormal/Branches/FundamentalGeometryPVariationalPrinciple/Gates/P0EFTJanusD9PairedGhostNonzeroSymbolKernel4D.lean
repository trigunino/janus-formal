import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

/-!
# Nonzero-symbol kernel of the paired D9 ghost coordinates

The paired five-coordinate ghost symbol scales both genuine Program-P `U(1)`
sector coordinates and the three constructed diffeomorphism coordinates by
the same positive norm square.  At every nonzero covector its kernel is
therefore trivial.  For coordinates coming from the actual bridges, vanishing
is equivalent to vanishing of both `U(1)` values and of the throat ghost at the
inspected point.  No operator domain or global differential cohomology is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9U1GhostPrincipalSymbolBridge4D
open P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
open P0EFTJanusD9GhostZeroModeCohomology4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- Coordinate form of the paired D9 principal symbol. -/
def d9PairedGhostPrincipalSymbol (covector : TangentVector3) :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9PairedGhostCoordinateSpace :=
  (normSquared covector) • LinearMap.id

@[simp] theorem d9PairedGhostPrincipalSymbol_apply
    (covector : TangentVector3) (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostPrincipalSymbol covector coordinate =
      normSquared covector • coordinate := by
  rfl

theorem d9PairedGhostPrincipalSymbol_firstU1
    (covector : TangentVector3) (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostFirstU1 (d9PairedGhostPrincipalSymbol covector coordinate) =
      normSquared covector * d9PairedGhostFirstU1 coordinate := by
  rfl

theorem d9PairedGhostPrincipalSymbol_secondU1
    (covector : TangentVector3) (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostSecondU1 (d9PairedGhostPrincipalSymbol covector coordinate) =
      normSquared covector * d9PairedGhostSecondU1 coordinate := by
  rfl

theorem d9PairedGhostPrincipalSymbol_diffeomorphism
    (covector : TangentVector3) (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostDiffeomorphism
        (d9PairedGhostPrincipalSymbol covector coordinate) =
      normSquared covector • d9PairedGhostDiffeomorphism coordinate := by
  rfl

theorem d9PairedGhostPrincipalSymbol_injective
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Function.Injective (d9PairedGhostPrincipalSymbol covector) := by
  intro first second hSymbol
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  simpa [d9PairedGhostPrincipalSymbol, hNorm] using hSymbol

theorem d9PairedGhostPrincipalSymbol_ker
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9PairedGhostPrincipalSymbol covector) = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (d9PairedGhostPrincipalSymbol_injective covector hCovector)

theorem d9PairedGhostPrincipalSymbol_surjective
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Function.Surjective (d9PairedGhostPrincipalSymbol covector) := by
  intro coordinate
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  refine ⟨(normSquared covector)⁻¹ • coordinate, ?_⟩
  simp [d9PairedGhostPrincipalSymbol, hNorm]

theorem d9PairedGhostPrincipalSymbol_range
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.range (d9PairedGhostPrincipalSymbol covector) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (d9PairedGhostPrincipalSymbol_surjective covector hCovector)

theorem d9PairedGhostPrincipalSymbol_ker_classification
    (covector : TangentVector3) :
    (covector = zeroTangent →
      LinearMap.ker (d9PairedGhostPrincipalSymbol covector) = ⊤) ∧
    (covector ≠ zeroTangent →
      LinearMap.ker (d9PairedGhostPrincipalSymbol covector) = ⊥) := by
  constructor
  · intro hCovector
    subst covector
    ext coordinate
    simp [d9PairedGhostPrincipalSymbol, zeroTangent, normSquared, tangentDot]
  · intro hCovector
    exact d9PairedGhostPrincipalSymbol_ker covector hCovector

theorem d9PairedGhostPrincipalSymbol_range_classification
    (covector : TangentVector3) :
    (covector = zeroTangent →
      LinearMap.range (d9PairedGhostPrincipalSymbol covector) = ⊥) ∧
    (covector ≠ zeroTangent →
      LinearMap.range (d9PairedGhostPrincipalSymbol covector) = ⊤) := by
  constructor
  · intro hCovector
    subst covector
    ext coordinate
    simp [d9PairedGhostPrincipalSymbol, zeroTangent, normSquared, tangentDot]
  · intro hCovector
    exact d9PairedGhostPrincipalSymbol_range covector hCovector

theorem d9PairedGhostPrincipalSymbol_bijective
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Function.Bijective (d9PairedGhostPrincipalSymbol covector) :=
  ⟨d9PairedGhostPrincipalSymbol_injective covector hCovector,
    d9PairedGhostPrincipalSymbol_surjective covector hCovector⟩

/-- Explicit inverse of the paired symbol at a nonzero covector. -/
def d9PairedGhostPrincipalSymbolInverse (covector : TangentVector3) :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9PairedGhostCoordinateSpace :=
  (normSquared covector)⁻¹ • LinearMap.id

theorem d9PairedGhostPrincipalSymbolInverse_left
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostPrincipalSymbolInverse covector
        (d9PairedGhostPrincipalSymbol covector coordinate) = coordinate := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  simp [d9PairedGhostPrincipalSymbolInverse, d9PairedGhostPrincipalSymbol, hNorm]

theorem d9PairedGhostPrincipalSymbolInverse_right
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostPrincipalSymbol covector
        (d9PairedGhostPrincipalSymbolInverse covector coordinate) = coordinate := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  simp [d9PairedGhostPrincipalSymbolInverse, d9PairedGhostPrincipalSymbol, hNorm]

/-- The paired nonzero symbol as an effective linear equivalence. -/
def d9PairedGhostPrincipalSymbolEquiv
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    D9PairedGhostCoordinateSpace ≃ₗ[Real] D9PairedGhostCoordinateSpace where
  toLinearMap := d9PairedGhostPrincipalSymbol covector
  invFun := d9PairedGhostPrincipalSymbolInverse covector
  left_inv := d9PairedGhostPrincipalSymbolInverse_left covector hCovector
  right_inv := d9PairedGhostPrincipalSymbolInverse_right covector hCovector

theorem d9PairedGhostPrincipalSymbol_eq_zero_iff
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostPrincipalSymbol covector coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro hSymbol
    exact (d9PairedGhostPrincipalSymbol_injective covector hCovector)
      (hSymbol.trans (map_zero (d9PairedGhostPrincipalSymbol covector)).symm)
  · rintro rfl
    exact map_zero _

/-- Package the already constructed throat ghost coordinates. -/
def d9DiffeomorphismGhostCoordinates
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real × Real × Real :=
  let tangent := throatTangentToD9 (ghost point)
  (tangent.x, tangent.y, tangent.z)

theorem d9DiffeomorphismGhostCoordinates_eq_zero_iff
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9DiffeomorphismGhostCoordinates period hPeriod ghost point = 0 ↔
      ghost point = 0 := by
  constructor
  · intro hCoordinates
    have hx : (throatTangentToD9 (ghost point)).x = 0 := by
      simpa [d9DiffeomorphismGhostCoordinates] using
        congrArg (fun value => value.1) hCoordinates
    have hy : (throatTangentToD9 (ghost point)).y = 0 := by
      simpa [d9DiffeomorphismGhostCoordinates] using
        congrArg (fun value => value.2.1) hCoordinates
    have hz : (throatTangentToD9 (ghost point)).z = 0 := by
      simpa [d9DiffeomorphismGhostCoordinates] using
        congrArg (fun value => value.2.2) hCoordinates
    have hPacked : throatTangentToD9 (ghost point) = zeroTangent := by
      apply TangentVector3.ext <;> simp_all [zeroTangent]
    apply throatTangentToD9_injective
    exact hPacked.trans throatTangentToD9_zero.symm
  · intro hGhost
    change (ghost point : ThroatCoverCoordinates) = 0 at hGhost
    have hPacked : throatTangentToD9 (ghost point) = zeroTangent :=
      (congrArg throatTangentToD9 hGhost).trans throatTangentToD9_zero
    rw [d9DiffeomorphismGhostCoordinates, hPacked]
    rfl

/-- Actual paired Program-P coordinate including the genuine throat ghost. -/
def d9PairedProgramGhostCoordinateFull
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) : D9PairedGhostCoordinateSpace :=
  d9PairedProgramGhostCoordinate period hPeriod variation column point
    (d9DiffeomorphismGhostCoordinates period hPeriod ghost point)

theorem d9PairedProgramGhostPrincipalSymbol_eq_zero_iff
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostPrincipalSymbol covector
        (d9PairedProgramGhostCoordinateFull period hPeriod variation column
          ghost point) = 0 ↔
      d9U1Ghost period hPeriod variation .plus column point = 0 ∧
      d9U1Ghost period hPeriod variation .minus column point = 0 ∧
      ghost point = 0 := by
  rw [d9PairedGhostPrincipalSymbol_eq_zero_iff covector hCovector]
  simp [d9PairedProgramGhostCoordinateFull, d9PairedProgramGhostCoordinate,
    d9DiffeomorphismGhostCoordinates_eq_zero_iff]

/-- Each paired coordinate projection agrees with the corresponding genuine
single-sector D9 principal-symbol bridge. -/
theorem d9PairedProgramGhostPrincipalSymbol_u1_projections
    (covector : TangentVector3)
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostFirstU1
        (d9PairedGhostPrincipalSymbol covector
          (d9PairedProgramGhostCoordinateFull period hPeriod variation column
            ghost point)) =
        (ghostPrincipalSymbol covector
          (d9U1OnlyGhostField period hPeriod variation .plus column point)).u1Ghost ∧
      d9PairedGhostSecondU1
        (d9PairedGhostPrincipalSymbol covector
          (d9PairedProgramGhostCoordinateFull period hPeriod variation column
            ghost point)) =
        (ghostPrincipalSymbol covector
          (d9U1OnlyGhostField period hPeriod variation .minus column point)).u1Ghost := by
  constructor <;> rfl

end
end P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D
end JanusFormal
