import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9GhostZeroModeCohomology4D

/-!
# Paired U(1) D9 ghost cohomology at the zero mode

The two genuine Program-P outer sectors supply two independent `U(1)` ghost
coordinates.  Together with the already constructed three diffeomorphism
coordinates, they form a five-coordinate paired zero-symbol complex.  Its
differential is zero, so its kernel, range, and quotient cohomology are
computed exactly.  This remains a zero-covector symbol calculation; no domain
or cohomology statement for the global differential operator is made.
-/

namespace JanusFormal
namespace P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9U1GhostPrincipalSymbolBridge4D
open P0EFTJanusD9GhostZeroModeCohomology4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- Five real coordinates: the additional outer-sector `U(1)` coordinate,
followed by the existing `U(1) + diffeomorphism³` D9 coordinates. -/
abbrev D9PairedGhostCoordinateSpace := Real × D9GhostCoordinateSpace

def d9PairedGhostFirstU1
    (coordinate : D9PairedGhostCoordinateSpace) : Real := coordinate.1

def d9PairedGhostSecondU1
    (coordinate : D9PairedGhostCoordinateSpace) : Real := coordinate.2.1

def d9PairedGhostDiffeomorphism
    (coordinate : D9PairedGhostCoordinateSpace) : Real × Real × Real :=
  coordinate.2.2

/-- Concrete coordinate supplied by the two true Program-P sector bridges,
with the already constructed diffeomorphism coordinates kept explicit. -/
def d9PairedProgramGhostCoordinate
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (diffeomorphism : Real × Real × Real) :
    D9PairedGhostCoordinateSpace :=
  (d9U1Ghost period hPeriod variation .plus column point,
    (d9U1Ghost period hPeriod variation .minus column point, diffeomorphism))

@[simp] theorem d9PairedProgramGhostCoordinate_firstU1
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (diffeomorphism : Real × Real × Real) :
    d9PairedGhostFirstU1
      (d9PairedProgramGhostCoordinate period hPeriod variation column point
        diffeomorphism) =
      d9U1Ghost period hPeriod variation .plus column point := rfl

@[simp] theorem d9PairedProgramGhostCoordinate_secondU1
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (diffeomorphism : Real × Real × Real) :
    d9PairedGhostSecondU1
      (d9PairedProgramGhostCoordinate period hPeriod variation column point
        diffeomorphism) =
      d9U1Ghost period hPeriod variation .minus column point := rfl

@[simp] theorem d9PairedProgramGhostCoordinate_diffeomorphism
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (diffeomorphism : Real × Real × Real) :
    d9PairedGhostDiffeomorphism
      (d9PairedProgramGhostCoordinate period hPeriod variation column point
        diffeomorphism) = diffeomorphism := rfl

/-- The two actual `U(1)`-only D9 bridge fields, one for each outer sector. -/
def d9PairedU1OnlyGhostFields
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    GaugeFixedGhostField × GaugeFixedGhostField :=
  (d9U1OnlyGhostField period hPeriod variation .plus column point,
    d9U1OnlyGhostField period hPeriod variation .minus column point)

@[simp] theorem d9PairedU1OnlyGhostFields_first_u1
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (d9PairedU1OnlyGhostFields period hPeriod variation column point).1.u1Ghost =
      d9U1Ghost period hPeriod variation .plus column point := rfl

@[simp] theorem d9PairedU1OnlyGhostFields_second_u1
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (d9PairedU1OnlyGhostFields period hPeriod variation column point).2.u1Ghost =
      d9U1Ghost period hPeriod variation .minus column point := rfl

/-- Each genuine sector bridge has zero principal symbol at zero covector. -/
theorem ghostPrincipalSymbol_d9PairedU1Only_zero
    (variation : IndependentFieldVariation period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    ghostPrincipalSymbol zeroTangent
        (d9PairedU1OnlyGhostFields period hPeriod variation column point).1 =
        zeroGhostField ∧
      ghostPrincipalSymbol zeroTangent
        (d9PairedU1OnlyGhostFields period hPeriod variation column point).2 =
        zeroGhostField := by
  constructor <;> apply GaugeFixedGhostField.ext <;>
    simp [d9PairedU1OnlyGhostFields, ghostPrincipalSymbol,
      d9U1OnlyGhostField, zeroTangent, normSquared, tangentDot,
      ghostLaplacianSymbol, zeroGhostField, scaleTangent]

/-- Differential of the paired five-coordinate zero-symbol complex. -/
def d9PairedGhostZeroModeDifferential :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9PairedGhostCoordinateSpace := 0

theorem d9PairedGhostZeroModeDifferential_ker :
    LinearMap.ker d9PairedGhostZeroModeDifferential = ⊤ :=
  LinearMap.ker_zero

theorem d9PairedGhostZeroModeDifferential_range :
    LinearMap.range d9PairedGhostZeroModeDifferential = ⊥ :=
  LinearMap.range_zero

abbrev D9PairedGhostZeroModeCohomology :=
  D9PairedGhostCoordinateSpace ⧸
    (LinearMap.range d9PairedGhostZeroModeDifferential)

def d9PairedGhostZeroModeCohomologyProjection :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9PairedGhostZeroModeCohomology :=
  (LinearMap.range d9PairedGhostZeroModeDifferential).mkQ

theorem d9PairedGhostZeroModeCohomologyProjection_injective :
    Function.Injective d9PairedGhostZeroModeCohomologyProjection := by
  apply LinearMap.ker_eq_bot.mp
  rw [d9PairedGhostZeroModeCohomologyProjection, Submodule.ker_mkQ,
    d9PairedGhostZeroModeDifferential_range]

theorem d9PairedGhostZeroModeCohomologyProjection_surjective :
    Function.Surjective d9PairedGhostZeroModeCohomologyProjection :=
  Submodule.mkQ_surjective _

def d9PairedGhostZeroModeCohomologyEquiv :
    D9PairedGhostCoordinateSpace ≃ₗ[Real] D9PairedGhostZeroModeCohomology :=
  LinearEquiv.ofBijective d9PairedGhostZeroModeCohomologyProjection
    ⟨d9PairedGhostZeroModeCohomologyProjection_injective,
      d9PairedGhostZeroModeCohomologyProjection_surjective⟩

/-- Complete certificate for the paired zero-covector symbol complex. -/
theorem d9_paired_u1_ghost_zero_mode_cohomology4D :
    LinearMap.ker d9PairedGhostZeroModeDifferential = ⊤ ∧
      LinearMap.range d9PairedGhostZeroModeDifferential = ⊥ ∧
      Function.Bijective d9PairedGhostZeroModeCohomologyProjection :=
  ⟨d9PairedGhostZeroModeDifferential_ker,
    d9PairedGhostZeroModeDifferential_range,
    d9PairedGhostZeroModeCohomologyProjection_injective,
    d9PairedGhostZeroModeCohomologyProjection_surjective⟩

end
end P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
end JanusFormal
