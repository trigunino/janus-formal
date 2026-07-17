import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9GeometricGhostFieldCompletion4D
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusCanonicalImmersionSymbolFamily

/-!
# D9 matter coefficient in the D11 squared-spinor coordinate fiber

The D9 matter fiber is Euclidean real four-space.  The D11 squared Dirac
block uses a real rank-four coordinate fiber.  Their canonical coordinate
equivalence closes the last type-level residual of the current local D9
record after the normal displacement and diffeomorphism ghost are supplied.

This gate does not identify a geometric SpinC bundle: that stronger claim
still requires a concrete spinor bundle and compatibility with its Clifford,
parallel-transport and boundary data.
-/

namespace JanusFormal
namespace P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
open P0EFTJanusD9GeometricGhostFieldCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)

/-- The real rank-four coordinate fiber used by D11 for the squared Dirac
block. -/
abbrev D9SquaredSpinorCoordinateFiber :=
  P0EFTJanusCanonicalImmersionSymbolFamily.CoordinateFiber 4

/-- Canonical coordinates identify the D9 matter fiber with the real
rank-four squared-spinor symbol fiber. -/
def matterFiberEquivSquaredSpinorCoordinates :
    MatterFiber ≃ D9SquaredSpinorCoordinateFiber :=
  (EuclideanSpace.equiv (Fin 4) Real).toLinearEquiv.toEquiv

@[simp] theorem matterFiberEquivSquaredSpinorCoordinates_apply
    (matter : MatterFiber) :
    matterFiberEquivSquaredSpinorCoordinates matter =
      EuclideanSpace.equiv (Fin 4) Real matter := rfl

/-- The coefficient-level D9 residual is discharged for the D11 real
squared-spinor coordinate slot. -/
def d9SquaredSpinorCoordinateResidual :
    D9ResidualAfterNormalAndGhost D9SquaredSpinorCoordinateFiber where
  matterSpinorIdentification := matterFiberEquivSquaredSpinorCoordinates

/-- Complete the local D9 field in the real squared-spinor coordinate
specialization. -/
def d9LocalFieldWithSquaredSpinorCoordinates
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    CompleteLocalField D9SquaredSpinorCoordinateFiber :=
  d9LocalFieldFromNormalAndGeometricGhost period hPeriod fields variation
    sector column point displacement anchor hPoint ghost
    d9SquaredSpinorCoordinateResidual

@[simp] theorem d9LocalFieldWithSquaredSpinorCoordinates_spinor
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    (d9LocalFieldWithSquaredSpinorCoordinates period hPeriod fields variation
      sector column point displacement anchor hPoint ghost).spinor =
        EuclideanSpace.equiv (Fin 4) Real
          (d9MatterCoefficient period hPeriod variation sector point) := rfl

end
end P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D
end JanusFormal
