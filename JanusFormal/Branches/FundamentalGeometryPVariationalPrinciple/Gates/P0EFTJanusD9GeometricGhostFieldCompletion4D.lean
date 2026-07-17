import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD8NormalBundleD9DisplacementBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D

/-!
# Geometric diffeomorphism ghost in the D9 field package

The D9 diffeomorphism ghost is an independent smooth tangent ghost, not a
component of a bosonic field variation.  This gate inserts the already
constructed global throat ghost into the residual D9 field package.  After
the genuine D8 normal displacement and this ghost are supplied, only the
matter-to-spinor identification remains as local completion data.
-/

namespace JanusFormal
namespace P0EFTJanusD9GeometricGhostFieldCompletion4D

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

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)

/-- Once the normal displacement and the genuine smooth diffeomorphism ghost
are fields in their own right, only the matter/spinor type identification is
still needed to fill the current local D9 record. -/
structure D9ResidualAfterNormalAndGhost (Spinor : Type*) where
  matterSpinorIdentification : MatterFiber ≃ Spinor

/-- Insert a genuine smooth throat ghost into the residual completion used by
the normal-bundle bridge. -/
def d9ResidualFromGeometricGhost
    {Spinor : Type*}
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (residual : D9ResidualAfterNormalAndGhost Spinor) :
    D9ResidualAfterNormalBundle Spinor where
  diffeomorphismGhost := throatTangentToD9 (ghost point)
  matterSpinorIdentification := residual.matterSpinorIdentification

@[simp] theorem d9ResidualFromGeometricGhost_diffeomorphismGhost
    {Spinor : Type*}
    (ghost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (residual : D9ResidualAfterNormalAndGhost Spinor) :
    (d9ResidualFromGeometricGhost period hPeriod ghost point residual).diffeomorphismGhost =
      throatTangentToD9 (ghost point) := rfl

/-- Complete local D9 field using the actual D8 normal section and the actual
smooth throat diffeomorphism ghost. -/
def d9LocalFieldFromNormalAndGeometricGhost
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod)
    (residual : D9ResidualAfterNormalAndGhost Spinor) : CompleteLocalField Spinor :=
  d9LocalFieldFromNormalBundle period hPeriod fields variation sector column
    point displacement anchor hPoint
    (d9ResidualFromGeometricGhost period hPeriod ghost point residual)

@[simp] theorem d9LocalFieldFromNormalAndGeometricGhost_normalMode
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod)
    (residual : D9ResidualAfterNormalAndGhost Spinor) :
    (d9LocalFieldFromNormalAndGeometricGhost period hPeriod fields variation
      sector column point displacement anchor hPoint ghost residual).bosonic.normalMode =
        localNormalMode period hPeriod displacement anchor point hPoint := rfl

@[simp] theorem d9LocalFieldFromNormalAndGeometricGhost_diffeomorphismGhost
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod)
    (residual : D9ResidualAfterNormalAndGhost Spinor) :
    (d9LocalFieldFromNormalAndGeometricGhost period hPeriod fields variation
      sector column point displacement anchor hPoint ghost residual).ghosts.diffeomorphismGhost =
        throatTangentToD9 (ghost point) := rfl

end
end P0EFTJanusD9GeometricGhostFieldCompletion4D
end JanusFormal
