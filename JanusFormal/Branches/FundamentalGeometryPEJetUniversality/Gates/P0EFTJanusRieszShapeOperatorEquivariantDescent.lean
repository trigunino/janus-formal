import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorBundleDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorEquivariantDescent

set_option autoImplicit false

noncomputable section

universe u v w x

/-- Coordinate changes and physical realization maps for one local atlas.

The realization law says directly that transporting coordinates from the first
chart to the second does not change the represented physical object. -/
structure EquivariantAtlas
    (Chart : Type u) (Base : Type v)
    (CoordinateFiber : Type w) (PhysicalFiber : Type x) where
  valid : Chart → Base → Prop
  transition : Chart → Chart → Base → CoordinateFiber ≃ CoordinateFiber
  realize : Chart → Base → CoordinateFiber ≃ PhysicalFiber
  cover : ∀ base, ∃ chart, valid chart base
  realize_transition :
    ∀ first second base,
      valid first base → valid second base →
        ∀ coordinate,
          realize second base (transition first second base coordinate) =
            realize first base coordinate

variable {Chart : Type u} {Base : Type v}
variable {CoordinateFiber : Type w} {PhysicalFiber : Type x}

/-- A local coordinate family is equivariant when its coordinates transform by
the atlas transition on overlaps. -/
def IsEquivariantLocalFamily
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber) : Prop :=
  ∀ first second base,
    atlas.valid first base → atlas.valid second base →
      localFamily second base =
        atlas.transition first second base (localFamily first base)

/-- Physical representative obtained by realizing one local coordinate value. -/
def physicalLocalValue
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber)
    (chart : Chart) (base : Base) : PhysicalFiber :=
  atlas.realize chart base (localFamily chart base)

/-- Equivariance of local coordinates implies equality of physical values on
every overlap. -/
theorem physicalLocalValue_compatible
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas localFamily)
    (first second : Chart) (base : Base)
    (hFirst : atlas.valid first base)
    (hSecond : atlas.valid second base) :
    physicalLocalValue atlas localFamily first base =
      physicalLocalValue atlas localFamily second base := by
  rw [physicalLocalValue, physicalLocalValue]
  rw [hEquivariant first second base hFirst hSecond]
  exact (atlas.realize_transition first second base hFirst hSecond
    (localFamily first base)).symm

/-- An equivariant local family canonically defines abstract descent data in the
physical fiber. -/
def descentDataOfEquivariantFamily
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas localFamily) :
    P0EFTJanusRieszShapeOperatorBundleDescent.LocalDescentData
      Chart Base PhysicalFiber where
  valid := atlas.valid
  localValue := physicalLocalValue atlas localFamily
  cover := atlas.cover
  compatible := by
    intro first second base hFirst hSecond
    exact physicalLocalValue_compatible atlas localFamily hEquivariant
      first second base hFirst hSecond

/-- Global physical object descended from an equivariant family of local
coordinates. -/
def descendedPhysicalValue
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas localFamily) :
    Base → PhysicalFiber :=
  P0EFTJanusRieszShapeOperatorBundleDescent.descendedValue
    (descentDataOfEquivariantFamily atlas localFamily hEquivariant)

/-- Every valid chart realizes exactly the descended physical value. -/
theorem physicalLocalValue_eq_descended
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (localFamily : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas localFamily)
    (chart : Chart) (base : Base)
    (hValid : atlas.valid chart base) :
    physicalLocalValue atlas localFamily chart base =
      descendedPhysicalValue atlas localFamily hEquivariant base := by
  exact
    P0EFTJanusRieszShapeOperatorBundleDescent.localValue_eq_descendedValue
      (descentDataOfEquivariantFamily atlas localFamily hEquivariant)
      chart base hValid

/-- Exact boundary of equivariant Riesz descent. -/
structure EquivariantRieszDescentStatus where
  coordinateTransitionLawProved : Prop
  physicalRealizationCompatibilityProved : Prop
  overlapPhysicalEqualityProved : Prop
  globalPhysicalValueDescended : Prop
  smoothAtlasConstructed : Prop
  smoothDescentProved : Prop
  actualJanusRieszFamilyInstantiated : Prop

/-- Full closure of equivariant Riesz descent. -/
def equivariantRieszDescentClosed
    (s : EquivariantRieszDescentStatus) : Prop :=
  s.coordinateTransitionLawProved ∧
  s.physicalRealizationCompatibilityProved ∧
  s.overlapPhysicalEqualityProved ∧
  s.globalPhysicalValueDescended ∧
  s.smoothAtlasConstructed ∧
  s.smoothDescentProved ∧
  s.actualJanusRieszFamilyInstantiated

/-- Algebraic equivariant descent does not construct the smooth Janus atlas. -/
theorem missing_smooth_atlas_blocks_equivariant_riesz_closure
    (s : EquivariantRieszDescentStatus)
    (hMissing : Not s.smoothAtlasConstructed) :
    Not (equivariantRieszDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorEquivariantDescent
end JanusFormal
