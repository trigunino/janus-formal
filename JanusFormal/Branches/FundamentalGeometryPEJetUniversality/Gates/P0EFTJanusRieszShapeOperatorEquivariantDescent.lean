import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorBundleDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorEquivariantDescent

set_option autoImplicit false

noncomputable section

universe u v w x

/-- Coordinate changes and physical realization maps for one local atlas.

The identity `realize second ∘ transition first second = realize first` says
that a coordinate vector transported to the second chart represents the same
physical object. -/
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
        (realize second base).trans
          (transition first second base).symm = realize first base

variable {Chart : Type u} {Base : Type v}
variable {CoordinateFiber : Type w} {PhysicalFiber : Type x}

/-- A local coordinate family is equivariant when its coordinates transform by
the atlas transition on overlaps. -/
def IsEquivariantLocalFamily
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber) : Prop :=
  ∀ first second base,
    atlas.valid first base → atlas.valid second base →
      local second base = atlas.transition first second base (local first base)

/-- Physical representative obtained by realizing one local coordinate value. -/
def physicalLocalValue
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber)
    (chart : Chart) (base : Base) : PhysicalFiber :=
  atlas.realize chart base (local chart base)

/-- Equivariance of local coordinates implies equality of physical values on
every overlap. This is the precise bridge from the existing Riesz overlap law
to abstract global descent. -/
theorem physicalLocalValue_compatible
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas local)
    (first second : Chart) (base : Base)
    (hFirst : atlas.valid first base)
    (hSecond : atlas.valid second base) :
    physicalLocalValue atlas local first base =
      physicalLocalValue atlas local second base := by
  rw [physicalLocalValue, physicalLocalValue]
  rw [hEquivariant first second base hFirst hSecond]
  have hRealize := atlas.realize_transition first second base hFirst hSecond
  apply (atlas.realize second base).injective
  change
    (atlas.realize second base).symm
        (atlas.realize first base (local first base)) =
      atlas.transition first second base (local first base)
  have hApply := congrArg
    (fun equivalence : CoordinateFiber ≃ PhysicalFiber =>
      equivalence (local first base)) hRealize
  simpa using congrArg (atlas.realize second base).symm hApply

/-- An equivariant local family canonically defines abstract descent data in the
physical fiber. -/
def descentDataOfEquivariantFamily
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas local) :
    P0EFTJanusRieszShapeOperatorBundleDescent.LocalDescentData
      Chart Base PhysicalFiber where
  valid := atlas.valid
  localValue := physicalLocalValue atlas local
  cover := atlas.cover
  compatible := by
    intro first second base hFirst hSecond
    exact physicalLocalValue_compatible atlas local hEquivariant
      first second base hFirst hSecond

/-- Global physical object descended from an equivariant family of local
coordinates. -/
def descendedPhysicalValue
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas local) :
    Base → PhysicalFiber :=
  P0EFTJanusRieszShapeOperatorBundleDescent.descendedValue
    (descentDataOfEquivariantFamily atlas local hEquivariant)

/-- Every valid chart realizes exactly the descended physical value. -/
theorem physicalLocalValue_eq_descended
    (atlas : EquivariantAtlas Chart Base CoordinateFiber PhysicalFiber)
    (local : Chart → Base → CoordinateFiber)
    (hEquivariant : IsEquivariantLocalFamily atlas local)
    (chart : Chart) (base : Base)
    (hValid : atlas.valid chart base) :
    physicalLocalValue atlas local chart base =
      descendedPhysicalValue atlas local hEquivariant base := by
  exact
    P0EFTJanusRieszShapeOperatorBundleDescent.localValue_eq_descendedValue
      (descentDataOfEquivariantFamily atlas local hEquivariant)
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
