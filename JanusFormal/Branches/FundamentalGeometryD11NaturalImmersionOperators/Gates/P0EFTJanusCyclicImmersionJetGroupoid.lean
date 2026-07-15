import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusSpinCImmersionCategory

namespace JanusFormal
namespace P0EFTJanusCyclicImmersionJetGroupoid

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory

/-- One-object groupoid retaining the full integer mapping-torus monodromy. -/
def cyclicCategory : SmallCategoryData where
  Obj := Unit
  Hom := fun _ _ => ℤ
  identity := fun _ => 0
  compose := fun second first => first + second
  identity_compose := by intros; simp
  compose_identity := by intros; simp
  compose_assoc := by intros; omega

/-- Decorated cyclic immersion category attached to one global geometry. -/
def cyclicImmersionCategory
    (geometry : SpinCImmersionGeometry) : SpinCImmersionCategory where
  category := cyclicCategory
  geometry := fun _ => geometry
  admissible := fun _ => True
  identityAdmissible := by intros; trivial
  compositionAdmissible := by intros; trivial

/-- Quarter monodromy is a functorial additive code on cyclic morphisms. -/
def jetMonodromy (winding : ℤ) : ZMod 4 := winding

@[simp] theorem jet_monodromy_identity : jetMonodromy 0 = 0 := by rfl

theorem jet_monodromy_composition (first second : ℤ) :
    jetMonodromy (@cyclicCategory.compose () () () second first) =
      jetMonodromy first + jetMonodromy second := by
  change ((first + second : ℤ) : ZMod 4) =
    (first : ZMod 4) + (second : ZMod 4)
  push_cast
  rfl

/-- A finite jet transforms by the monodromy representation at every order. -/
def transformJet {Jet : Type*} (action : ZMod 4 → Jet → Jet)
    (winding : ℤ) (jet : Jet) : Jet :=
  action (jetMonodromy winding) jet

structure CyclicJetGlobalStatus where
  mappingTorusGroupoidIdentified : Prop
  decoratedCyclicCategoryConstructed : Prop
  jetBundlesConstructed : Prop
  monodromyActionConstructed : Prop
  identityLawProved : Prop
  compositionLawProved : Prop
  atlasDescentProved : Prop

def cyclicJetGlobalClosed (s : CyclicJetGlobalStatus) : Prop :=
  s.mappingTorusGroupoidIdentified ∧ s.decoratedCyclicCategoryConstructed ∧
  s.jetBundlesConstructed ∧ s.monodromyActionConstructed ∧
  s.identityLawProved ∧ s.compositionLawProved ∧ s.atlasDescentProved

end P0EFTJanusCyclicImmersionJetGroupoid
end JanusFormal
