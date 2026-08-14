import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusSpinCImmersionCategory

/-!
# Admissible isomorphisms in the SpinC immersion category

Program D11 originally records admissible morphisms, identities and
composition, but not invertible admissible morphisms as a first-class object.
This file adds the minimal groupoid interface needed for transporting natural
operator kernels between family parameters.
-/

namespace JanusFormal
namespace P0EFTJanusAdmissibleMorphismIsomorphism

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory

universe u v

/-- Two admissible morphisms are equal once their underlying categorical
morphisms are equal; preservation certificates are propositions. -/
@[ext]
theorem admissibleMorphism_ext
    {immersionCategory : SpinCImmersionCategory}
    {source target : immersionCategory.category.Obj}
    {first second : AdmissibleMorphism immersionCategory source target}
    (hMorphism : first.morphism = second.morphism) :
    first = second := by
  cases first with
  | mk firstMorphism firstPreservation =>
      cases second with
      | mk secondMorphism secondPreservation =>
          dsimp at hMorphism
          cases hMorphism
          rfl

/-- An admissible morphism equipped with an admissible two-sided inverse. -/
structure AdmissibleIsomorphism
    (immersionCategory : SpinCImmersionCategory)
    (source target : immersionCategory.category.Obj) where
  hom : AdmissibleMorphism immersionCategory source target
  inv : AdmissibleMorphism immersionCategory target source
  hom_inv_id :
    admissibleCompose immersionCategory hom inv =
      admissibleIdentity immersionCategory target
  inv_hom_id :
    admissibleCompose immersionCategory inv hom =
      admissibleIdentity immersionCategory source

namespace AdmissibleIsomorphism

/-- Identity admissible isomorphism. -/
def refl
    (immersionCategory : SpinCImmersionCategory)
    (object : immersionCategory.category.Obj) :
    AdmissibleIsomorphism immersionCategory object object where
  hom := admissibleIdentity immersionCategory object
  inv := admissibleIdentity immersionCategory object
  hom_inv_id := by
    apply admissibleMorphism_ext
    exact immersionCategory.category.identity_compose
      (immersionCategory.category.identity object)
  inv_hom_id := by
    apply admissibleMorphism_ext
    exact immersionCategory.category.identity_compose
      (immersionCategory.category.identity object)

/-- Reverse an admissible isomorphism. -/
def symm
    {immersionCategory : SpinCImmersionCategory}
    {source target : immersionCategory.category.Obj}
    (isomorphism : AdmissibleIsomorphism immersionCategory source target) :
    AdmissibleIsomorphism immersionCategory target source where
  hom := isomorphism.inv
  inv := isomorphism.hom
  hom_inv_id := isomorphism.inv_hom_id
  inv_hom_id := isomorphism.hom_inv_id

@[simp]
theorem refl_hom
    (immersionCategory : SpinCImmersionCategory)
    (object : immersionCategory.category.Obj) :
    (refl immersionCategory object).hom =
      admissibleIdentity immersionCategory object :=
  rfl

@[simp]
theorem refl_inv
    (immersionCategory : SpinCImmersionCategory)
    (object : immersionCategory.category.Obj) :
    (refl immersionCategory object).inv =
      admissibleIdentity immersionCategory object :=
  rfl

@[simp]
theorem symm_hom
    {immersionCategory : SpinCImmersionCategory}
    {source target : immersionCategory.category.Obj}
    (isomorphism : AdmissibleIsomorphism immersionCategory source target) :
    isomorphism.symm.hom = isomorphism.inv :=
  rfl

@[simp]
theorem symm_inv
    {immersionCategory : SpinCImmersionCategory}
    {source target : immersionCategory.category.Obj}
    (isomorphism : AdmissibleIsomorphism immersionCategory source target) :
    isomorphism.symm.inv = isomorphism.hom :=
  rfl

/-- Public admissible-isomorphism checkpoint. -/
theorem admissible_isomorphism_gate
    {immersionCategory : SpinCImmersionCategory}
    {source target : immersionCategory.category.Obj}
    (isomorphism : AdmissibleIsomorphism immersionCategory source target) :
    admissibleCompose immersionCategory isomorphism.hom isomorphism.inv =
        admissibleIdentity immersionCategory target ∧
      admissibleCompose immersionCategory isomorphism.inv isomorphism.hom =
        admissibleIdentity immersionCategory source :=
  ⟨isomorphism.hom_inv_id, isomorphism.inv_hom_id⟩

end AdmissibleIsomorphism

end P0EFTJanusAdmissibleMorphismIsomorphism
end JanusFormal