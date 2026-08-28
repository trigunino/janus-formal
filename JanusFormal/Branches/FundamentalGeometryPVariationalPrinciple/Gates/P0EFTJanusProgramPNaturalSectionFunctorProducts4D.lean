import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalBundleFunctor

/-!
# Products of D11 natural section functors and operators

Candidate-A is intrinsically multi-sector.  D11 exposes natural section functors
one bundle at a time, so this file supplies the missing categorical product
construction.  Pullback acts componentwise and natural operators combine into a
block-diagonal product operator whose naturality is inherited automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNaturalSectionFunctorProducts4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor

variable {immersionCategory : SpinCImmersionCategory}

/-- Binary product of natural section functors. -/
def naturalSectionFunctorProd
    (first second : NaturalSectionFunctor immersionCategory) :
    NaturalSectionFunctor immersionCategory where
  Section := fun object => first.Section object × second.Section object
  pullback := fun morphism sectionValue =>
    (first.pullback morphism sectionValue.1,
      second.pullback morphism sectionValue.2)
  pullbackIdentity := by
    intro object sectionValue
    ext
    · exact first.pullbackIdentity object sectionValue.1
    · exact second.pullbackIdentity object sectionValue.2
  pullbackComposition := by
    intro firstObject secondObject thirdObject secondMorphism firstMorphism sectionValue
    ext
    · exact first.pullbackComposition
        secondMorphism firstMorphism sectionValue.1
    · exact second.pullbackComposition
        secondMorphism firstMorphism sectionValue.2

@[simp]
theorem naturalSectionFunctorProd_pullback_fst
    (first second : NaturalSectionFunctor immersionCategory)
    {source target : immersionCategory.category.Obj}
    (morphism : AdmissibleMorphism immersionCategory source target)
    (sectionValue : (naturalSectionFunctorProd first second).Section target) :
    ((naturalSectionFunctorProd first second).pullback morphism sectionValue).1 =
      first.pullback morphism sectionValue.1 :=
  rfl

@[simp]
theorem naturalSectionFunctorProd_pullback_snd
    (first second : NaturalSectionFunctor immersionCategory)
    {source target : immersionCategory.category.Obj}
    (morphism : AdmissibleMorphism immersionCategory source target)
    (sectionValue : (naturalSectionFunctorProd first second).Section target) :
    ((naturalSectionFunctorProd first second).pullback morphism sectionValue).2 =
      second.pullback morphism sectionValue.2 :=
  rfl

/-- Product of two natural operators, acting block-diagonally. -/
def naturalOperatorProd
    {sourceFirst targetFirst sourceSecond targetSecond :
      NaturalSectionFunctor immersionCategory}
    (first : NaturalOperator immersionCategory sourceFirst targetFirst)
    (second : NaturalOperator immersionCategory sourceSecond targetSecond) :
    NaturalOperator immersionCategory
      (naturalSectionFunctorProd sourceFirst sourceSecond)
      (naturalSectionFunctorProd targetFirst targetSecond) where
  apply := fun object sectionValue =>
    (first.apply object sectionValue.1,
      second.apply object sectionValue.2)
  naturality := by
    intro source target morphism sectionValue
    apply Prod.ext
    · exact first.naturality morphism sectionValue.1
    · exact second.naturality morphism sectionValue.2

@[simp]
theorem naturalOperatorProd_apply_fst
    {sourceFirst targetFirst sourceSecond targetSecond :
      NaturalSectionFunctor immersionCategory}
    (first : NaturalOperator immersionCategory sourceFirst targetFirst)
    (second : NaturalOperator immersionCategory sourceSecond targetSecond)
    (object : immersionCategory.category.Obj)
    (sectionValue :
      (naturalSectionFunctorProd sourceFirst sourceSecond).Section object) :
    ((naturalOperatorProd first second).apply object sectionValue).1 =
      first.apply object sectionValue.1 :=
  rfl

@[simp]
theorem naturalOperatorProd_apply_snd
    {sourceFirst targetFirst sourceSecond targetSecond :
      NaturalSectionFunctor immersionCategory}
    (first : NaturalOperator immersionCategory sourceFirst targetFirst)
    (second : NaturalOperator immersionCategory sourceSecond targetSecond)
    (object : immersionCategory.category.Obj)
    (sectionValue :
      (naturalSectionFunctorProd sourceFirst sourceSecond).Section object) :
    ((naturalOperatorProd first second).apply object sectionValue).2 =
      second.apply object sectionValue.2 :=
  rfl

/-- Product naturality is available without any additional compatibility input. -/
theorem natural_operator_prod_gate
    {sourceFirst targetFirst sourceSecond targetSecond :
      NaturalSectionFunctor immersionCategory}
    (first : NaturalOperator immersionCategory sourceFirst targetFirst)
    (second : NaturalOperator immersionCategory sourceSecond targetSecond) :
    ∀ {source target : immersionCategory.category.Obj}
      (morphism : AdmissibleMorphism immersionCategory source target)
      (sectionValue :
        (naturalSectionFunctorProd sourceFirst sourceSecond).Section target),
      (naturalSectionFunctorProd targetFirst targetSecond).pullback morphism
          ((naturalOperatorProd first second).apply target sectionValue) =
        (naturalOperatorProd first second).apply source
          ((naturalSectionFunctorProd sourceFirst sourceSecond).pullback
            morphism sectionValue) :=
  (naturalOperatorProd first second).naturality

end
end P0EFTJanusProgramPNaturalSectionFunctorProducts4D
end JanusFormal
