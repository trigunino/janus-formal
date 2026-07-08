namespace JanusFormal
namespace P0EFTJanusComplexRealityEq131KKSProjectionGate

set_option autoImplicit false

structure Eq131KKSProjectionGate where
  publishedEq131AcceptedAsSourceAnchor : Prop
  rawEq131TranslationTermPreservesAntiHermitianMGenerically : Prop
  antiHermitianTranslationProjectionDeclared : Prop
  projectionMatchesRealAppendixPattern : Prop
  projectedTermPreservesAntiHermitianM : Prop

def eq131KKSProjectionReady (g : Eq131KKSProjectionGate) : Prop :=
  g.publishedEq131AcceptedAsSourceAnchor /\
  Not g.rawEq131TranslationTermPreservesAntiHermitianMGenerically /\
  g.antiHermitianTranslationProjectionDeclared /\
  g.projectionMatchesRealAppendixPattern /\
  g.projectedTermPreservesAntiHermitianM

theorem raw_eq131_translation_requires_projection
    (g : Eq131KKSProjectionGate)
    (h : eq131KKSProjectionReady g) :
    Not g.rawEq131TranslationTermPreservesAntiHermitianMGenerically := by
  rcases h with ⟨_, hRaw, _, _, _⟩
  exact hRaw

end P0EFTJanusComplexRealityEq131KKSProjectionGate
end JanusFormal
