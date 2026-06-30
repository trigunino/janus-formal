import JanusFormal.P0EFTThinShellCompositeQTQA

namespace JanusFormal
namespace P0EFTCayleyShellNormalization

set_option autoImplicit false

structure CayleyShellNormalization where
  symmetricThinShellValue : Prop
  cayleyTransitionDefined : Prop
  cayleyTransitionInvertible : Prop
  chiralProjectorRankHalf : Prop
  pinMinusRatioInserted : Prop
  singularLimitDerived : Prop
  boundaryEulerLagrangeProjectorDerived : Prop

def finiteCayleyCannotBeProjector (c : CayleyShellNormalization) : Prop :=
  c.cayleyTransitionDefined /\
  c.cayleyTransitionInvertible /\
  c.chiralProjectorRankHalf

def cayleyClosureRequiresExtraSelection (c : CayleyShellNormalization) : Prop :=
  c.symmetricThinShellValue /\
  c.cayleyTransitionDefined /\
  c.pinMinusRatioInserted /\
  (c.singularLimitDerived \/ c.boundaryEulerLagrangeProjectorDerived)

theorem finite_invertible_cayley_blocks_projector_identification
    (c : CayleyShellNormalization)
    (hDefined : c.cayleyTransitionDefined)
    (hInvertible : c.cayleyTransitionInvertible)
    (hProjector : c.chiralProjectorRankHalf) :
    finiteCayleyCannotBeProjector c := by
  exact And.intro hDefined (And.intro hInvertible hProjector)

theorem pin_minus_ratio_alone_does_not_close_cayley
    (c : CayleyShellNormalization)
    (hNoSingular : Not c.singularLimitDerived)
    (hNoBoundary : Not c.boundaryEulerLagrangeProjectorDerived) :
    Not (cayleyClosureRequiresExtraSelection c) := by
  intro h
  cases h.right.right.right with
  | inl hs => exact hNoSingular hs
  | inr hb => exact hNoBoundary hb

theorem singular_or_boundary_selection_closes_cayley_conditionally
    (c : CayleyShellNormalization)
    (hSym : c.symmetricThinShellValue)
    (hDefined : c.cayleyTransitionDefined)
    (hPin : c.pinMinusRatioInserted)
    (hSelect : c.singularLimitDerived \/ c.boundaryEulerLagrangeProjectorDerived) :
    cayleyClosureRequiresExtraSelection c := by
  exact And.intro hSym (And.intro hDefined (And.intro hPin hSelect))

end P0EFTCayleyShellNormalization
end JanusFormal
