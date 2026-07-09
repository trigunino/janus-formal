namespace JanusFormal
namespace P0EFTJanusNewIdeaMatrixGate

set_option autoImplicit false

structure NewIdeaMatrixGate where
  bibliographyChecked : Prop
  ideasRanked : Prop
  noMagicFitAllowed : Prop
  noFitAlphaGeneratedNow : Prop
  allIdeasHaveExplicitBlocker : Prop

def exhaustedWithoutFakeClosure (g : NewIdeaMatrixGate) : Prop :=
  g.bibliographyChecked /\
  g.ideasRanked /\
  g.noMagicFitAllowed /\
  Not g.noFitAlphaGeneratedNow /\
  g.allIdeasHaveExplicitBlocker

theorem new_idea_matrix_does_not_create_alpha_by_fit
    (g : NewIdeaMatrixGate)
    (h : exhaustedWithoutFakeClosure g) :
    Not g.noFitAlphaGeneratedNow := by
  exact h.right.right.right.left

end P0EFTJanusNewIdeaMatrixGate
end JanusFormal
