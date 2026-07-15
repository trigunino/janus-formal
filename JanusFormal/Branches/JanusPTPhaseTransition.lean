import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT01OrderParameter
import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT02LandauMinima
import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT03ScaleNoGo

namespace JanusFormal
namespace JanusPTPhaseTransition

structure ProgramStatus where
  pt01ParityClassification : Prop
  pt02ConditionalMinima : Prop
  pt03ScaleNoGo : Prop
  physicalPotentialFromP : Prop

def conditionalCoreClosed (s : ProgramStatus) : Prop :=
  s.pt01ParityClassification ∧ s.pt02ConditionalMinima ∧ s.pt03ScaleNoGo

end JanusPTPhaseTransition
end JanusFormal
