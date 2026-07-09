import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermNonGHYAbsenceReadinessGate

set_option autoImplicit false

structure CountertermNonGHYAbsenceReadinessGate where
  knownPartitionClean : Prop
  activeFirstActionAssembled : Prop
  plusMinusMatterActionsReady : Prop
  crossTransportSourceAccepted : Prop
  canProveRemainingNonGHYAbsence : Prop
  canPromoteECountertermZero : Prop
  incompleteActionAbsenceProofForbidden : Prop

def nonGHYAbsenceReadiness
    (g : CountertermNonGHYAbsenceReadinessGate) : Prop :=
  g.knownPartitionClean /\
  g.activeFirstActionAssembled /\
  g.plusMinusMatterActionsReady /\
  g.crossTransportSourceAccepted /\
  g.incompleteActionAbsenceProofForbidden

theorem non_ghy_absence_requires_active_first_action
    (g : CountertermNonGHYAbsenceReadinessGate)
    (hReady : nonGHYAbsenceReadiness g) :
    g.activeFirstActionAssembled := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCountertermNonGHYAbsenceReadinessGate
end JanusFormal
