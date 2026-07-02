import JanusFormal.P0EFTGlobalTopologyMasterLock
import JanusFormal.P0EFTJanusZ4FullActionAssemblyTarget
import JanusFormal.P0EFTJanusZ4FullActionWardClosure

namespace JanusFormal
namespace P0EFTJanusZ4PureMathClosureAuditGate

set_option autoImplicit false

structure PureMathClosureAuditGate where
  apsPinScaffoldComplete : Prop
  orbifoldScaffoldComplete : Prop
  actionScaffoldComplete : Prop
  apsGlobalTheoremProvedWithoutAxioms : Prop
  orbifoldGlobalTheoremProvedWithoutAxioms : Prop
  uniqueActionVariationProvedWithoutAxioms : Prop
  pureMathModelClosedWithoutAxioms : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def allGlobalTheoremsClosed (g : PureMathClosureAuditGate) : Prop :=
  g.apsGlobalTheoremProvedWithoutAxioms /\
  g.orbifoldGlobalTheoremProvedWithoutAxioms /\
  g.uniqueActionVariationProvedWithoutAxioms

def scaffoldButNotClosed (g : PureMathClosureAuditGate) : Prop :=
  g.apsPinScaffoldComplete /\
  g.orbifoldScaffoldComplete /\
  g.actionScaffoldComplete /\
  Not (allGlobalTheoremsClosed g) /\
  Not g.pureMathModelClosedWithoutAxioms /\
  Not g.fullCosmologyPredictionReadyNoFit

theorem scaffold_without_global_theorems_blocks_no_fit
    (g : PureMathClosureAuditGate)
    (h : scaffoldButNotClosed g) :
    Not g.pureMathModelClosedWithoutAxioms /\ Not g.fullCosmologyPredictionReadyNoFit := by
  rcases h with ⟨_, _, _, _, hClosed, hNoFit⟩
  exact ⟨hClosed, hNoFit⟩

theorem all_global_theorems_are_required_for_pure_closure
    (g : PureMathClosureAuditGate)
    (hClosed : g.pureMathModelClosedWithoutAxioms)
    (hImplies : g.pureMathModelClosedWithoutAxioms -> allGlobalTheoremsClosed g) :
    allGlobalTheoremsClosed g := by
  exact hImplies hClosed

end P0EFTJanusZ4PureMathClosureAuditGate
end JanusFormal
