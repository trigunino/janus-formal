import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTAPSPinTraceGlobalDerivation
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldVolumeCoverClassification
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4FullActionAssemblyTarget
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4FullActionWardClosure
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4PureMathClosureAuditGate

namespace JanusFormal
namespace P0EFTJanusZ4HardGlobalTheoremReductionGate

set_option autoImplicit false

structure HardGlobalTheoremReductionGate where
  apsIndexPackageClosed : Prop
  janusCoverRatioDerived : Prop
  fullActionVariationClosed : Prop
  fullActionWardClosed : Prop
  apsGlobalTheoremReducedToIndexPackage : Prop
  orbifoldGlobalTheoremReducedToCoverRatio : Prop
  uniqueActionReducedToVariationAndWard : Prop
  allReducedObligationsClosed : Prop
  pureMathModelClosedWithoutAxioms : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def reducedObligationsClosed (g : HardGlobalTheoremReductionGate) : Prop :=
  g.apsIndexPackageClosed /\
  g.janusCoverRatioDerived /\
  g.fullActionVariationClosed /\
  g.fullActionWardClosed /\
  g.apsGlobalTheoremReducedToIndexPackage /\
  g.orbifoldGlobalTheoremReducedToCoverRatio /\
  g.uniqueActionReducedToVariationAndWard

theorem reduced_obligations_are_the_reduction_certificate
    (g : HardGlobalTheoremReductionGate)
    (h : reducedObligationsClosed g) :
    g.apsIndexPackageClosed /\ g.janusCoverRatioDerived /\
    g.fullActionVariationClosed /\ g.fullActionWardClosed := by
  exact And.intro h.left
    (And.intro h.right.left
      (And.intro h.right.right.left h.right.right.right.left))

theorem missing_action_variation_blocks_reduced_closure
    (g : HardGlobalTheoremReductionGate)
    (hMissing : Not g.fullActionVariationClosed) :
    Not (reducedObligationsClosed g) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_ward_closure_blocks_reduced_closure
    (g : HardGlobalTheoremReductionGate)
    (hMissing : Not g.fullActionWardClosed) :
    Not (reducedObligationsClosed g) := by
  intro h
  exact hMissing h.right.right.right.left

theorem pure_closure_requires_reduced_obligations
    (g : HardGlobalTheoremReductionGate)
    (hImplies : g.pureMathModelClosedWithoutAxioms -> reducedObligationsClosed g)
    (hClosed : g.pureMathModelClosedWithoutAxioms) :
    reducedObligationsClosed g := by
  exact hImplies hClosed

end P0EFTJanusZ4HardGlobalTheoremReductionGate
end JanusFormal
