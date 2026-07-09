import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4InternalTransferFrontierVerdictGate

namespace JanusFormal
namespace P0EFTJanusSym4SchurIrreducibilityObstructionGate

set_option autoImplicit false

structure Sym4SchurIrreducibilityObstructionGate where
  Sym4C11IrreducibleUnderNaturalAction : Prop
  HFullyInvariantUnderNaturalAction : Prop
  SchurForcesHScalar : Prop
  HScalarOrders1001States : Prop
  derivedSymmetryBreakingNormalGenerator : Prop
  modularStateHamiltonianDerived : Prop

def SchurCompatibleNontrivialHClosed
    (g : Sym4SchurIrreducibilityObstructionGate) : Prop :=
  g.Sym4C11IrreducibleUnderNaturalAction /\
  (
    g.derivedSymmetryBreakingNormalGenerator \/
    g.modularStateHamiltonianDerived
  )

def SchurObstructionFrontier
    (g : Sym4SchurIrreducibilityObstructionGate) : Prop :=
  g.Sym4C11IrreducibleUnderNaturalAction /\
  g.HFullyInvariantUnderNaturalAction /\
  g.SchurForcesHScalar /\
  Not g.HScalarOrders1001States /\
  Not g.derivedSymmetryBreakingNormalGenerator /\
  Not g.modularStateHamiltonianDerived

theorem full_invariance_plus_schur_blocks_nontrivial_sym4_ordering
    (g : Sym4SchurIrreducibilityObstructionGate)
    (hFrontier : SchurObstructionFrontier g) :
    Not (SchurCompatibleNontrivialHClosed g) := by
  intro h
  rcases h.2 with hBreak | hModular
  · exact hFrontier.2.2.2.2.1 hBreak
  · exact hFrontier.2.2.2.2.2 hModular

end P0EFTJanusSym4SchurIrreducibilityObstructionGate
end JanusFormal
