import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4SchurIrreducibilityObstructionGate

namespace JanusFormal
namespace P0EFTJanusHnormalSymmetryBreakingCandidateMatrixGate

set_option autoImplicit false

structure HnormalSymmetryBreakingCandidateMatrixGate where
  SchurObstructionActive : Prop
  PTNormalGeneratorJanusAnchored : Prop
  PTNormalInternalSym4MatrixDerived : Prop
  BoundaryModularStateDerived : Prop
  CosmologicalTimeGeneratorScalarOnly : Prop
  ComponentwiseTripletDirectionUnanchored : Prop
  AdmissibleCloserNow : Prop

def HnormalSymmetryBreakingClosed
    (g : HnormalSymmetryBreakingCandidateMatrixGate) : Prop :=
  g.SchurObstructionActive /\
  (
    (g.PTNormalGeneratorJanusAnchored /\ g.PTNormalInternalSym4MatrixDerived) \/
    g.BoundaryModularStateDerived
  ) /\
  g.AdmissibleCloserNow

def HnormalSymmetryBreakingFrontier
    (g : HnormalSymmetryBreakingCandidateMatrixGate) : Prop :=
  g.SchurObstructionActive /\
  g.PTNormalGeneratorJanusAnchored /\
  Not g.PTNormalInternalSym4MatrixDerived /\
  Not g.BoundaryModularStateDerived /\
  g.CosmologicalTimeGeneratorScalarOnly /\
  g.ComponentwiseTripletDirectionUnanchored /\
  Not g.AdmissibleCloserNow

theorem no_internal_PT_matrix_blocks_symmetry_breaking_closure
    (g : HnormalSymmetryBreakingCandidateMatrixGate)
    (hFrontier : HnormalSymmetryBreakingFrontier g) :
    Not (HnormalSymmetryBreakingClosed g) := by
  intro h
  rcases h.2.1 with hPT | hModular
  · exact hFrontier.2.2.1 hPT.2
  · exact hFrontier.2.2.2.1 hModular

end P0EFTJanusHnormalSymmetryBreakingCandidateMatrixGate
end JanusFormal
