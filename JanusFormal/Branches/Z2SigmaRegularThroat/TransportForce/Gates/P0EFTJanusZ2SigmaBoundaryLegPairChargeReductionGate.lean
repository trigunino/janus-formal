namespace JanusFormal
namespace P0EFTJanusZ2SigmaBoundaryLegPairChargeReductionGate

set_option autoImplicit false

structure BoundaryLegPairChargeReductionGate where
  plusLegEvaluated : Prop
  minusLegEvaluated : Prop
  oppositeNormalsVerified : Prop
  unitLapseVerified : Prop
  pt67RegularProjectionReady : Prop
  renormalizedUnitChargeZero : Prop
  absoluteMeasureAvailable : Prop
  nonzeroBoundaryStateAvailable : Prop
  noSingleLegShortcut : Prop
  noReferenceZeroAsSourceShortcut : Prop

def pairReductionReady
    (g : BoundaryLegPairChargeReductionGate) : Prop :=
  g.plusLegEvaluated /\
  g.minusLegEvaluated /\
  g.oppositeNormalsVerified /\
  g.unitLapseVerified /\
  g.pt67RegularProjectionReady /\
  g.noSingleLegShortcut /\
  g.noReferenceZeroAsSourceShortcut

theorem zero_unit_charge_blocks_nonzero_boundary_state
    (g : BoundaryLegPairChargeReductionGate)
    (_hReady : pairReductionReady g)
    (hZero : g.renormalizedUnitChargeZero)
    (hStateNeedsNonzero :
      g.nonzeroBoundaryStateAvailable -> Not g.renormalizedUnitChargeZero) :
    Not g.nonzeroBoundaryStateAvailable := by
  intro hState
  exact (hStateNeedsNonzero hState) hZero

theorem missing_absolute_measure_blocks_numeric_charge
    (g : BoundaryLegPairChargeReductionGate)
    (hMissing : Not g.absoluteMeasureAvailable)
    (hNumericNeedsMeasure :
      g.nonzeroBoundaryStateAvailable -> g.absoluteMeasureAvailable) :
    Not g.nonzeroBoundaryStateAvailable := by
  intro hState
  exact hMissing (hNumericNeedsMeasure hState)

end P0EFTJanusZ2SigmaBoundaryLegPairChargeReductionGate
end JanusFormal
