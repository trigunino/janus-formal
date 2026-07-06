namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradComponentParityGate

set_option autoImplicit false

structure TetradComponentParityGate where
  metricVariationEven : Prop
  extrinsicVariationOdd : Prop
  rHAbOddCoefficientParity : Prop
  rKAbEvenCoefficientParity : Prop
  metricTetradComponentOdd : Prop
  extrinsicTetradComponentOdd : Prop

def tetradComponentParityReady (g : TetradComponentParityGate) : Prop :=
  g.metricVariationEven /\
  g.extrinsicVariationOdd /\
  g.rHAbOddCoefficientParity /\
  g.rKAbEvenCoefficientParity /\
  g.metricTetradComponentOdd /\
  g.extrinsicTetradComponentOdd

theorem metric_component_requires_rh_odd
    (g : TetradComponentParityGate)
    (hReady : tetradComponentParityReady g) :
    g.rHAbOddCoefficientParity := by
  exact hReady.2.2.1

theorem extrinsic_component_requires_rk_even
    (g : TetradComponentParityGate)
    (hReady : tetradComponentParityReady g) :
    g.rKAbEvenCoefficientParity := by
  exact hReady.2.2.2.1

theorem missing_rh_parity_blocks_tetrad_component_parity
    (g : TetradComponentParityGate)
    (hMissing : Not g.rHAbOddCoefficientParity) :
    Not (tetradComponentParityReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

theorem missing_rk_parity_blocks_tetrad_component_parity
    (g : TetradComponentParityGate)
    (hMissing : Not g.rKAbEvenCoefficientParity) :
    Not (tetradComponentParityReady g) := by
  intro hReady
  exact hMissing hReady.2.2.2.1

end P0EFTJanusZ2SigmaCountertermTetradComponentParityGate
end JanusFormal
