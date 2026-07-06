namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermCoefficientParityFromOddDensityGate

set_option autoImplicit false

structure CoefficientParityFromOddDensityGate where
  variationalCoefficientFormulaReady : Prop
  hEven : Prop
  kOdd : Prop
  lCtZ2OddDensity : Prop
  rHAbOddCoefficientParity : Prop
  rKAbEvenCoefficientParity : Prop

def conditionalParityInputsReady
    (g : CoefficientParityFromOddDensityGate) : Prop :=
  g.variationalCoefficientFormulaReady /\ g.hEven /\ g.kOdd

def coefficientParityReady
    (g : CoefficientParityFromOddDensityGate) : Prop :=
  conditionalParityInputsReady g /\
  g.lCtZ2OddDensity /\
  g.rHAbOddCoefficientParity /\
  g.rKAbEvenCoefficientParity

theorem odd_density_gives_requested_coefficient_parities
    (g : CoefficientParityFromOddDensityGate)
    (hTransport :
      conditionalParityInputsReady g ->
      g.lCtZ2OddDensity ->
      g.rHAbOddCoefficientParity /\ g.rKAbEvenCoefficientParity)
    (hInputs : conditionalParityInputsReady g)
    (hOdd : g.lCtZ2OddDensity) :
    g.rHAbOddCoefficientParity /\ g.rKAbEvenCoefficientParity := by
  exact hTransport hInputs hOdd

theorem missing_lct_odd_density_blocks_coefficient_parity
    (g : CoefficientParityFromOddDensityGate)
    (hMissing : Not g.lCtZ2OddDensity) :
    Not (coefficientParityReady g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaCountertermCoefficientParityFromOddDensityGate
end JanusFormal
