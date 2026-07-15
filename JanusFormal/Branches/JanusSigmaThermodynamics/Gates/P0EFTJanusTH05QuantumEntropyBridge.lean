import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH04MovingInterfaceRelaxation

namespace JanusFormal
namespace P0EFTJanusTH05QuantumEntropyBridge

set_option autoImplicit false

/-- Mutual information from subsystem and total von Neumann entropies. -/
def mutualInformation (plusEntropy minusEntropy totalEntropy : ℝ) : ℝ :=
  plusEntropy + minusEntropy - totalEntropy

theorem pure_bipartite_mutual_information
    (reducedEntropy : ℝ) :
    mutualInformation reducedEntropy reducedEntropy 0 =
      2 * reducedEntropy := by
  unfold mutualInformation
  ring

/-- A closed classical exchange can conserve total entropy rate while either
sector has a nonzero rate. -/
theorem zero_total_exchange_does_not_force_zero_sector_rate
    (rate : ℝ) (hRate : rate ≠ 0) :
    rate + (-rate) = 0 ∧ rate ≠ 0 := by
  exact ⟨by ring, hRate⟩

/-- Reduced entropy is not by itself a thermodynamic production law. -/
structure QuantumThermodynamicBridgeInputs where
  globalDensityOperatorSpecified : Prop
  plusMinusObservableAlgebrasSpecified : Prop
  reducedStatesDerived : Prop
  coarseGrainingOrBathSpecified : Prop
  heatAndWorkSplitSpecified : Prop
  entropyProductionFunctionalDerived : Prop

def thermodynamicInterpretationReady
    (s : QuantumThermodynamicBridgeInputs) : Prop :=
  s.globalDensityOperatorSpecified ∧
  s.plusMinusObservableAlgebrasSpecified ∧
  s.reducedStatesDerived ∧
  s.coarseGrainingOrBathSpecified ∧
  s.heatAndWorkSplitSpecified ∧
  s.entropyProductionFunctionalDerived

theorem no_bath_or_coarse_graining_blocks_thermodynamic_interpretation
    (s : QuantumThermodynamicBridgeInputs)
    (hMissing : ¬s.coarseGrainingOrBathSpecified) :
    ¬thermodynamicInterpretationReady s := by
  intro hReady
  exact hMissing hReady.2.2.2.1

end P0EFTJanusTH05QuantumEntropyBridge
end JanusFormal
