import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH01BalanceLaws
import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH02PTOnsagerCasimir
import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH03EntropyPositivity
import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH04MovingInterfaceRelaxation
import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH05QuantumEntropyBridge

namespace JanusFormal
namespace JanusSigmaThermodynamics

structure ProgramStatus where
  th01ConditionalBalances : Prop
  th02ConditionalPTParities : Prop
  th03ConditionalEntropyPositivity : Prop
  th04ConditionalMovingInterfaceRelaxation : Prop
  th05ConditionalQuantumEntropyBridge : Prop
  microscopicCurrentsDerivedFromP : Prop
  physicalStateLawDerivedFromP : Prop

def conditionalCoreClosed (s : ProgramStatus) : Prop :=
  s.th01ConditionalBalances ∧
  s.th02ConditionalPTParities ∧
  s.th03ConditionalEntropyPositivity ∧
  s.th04ConditionalMovingInterfaceRelaxation ∧
  s.th05ConditionalQuantumEntropyBridge

def physicalCoreClosed (s : ProgramStatus) : Prop :=
  conditionalCoreClosed s ∧
  s.microscopicCurrentsDerivedFromP ∧
  s.physicalStateLawDerivedFromP

end JanusSigmaThermodynamics
end JanusFormal
