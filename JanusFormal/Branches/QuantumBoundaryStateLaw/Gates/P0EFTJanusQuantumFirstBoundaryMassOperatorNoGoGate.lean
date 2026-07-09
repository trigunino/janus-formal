import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstAlphaSpectrumGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstBoundaryMassOperatorNoGoGate

set_option autoImplicit false

structure QuantumFirstBoundaryMassOperatorNoGoGate where
  cp1PrequantizedLabelsAvailable : Prop
  cp1MomentMapAvailable : Prop
  cp1EnergyGeneratorSelected : Prop
  cp1DimensionfulEnergyUnitDerived : Prop
  tqftSectorsAvailable : Prop
  tqftBoundaryTimeGeneratorDerived : Prop
  tqftHamiltonianNonzeroDerived : Prop
  boundaryMassOperatorDerived : Prop

def cp1MassOperatorReady (g : QuantumFirstBoundaryMassOperatorNoGoGate) : Prop :=
  g.cp1PrequantizedLabelsAvailable /\
  g.cp1MomentMapAvailable /\
  g.cp1EnergyGeneratorSelected /\
  g.cp1DimensionfulEnergyUnitDerived

def tqftMassOperatorReady (g : QuantumFirstBoundaryMassOperatorNoGoGate) : Prop :=
  g.tqftSectorsAvailable /\
  g.tqftBoundaryTimeGeneratorDerived /\
  g.tqftHamiltonianNonzeroDerived

def anyBoundaryMassOperatorReady (g : QuantumFirstBoundaryMassOperatorNoGoGate) : Prop :=
  (cp1MassOperatorReady g \/ tqftMassOperatorReady g) /\ g.boundaryMassOperatorDerived

theorem missing_energy_unit_blocks_cp1_mass
    (g : QuantumFirstBoundaryMassOperatorNoGoGate)
    (hMissing : Not g.cp1DimensionfulEnergyUnitDerived) :
    Not (cp1MassOperatorReady g) := by
  intro h
  exact hMissing h.right.right.right

theorem topological_tqft_without_time_generator_blocks_mass
    (g : QuantumFirstBoundaryMassOperatorNoGoGate)
    (hMissing : Not g.tqftBoundaryTimeGeneratorDerived) :
    Not (tqftMassOperatorReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusQuantumFirstBoundaryMassOperatorNoGoGate
end JanusFormal
