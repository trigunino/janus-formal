import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTEffectiveVlasovTransport

namespace JanusFormal
namespace P0EFTSameLPhaseSpaceBridge

set_option autoImplicit false

structure SameLPhaseSpaceBridge where
  configurationMapFromSoldering : Prop
  cotangentLiftDefined : Prop
  sameLHamiltonianPreserved : Prop
  liouvilleJacobianOne : Prop
  massShellMeasureClosed : Prop
  activeB4volMeasureClosed : Prop

def liouvilleBridgeClosed (b : SameLPhaseSpaceBridge) : Prop :=
  b.configurationMapFromSoldering /\
  b.cotangentLiftDefined /\
  b.sameLHamiltonianPreserved /\
  b.liouvilleJacobianOne

def activeMatterMeasureClosed (b : SameLPhaseSpaceBridge) : Prop :=
  liouvilleBridgeClosed b /\
  b.massShellMeasureClosed /\
  b.activeB4volMeasureClosed

theorem cotangent_lift_closes_liouville_bridge
    (b : SameLPhaseSpaceBridge)
    (hPhi : b.configurationMapFromSoldering)
    (hLift : b.cotangentLiftDefined)
    (hSameL : b.sameLHamiltonianPreserved)
    (hJac : b.liouvilleJacobianOne) :
    liouvilleBridgeClosed b := by
  exact And.intro hPhi (And.intro hLift (And.intro hSameL hJac))

theorem missing_b4vol_blocks_active_measure
    (b : SameLPhaseSpaceBridge)
    (hMissing : Not b.activeB4volMeasureClosed) :
    Not (activeMatterMeasureClosed b) := by
  intro h
  exact hMissing h.right.right

end P0EFTSameLPhaseSpaceBridge
end JanusFormal
