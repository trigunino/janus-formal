import JanusFormal.P0EFTDSVectorBoundaryGhostAudit

namespace JanusFormal
namespace P0EFTMatterVlasovBridgeAfterDS

set_option autoImplicit false

structure MatterVlasovBridge where
  dsBoundaryInputsAvailable : Prop
  matterBridgeDefined : Prop
  vlasovEquationDerived : Prop
  phaseSpaceMeasureClosed : Prop
  stressTensorMomentsClosed : Prop
  lensingGrowthSourcesClosed : Prop

def matterPipelineStarted (m : MatterVlasovBridge) : Prop :=
  m.dsBoundaryInputsAvailable /\ m.matterBridgeDefined

def matterPipelineClosed (m : MatterVlasovBridge) : Prop :=
  matterPipelineStarted m /\
  m.vlasovEquationDerived /\
  m.phaseSpaceMeasureClosed /\
  m.stressTensorMomentsClosed /\
  m.lensingGrowthSourcesClosed

theorem ds_boundary_inputs_start_matter_pipeline
    (m : MatterVlasovBridge)
    (hDS : m.dsBoundaryInputsAvailable)
    (hBridge : m.matterBridgeDefined) :
    matterPipelineStarted m := by
  exact And.intro hDS hBridge

theorem missing_vlasov_blocks_matter_closure
    (m : MatterVlasovBridge)
    (hMissing : Not m.vlasovEquationDerived) :
    Not (matterPipelineClosed m) := by
  intro h
  exact hMissing h.right.left

theorem missing_measure_blocks_matter_closure
    (m : MatterVlasovBridge)
    (hMissing : Not m.phaseSpaceMeasureClosed) :
    Not (matterPipelineClosed m) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTMatterVlasovBridgeAfterDS
end JanusFormal
