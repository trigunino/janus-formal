import JanusFormal.P0EFTMatterVlasovBridgeAfterDS

namespace JanusFormal
namespace P0EFTEffectiveVlasovTransport

set_option autoImplicit false

structure EffectiveVlasovTransport where
  sheetHamiltonianDefined : Prop
  liouvilleOperatorDerived : Prop
  collisionlessVlasovPerSheet : Prop
  sameLBridgeExact : Prop
  phaseSpaceJacobianComputed : Prop
  measureTransportClosed : Prop

def vlasovPerSheetClosed (v : EffectiveVlasovTransport) : Prop :=
  v.sheetHamiltonianDefined /\
  v.liouvilleOperatorDerived /\
  v.collisionlessVlasovPerSheet

def bridgeMeasureClosed (v : EffectiveVlasovTransport) : Prop :=
  vlasovPerSheetClosed v /\
  v.sameLBridgeExact /\
  v.phaseSpaceJacobianComputed /\
  v.measureTransportClosed

theorem hamiltonian_liouville_give_vlasov_per_sheet
    (v : EffectiveVlasovTransport)
    (hH : v.sheetHamiltonianDefined)
    (hL : v.liouvilleOperatorDerived)
    (hV : v.collisionlessVlasovPerSheet) :
    vlasovPerSheetClosed v := by
  exact And.intro hH (And.intro hL hV)

theorem missing_sameL_bridge_blocks_measure_closure
    (v : EffectiveVlasovTransport)
    (hMissing : Not v.sameLBridgeExact) :
    Not (bridgeMeasureClosed v) := by
  intro h
  exact hMissing h.right.left

theorem sameL_jacobian_closes_measure_conditionally
    (v : EffectiveVlasovTransport)
    (hVlasov : vlasovPerSheetClosed v)
    (hBridge : v.sameLBridgeExact)
    (hJac : v.phaseSpaceJacobianComputed)
    (hMeasure : v.measureTransportClosed) :
    bridgeMeasureClosed v := by
  exact And.intro hVlasov (And.intro hBridge (And.intro hJac hMeasure))

end P0EFTEffectiveVlasovTransport
end JanusFormal
