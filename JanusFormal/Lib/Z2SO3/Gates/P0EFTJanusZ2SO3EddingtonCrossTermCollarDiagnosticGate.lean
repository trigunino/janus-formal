namespace JanusFormal
namespace P0EFTJanusZ2SO3EddingtonCrossTermCollarDiagnosticGate

set_option autoImplicit false

structure SO3EddingtonCrossTermCollarDiagnosticGate where
  crossTermMetricBlockDeclared : Prop
  bulkTRBlockRegularAtRs : Prop
  rConstThroatInducedMetricNull : Prop
  evenRadiusFoldCoordinateDegeneratesAtSigma : Prop
  currentRegularSigmaHKCompatible : Prop
  nullSigmaFormalismRequiredIfBridgeActive : Prop

def eddingtonBridgeDiagnosticReady
    (g : SO3EddingtonCrossTermCollarDiagnosticGate) : Prop :=
  g.crossTermMetricBlockDeclared /\
  g.bulkTRBlockRegularAtRs /\
  g.rConstThroatInducedMetricNull /\
  g.evenRadiusFoldCoordinateDegeneratesAtSigma

theorem cross_term_bulk_regular_does_not_imply_regular_sigma_hK
    (g : SO3EddingtonCrossTermCollarDiagnosticGate)
    (_h : eddingtonBridgeDiagnosticReady g)
    (hNoHK : Not g.currentRegularSigmaHKCompatible) :
    Not g.currentRegularSigmaHKCompatible := by
  exact hNoHK

theorem null_sigma_route_required_for_active_bridge
    (g : SO3EddingtonCrossTermCollarDiagnosticGate)
    (_hNoHK : Not g.currentRegularSigmaHKCompatible)
    (hNull : g.nullSigmaFormalismRequiredIfBridgeActive) :
    g.nullSigmaFormalismRequiredIfBridgeActive := by
  exact hNull

end P0EFTJanusZ2SO3EddingtonCrossTermCollarDiagnosticGate
end JanusFormal
