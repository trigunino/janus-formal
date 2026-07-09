namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWSourceRequirementGate

set_option autoImplicit false

structure FLRWSourceRequirementGate where
  sigmaOnlyActionAudited : Prop
  sigmaOnlyVariationEmitsZeroSource : Prop
  publishedJanusUsesBulkBimetricSource : Prop
  bulkBimetricStressDerived : Prop
  boundaryHamiltonianChargeNonzero : Prop
  admittedSigmaSurfaceDensityNonzero : Prop
  nullLLBridgeSourceProjected : Prop
  quantumTopologicalVacuumSourceDerived : Prop

def hasAdmittedFLRWSource (g : FLRWSourceRequirementGate) : Prop :=
  g.bulkBimetricStressDerived \/
  g.boundaryHamiltonianChargeNonzero \/
  g.admittedSigmaSurfaceDensityNonzero \/
  g.nullLLBridgeSourceProjected \/
  g.quantumTopologicalVacuumSourceDerived

theorem sigma_zero_requires_non_sigma_channel
    (g : FLRWSourceRequirementGate)
    (_hAudit : g.sigmaOnlyActionAudited)
    (_hZero : g.sigmaOnlyVariationEmitsZeroSource)
    (hNoBulk : Not g.bulkBimetricStressDerived)
    (hNoBoundary : Not g.boundaryHamiltonianChargeNonzero)
    (hNoSurface : Not g.admittedSigmaSurfaceDensityNonzero)
    (hNoLL : Not g.nullLLBridgeSourceProjected)
    (hNoQuantum : Not g.quantumTopologicalVacuumSourceDerived) :
    Not (hasAdmittedFLRWSource g) := by
  intro h
  rcases h with hBulk | hBoundary | hSurface | hLL | hQuantum
  · exact hNoBulk hBulk
  · exact hNoBoundary hBoundary
  · exact hNoSurface hSurface
  · exact hNoLL hLL
  · exact hNoQuantum hQuantum

theorem published_janus_pivot_is_bulk_not_sigma
    (g : FLRWSourceRequirementGate)
    (hPaper : g.publishedJanusUsesBulkBimetricSource)
    (hSigmaZero : g.sigmaOnlyVariationEmitsZeroSource) :
    g.publishedJanusUsesBulkBimetricSource /\ g.sigmaOnlyVariationEmitsZeroSource := by
  exact And.intro hPaper hSigmaZero

end P0EFTJanusZ2SigmaFLRWSourceRequirementGate
end JanusFormal
