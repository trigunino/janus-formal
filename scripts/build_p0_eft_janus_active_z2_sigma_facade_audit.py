from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_active_z2_sigma_facade_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_active_z2_sigma_facade_audit.json")

ALLOWED_IMPORTS = {
    "JanusFormal.Basic",
    "JanusFormal.P0EFTJanusTopologyLayerAlignmentGate",
    "JanusFormal.P0EFTJanusProjectiveTunnelInterface",
    "JanusFormal.P0EFTJanusFormalModelReauditAfterTopologyCorrectionGate",
    "JanusFormal.P0EFTJanusZ2TunnelCoreGate",
    "JanusFormal.P0EFTJanusLegacyZ4ArchivePolicyGate",
    "JanusFormal.P0EFTJanusRP4PinSignComputationGate",
    "JanusFormal.P0EFTJanusSigmaAPSPinLiftObligationGate",
    "JanusFormal.P0EFTJanusSigmaAPSLocalThroatModelGate",
    "JanusFormal.P0EFTJanusSigmaAPSEtaCancellationGate",
    "JanusFormal.P0EFTJanusSigmaAPSParityAnomalyCancellationGate",
    "JanusFormal.P0EFTJanusSigmaAPSTraceRegularizationGate",
    "JanusFormal.P0EFTJanusRP4PinSignAuditGate",
    "JanusFormal.P0EFTJanusAroundSigmaZ2CycleTransportGate",
    "JanusFormal.P0EFTJanusProjectiveTunnelCoverSurvivalGate",
    "JanusFormal.P0EFTJanusProjectiveTunnelVolumeRatioGate",
    "JanusFormal.P0EFTJanusProjectiveTunnelCoverRatioGate",
    "JanusFormal.P0EFTJanusSigmaBoundaryActionSupportGate",
    "JanusFormal.P0EFTJanusSigmaBoundaryVariationalDecompositionGate",
    "JanusFormal.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaPureMathClosureAuditGate",
    "JanusFormal.P0EFTJanusZ2SigmaHardTheoremTargetRegistry",
    "JanusFormal.P0EFTJanusZ2SigmaObservationalRoadmapGate",
    "JanusFormal.P0EFTJanusZ2SigmaBackgroundBibliographyGate",
    "JanusFormal.P0EFTJanusZ2SigmaBoundaryStressExtractionGate",
    "JanusFormal.P0EFTJanusZ2SigmaThroatRadiusLawGate",
    "JanusFormal.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate",
    "JanusFormal.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate",
    "JanusFormal.P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate",
    "JanusFormal.P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate",
    "JanusFormal.P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate",
    "JanusFormal.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate",
    "JanusFormal.P0EFTJanusZ2SigmaCartanGHYRadialBlockGate",
    "JanusFormal.P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxFrontierGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxTransparencyReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxTraceRegularityGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate",
    "JanusFormal.P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate",
    "JanusFormal.P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate",
    "JanusFormal.P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate",
    "JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate",
    "JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate",
    "JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate",
    "JanusFormal.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate",
    "JanusFormal.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate",
    "JanusFormal.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate",
    "JanusFormal.P0EFTJanusZ2SigmaSpinorBundleProjectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaSpinorProjectionReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectedDiracActionReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate",
    "JanusFormal.P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate",
    "JanusFormal.P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate",
    "JanusFormal.P0EFTJanusZ2SigmaNormalMatterCurrentGate",
    "JanusFormal.P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxTransparencyGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaBulkStressOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaSectorDensityPressureOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate",
    "JanusFormal.P0EFTJanusZ2SigmaImmirziProfileOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaHolstTorsionStressOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaFermionRouteSelectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracNumberNormalizationGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracHolstVertexOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracInteractionRateOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracDecouplingConditionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracRegimeSelectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracMassTermFromActionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracScalarMassLawGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracDegeneracyFactorGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaFermionDistributionOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate",
    "JanusFormal.P0EFTJanusZ2SigmaFLRWMomentumFrameGate",
    "JanusFormal.P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate",
    "JanusFormal.P0EFTJanusZ2SigmaRadialOccupationProjectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate",
    "JanusFormal.P0EFTJanusZ2SigmaKineticMomentFluidClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaSpinCurrentOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermRadialBlockGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate",
    "JanusFormal.P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate",
    "JanusFormal.P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate",
    "JanusFormal.P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate",
    "JanusFormal.P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermResidualExtractionGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermDensityExpansionGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate",
    "JanusFormal.P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate",
    "JanusFormal.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate",
    "JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate",
    "JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate",
    "JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate",
    "JanusFormal.P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate",
    "JanusFormal.P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate",
    "JanusFormal.P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate",
    "JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate",
    "JanusFormal.P0EFTJanusZ2SigmaCountertermFLRWObligationGate",
    "JanusFormal.P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGate",
    "JanusFormal.P0EFTJanusZ2SigmaProjectedStressTensorGate",
    "JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionConditionGate",
    "JanusFormal.P0EFTJanusZ2SigmaEffectiveFluidClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaBackgroundEquationDerivationGate",
    "JanusFormal.P0EFTJanusZ2SigmaNumericalBackgroundClosureGate",
    "JanusFormal.P0EFTJanusZ2SigmaDistanceBAOBibliographyGate",
    "JanusFormal.P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate",
    "JanusFormal.P0EFTJanusZ2SigmaBAOSoundRulerGate",
    "JanusFormal.P0EFTJanusZ2SigmaBAONonCompressedObservationGate",
    "JanusFormal.P0EFTJanusZ2SigmaGrowthBibliographyGate",
    "JanusFormal.P0EFTJanusZ2SigmaGrowthPerturbationEquationGate",
    "JanusFormal.P0EFTJanusZ2SigmaGrowthPredictionVectorGate",
    "JanusFormal.P0EFTJanusZ2SigmaGrowthNonCompressedObservationGate",
    "JanusFormal.P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate",
    "JanusFormal.P0EFTJanusZ2SigmaCMBBoltzmannEquationGate",
    "JanusFormal.P0EFTJanusZ2SigmaCMBNonCompressedObservationGate",
    "JanusFormal.P0EFTJanusZ2SigmaNonCompressedObservationGate",
}


def _imports() -> list[str]:
    return [
        line.removeprefix("import ").strip()
        for line in ROOT_PATH.read_text(encoding="utf-8").splitlines()
        if line.startswith("import ")
    ]


def build_payload() -> dict:
    imports = _imports()
    unexpected = [item for item in imports if item not in ALLOWED_IMPORTS]
    forbidden_active_z4 = [
        item
        for item in imports
        if "Z4" in item and item != "JanusFormal.P0EFTJanusLegacyZ4ArchivePolicyGate"
    ]
    allowed_cmb_boltzmann = {
        "JanusFormal.P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate",
        "JanusFormal.P0EFTJanusZ2SigmaCMBBoltzmannEquationGate",
        "JanusFormal.P0EFTJanusZ2SigmaCMBNonCompressedObservationGate",
    }
    forbidden_cmb_planck = [
        item
        for item in imports
        if any(token in item for token in ("CMB", "Planck", "Boltzmann"))
        and item not in allowed_cmb_boltzmann
    ]
    return {
        "status": "janus-active-z2-sigma-facade-audit",
        "root": str(ROOT_PATH),
        "imports": imports,
        "unexpected_imports": unexpected,
        "forbidden_active_z4_imports": forbidden_active_z4,
        "forbidden_cmb_planck_imports": forbidden_cmb_planck,
        "active_facade_z2_sigma_only": not unexpected and not forbidden_active_z4 and not forbidden_cmb_planck,
        "legacy_z4_archive_policy_imported": "JanusFormal.P0EFTJanusLegacyZ4ArchivePolicyGate" in imports,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Active Z2/Sigma Facade Audit",
        "",
        f"Active facade Z2/Sigma only: `{payload['active_facade_z2_sigma_only']}`",
        f"Legacy Z4 archive policy imported: `{payload['legacy_z4_archive_policy_imported']}`",
        f"Unexpected imports: `{payload['unexpected_imports']}`",
        f"Forbidden active Z4 imports: `{payload['forbidden_active_z4_imports']}`",
        f"Forbidden CMB/Planck imports: `{payload['forbidden_cmb_planck_imports']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
