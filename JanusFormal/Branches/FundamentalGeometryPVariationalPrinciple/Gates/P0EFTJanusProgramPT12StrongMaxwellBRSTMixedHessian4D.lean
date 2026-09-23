import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongMaxwellBRSTMixedHessian4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open P0EFTJanusProgramPT12ProjectedGradientDerivative4D
open P0EFTJanusProgramPT12PairedMaxwellCenterC24D
open P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D
open P0EFTJanusProgramPT12StrongMaxwellActionHessian4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

/-- Preserve the coefficient packet when the physical and Maxwell frames differ. -/
def maxwellGaugeRebase (base source : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothAbelianGaugePotential period hPeriod) : SmoothAbelianGaugePotential period hPeriod :=
  regularFrameGaugePotentialFromCoefficients period hPeriod base
    (gaugePotentialFrameCoefficients period hPeriod source direction)

theorem maxwellGaugeRebase_c2 (base source : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothAbelianGaugePotential period hPeriod) :
    maxwellSmoothGaugeC2 period hPeriod base (maxwellGaugeRebase period hPeriod base source direction) =
    maxwellSmoothGaugeC2 period hPeriod source direction :=
  maxwellSmoothGaugeC2_reconstructed period hPeriod base
    (gaugePotentialFrameCoefficients period hPeriod source direction)

attribute [local irreducible] nativeMobileMaxwellHessian maxwellSmoothGaugeC2
  pairedMaxwellPlusProjection pairedMaxwellMinusProjection

variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
  (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
  (test : GlobalPairedAbelianBRSTState period hPeriod)
def strongMaxwellPlusMixedHessian : Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact fderiv Real (actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).maxwellPlus) 0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis field))
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis test))

theorem strongMaxwellPlusMixedHessian_eq_native :
    strongMaxwellPlusMixedHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test =
    couplings.plusMaxwellScale * nativeMobileMaxwellHessian period hPeriod plusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase configuration.physical.coefficientFields.gauge.1)
      (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (field.metricPerturbation .plus), 0)
      (0, maxwellSmoothGaugeC2 period hPeriod plusBase
        (maxwellGaugeRebase period hPeriod plusBase data.plusGravity.metric (test.potential .plus))) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have h := strongMaxwellPlusActionHessian_eq_native period hPeriod configuration data analysis realization
    plusBase minusBase hBase
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis field))
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis test))
  simp only [globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM_apply,
    pairedPlusProjection_diffeomorphismCore, pairedPlusProjection_abelianCore] at h
  exact h.trans (by rw [maxwellGaugeRebase_c2])
def strongMaxwellMinusMixedHessian : Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact fderiv Real (actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).maxwellMinus) 0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis field))
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis test))

theorem strongMaxwellMinusMixedHessian_eq_native :
    strongMaxwellMinusMixedHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test =
    couplings.minusMaxwellScale * nativeMobileMaxwellHessian period hPeriod minusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase configuration.physical.coefficientFields.gauge.2)
      (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (field.metricPerturbation .minus), 0)
      (0, maxwellSmoothGaugeC2 period hPeriod minusBase
        (maxwellGaugeRebase period hPeriod minusBase data.minusGravity.metric (test.potential .minus))) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have h := strongMaxwellMinusActionHessian_eq_native period hPeriod configuration data analysis realization
    plusBase minusBase hBase
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis field))
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis test))
  simp only [globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM_apply,
    pairedMinusProjection_diffeomorphismCore, pairedMinusProjection_abelianCore] at h
  exact h.trans (by rw [maxwellGaugeRebase_c2])

end
end P0EFTJanusProgramPT12StrongMaxwellBRSTMixedHessian4D
end JanusFormal
