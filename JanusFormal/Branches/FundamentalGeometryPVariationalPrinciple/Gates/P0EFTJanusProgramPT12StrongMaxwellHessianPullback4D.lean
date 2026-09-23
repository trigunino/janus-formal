import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProjectedGradientDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedMaxwellCenterC24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricEinsteinHilbertTotalEuler4D

/-! Exact native Hessians of the actual strong Maxwell gradients. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongMaxwellHessianPullback4D

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

attribute [local irreducible] nativeMobileMaxwellHessian
  pairedMaxwellPlusProjection pairedMaxwellMinusProjection
  regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
  regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
  canonicalPhysicalScalarC2JetCoreSubmodule
  P0EFTJanusProgramPGeneralMetricC2OpenDomain4D.generalMetricRelativeC2CoreSubmodule

theorem strongMaxwellPlusDerivative_fderiv
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) 0 first second =
    couplings.plusMaxwellScale * nativeMobileMaxwellHessian period hPeriod plusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase configuration.physical.coefficientFields.gauge.1)
      (pairedMaxwellPlusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
          period hPeriod configuration data analysis realization plusBase minusBase first))
      (pairedMaxwellPlusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
          period hPeriod configuration data analysis realization plusBase minusBase second)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hSecond := ((pairedPlusScaledMaxwellAction_contDiffAt_zero period hPeriod
    configuration.physical plusBase minusBase couplings.plusMaxwellScale).fderiv_right
      (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hPull := projectedGradient_fderiv
    (fun core => couplings.plusMaxwellScale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration.physical plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core)
    (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
      period hPeriod configuration data analysis realization plusBase minusBase) hSecond first second
  exact hPull.trans (pairedPlusMaxwellHessian_eq_native period hPeriod configuration.physical
    plusBase minusBase couplings.plusMaxwellScale _ _)
theorem strongMaxwellMinusDerivative_fderiv
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) 0 first second =
    couplings.minusMaxwellScale * nativeMobileMaxwellHessian period hPeriod minusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase configuration.physical.coefficientFields.gauge.2)
      (pairedMaxwellMinusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
          period hPeriod configuration data analysis realization plusBase minusBase first))
      (pairedMaxwellMinusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
          period hPeriod configuration data analysis realization plusBase minusBase second)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hSecond := ((pairedMinusScaledMaxwellAction_contDiffAt_zero period hPeriod
    configuration.physical plusBase minusBase couplings.minusMaxwellScale).fderiv_right
      (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hPull := projectedGradient_fderiv
    (fun core => couplings.minusMaxwellScale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration.physical plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core)
    (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
      period hPeriod configuration data analysis realization plusBase minusBase) hSecond first second
  exact hPull.trans (pairedMinusMaxwellHessian_eq_native period hPeriod configuration.physical
    plusBase minusBase couplings.minusMaxwellScale _ _)

end
end P0EFTJanusProgramPT12StrongMaxwellHessianPullback4D
end JanusFormal
