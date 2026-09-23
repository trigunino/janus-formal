import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongEinsteinHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProjectedGradientDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricEinsteinHilbertTotalEuler4D

/-! Exact native Hessians of the actual strong Einstein--Hilbert gradients. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongEinsteinActionHessian4D

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
open P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
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

attribute [local irreducible] nativeEinsteinHilbertHessian
  pairedEinsteinPlusProjection pairedEinsteinMinusProjection
  regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
  regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
  canonicalPhysicalScalarC2JetCoreSubmodule
  P0EFTJanusProgramPGeneralMetricC2OpenDomain4D.generalMetricRelativeC2CoreSubmodule

open P0EFTJanusProgramPT12StrongEinsteinHessianPullback4D

variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)

theorem strongEinsteinPlusGradient_eventually :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).einsteinHilbertPlus =ᶠ[𝓝 0]
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hNear := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
    period hPeriod configuration data analysis realization plusBase minusBase).mem_nhds
      (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration.physical plusBase minusBase hBase)
  filter_upwards [hNear] with point hPoint
  exact (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint).fderiv
theorem strongEinsteinPlusActionHessian_eq_native
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).einsteinHilbertPlus) 0 first second =
    nativeEinsteinHilbertHessian period hPeriod plusBase couplings.plusEinstein
      (pairedEinsteinPlusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
          period hPeriod configuration data analysis realization plusBase minusBase first))
      (pairedEinsteinPlusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
          period hPeriod configuration data analysis realization plusBase minusBase second)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hEq := strongEinsteinPlusGradient_eventually period hPeriod configuration data analysis realization
    plusBase minusBase hBase
  exact (congrArg (fun derivative : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →L[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →L[Real] Real =>
        derivative first second) (hEq.fderiv_eq (𝕜 := Real))).trans
    (strongEinsteinPlusDerivative_fderiv period hPeriod configuration data analysis realization
      plusBase minusBase first second)
theorem strongEinsteinMinusGradient_eventually :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).einsteinHilbertMinus =ᶠ[𝓝 0]
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hNear := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
    period hPeriod configuration data analysis realization plusBase minusBase).mem_nhds
      (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration.physical plusBase minusBase hBase)
  filter_upwards [hNear] with point hPoint
  exact (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint).fderiv
theorem strongEinsteinMinusActionHessian_eq_native
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (actionGradient (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).einsteinHilbertMinus) 0 first second =
    nativeEinsteinHilbertHessian period hPeriod minusBase couplings.minusEinstein
      (pairedEinsteinMinusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
          period hPeriod configuration data analysis realization plusBase minusBase first))
      (pairedEinsteinMinusProjection period hPeriod plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
          period hPeriod configuration data analysis realization plusBase minusBase second)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hEq := strongEinsteinMinusGradient_eventually period hPeriod configuration data analysis realization
    plusBase minusBase hBase
  exact (congrArg (fun derivative : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →L[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →L[Real] Real =>
        derivative first second) (hEq.fderiv_eq (𝕜 := Real))).trans
    (strongEinsteinMinusDerivative_fderiv period hPeriod configuration data analysis realization
      plusBase minusBase first second)

end
end P0EFTJanusProgramPT12StrongEinsteinActionHessian4D
end JanusFormal
