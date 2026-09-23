import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! Concrete L2 bound for both strong Einstein--Hilbert metric derivatives. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongEinsteinHilbertL24D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open scoped BigOperators
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
open P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
open P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D

private def gravityMetric : Sector → RegularGeneralLorentzMetric period hPeriod
  | .plus => plusBase
  | .minus => minusBase

private def gravityCouplings : Sector → EinsteinHilbertCouplings
  | .plus => couplings.plusEinstein
  | .minus => couplings.minusEinstein

private theorem sum_sector (f : Sector → Real) : (∑ sector, f sector) = f .plus + f .minus := by
  have h : (Finset.univ : Finset Sector) = {.plus, .minus} := by
    ext sector
    cases sector <;> simp
  rw [h, Finset.sum_pair (by decide)]

def strongEinsteinHilbertCovector (normalization : SmoothGeneralLorentzMetric period hPeriod) :
    DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  pairedEinsteinHilbertCovector period hPeriod normalization
    (gravityMetric period hPeriod plusBase minusBase) (gravityCouplings (couplings := couplings))

/-- Sum of the two native strong derivatives evaluated on the physical metric direction. -/
def strongEinsteinHilbertMetricVariation
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) : Real :=
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
    period hPeriod configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod
      configuration.physical field.metricPerturbation) +
  regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
    period hPeriod configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod
      configuration.physical field.metricPerturbation)

theorem strongEinsteinHilbertMetricVariation_eq_covector
    (normalization : SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    strongEinsteinHilbertMetricVariation period hPeriod configuration data analysis realization
      plusBase minusBase field =
    strongEinsteinHilbertCovector period hPeriod plusBase minusBase normalization (couplings := couplings)
      (diffeomorphismL2Smooth period hPeriod normalization field) := by
  rw [strongEinsteinHilbertMetricVariation,
    pairedStrongEinsteinHilbertPlusDerivative_zero_eq_fixedVolume,
    pairedStrongEinsteinHilbertMinusDerivative_zero_eq_fixedVolume,
    strongEinsteinHilbertCovector, pairedEinsteinHilbertCovector_smooth, sum_sector]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem strongEinsteinHilbertMetricVariation_bound
    (normalization : SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖strongEinsteinHilbertMetricVariation period hPeriod configuration data analysis realization
      plusBase minusBase field‖ ≤
    ‖strongEinsteinHilbertCovector period hPeriod plusBase minusBase normalization (couplings := couplings)‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization field‖ := by
  rw [strongEinsteinHilbertMetricVariation_eq_covector, strongEinsteinHilbertCovector,
    pairedEinsteinHilbertCovector_smooth]
  exact pairedEinsteinHilbertDerivative_metric_bound period hPeriod normalization
    (gravityMetric period hPeriod plusBase minusBase) (gravityCouplings (couplings := couplings)) field

end
end P0EFTJanusProgramPT12StrongEinsteinHilbertL24D
end JanusFormal
