import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongEinsteinBRSTHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHessianL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongEinsteinActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongEinsteinBRSTL24D

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

open P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D
open P0EFTJanusProgramPT12StrongEinsteinActionHessian4D

open P0EFTJanusProgramPT12StrongEinsteinBRSTHessian4D
open P0EFTJanusProgramPT12PairedEinsteinHessianL24D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open scoped BigOperators

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

/-- Actual gravity BRST Hessian column, represented by a bounded L2 covector. -/
def strongEinsteinBRSTHessianCovector (normalization : SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  pairedEinsteinHessianCovector period hPeriod normalization
    (gravityMetric period hPeriod plusBase minusBase) (gravityCouplings (couplings := couplings)) field

variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
  (normalization : SmoothGeneralLorentzMetric period hPeriod)
  (field test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)

theorem strongEinsteinBRSTHessian_eq_covector :
    strongEinsteinPlusBRSTHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test +
    strongEinsteinMinusBRSTHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test =
    strongEinsteinBRSTHessianCovector period hPeriod plusBase minusBase normalization field (couplings := couplings)
      (diffeomorphismL2Smooth period hPeriod normalization test) := by
  rw [strongEinsteinPlusBRSTHessian_eq_native, strongEinsteinMinusBRSTHessian_eq_native,
    strongEinsteinBRSTHessianCovector, pairedEinsteinHessianCovector_smooth, sum_sector]
  rfl

theorem strongEinsteinBRSTHessian_metric_bound :
    ‖strongEinsteinPlusBRSTHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test +
    strongEinsteinMinusBRSTHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase field test‖ ≤
    ‖strongEinsteinBRSTHessianCovector period hPeriod plusBase minusBase normalization field (couplings := couplings)‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization test‖ := by
  rw [strongEinsteinBRSTHessian_eq_covector, strongEinsteinBRSTHessianCovector,
    pairedEinsteinHessianCovector_smooth]
  exact pairedEinsteinHessian_metric_bound period hPeriod normalization
    (gravityMetric period hPeriod plusBase minusBase) (gravityCouplings (couplings := couplings)) field test

end
end P0EFTJanusProgramPT12StrongEinsteinBRSTL24D
end JanusFormal
