import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-! # Exact nine-block pairings for authentic strong component residuals -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEulerNineBlockDecomposition4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Pure seven-bulk direction in the authentic strong chart. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration).symm.toLinearMap.comp
    ((productFirstInclusion
        (GlobalMinimalPhysicalBulkTangent period hPeriod)
        (Sector → D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)).comp
      (globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap)

/-- Pure primitive SpinC direction in the authentic strong chart. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    (Sector → D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration).symm.toLinearMap.comp
    (productSecondInclusion
      (GlobalMinimalPhysicalBulkTangent period hPeriod)
      (Sector → D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter))

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (measure : Measure (EffectiveQuotient period hPeriod))
variable [IsFiniteMeasure measure]
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- The seven-bulk covector evaluates as the exact nine-block derivative on
its pure strong-chart direction. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_apply_eq_nineBlockSum
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (variation : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point variation =
      fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
          period hPeriod configuration.physical variation) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
        period hPeriod configuration.physical variation) = _
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint]

/-- Every pure restriction of the seven bulk coordinates inherits the same
exact formula. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_restrict_apply_eq_nineBlockSum
    {Component : Type*} [AddCommGroup Component] [Module Real Component]
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (inclusion : Component →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (variation : Component) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ((regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point).comp inclusion) variation =
      fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
          period hPeriod configuration.physical (inclusion variation)) :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_apply_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint (inclusion variation)

/-- The SpinC covector is likewise the exact nine-block derivative on pure
matter directions. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEuler_apply_eq_nineBlockSum
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point variation =
      fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical variation) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
        period hPeriod configuration.physical variation) = _
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint]

/-- Any separating bulk-component residual pairs with the derivative of the
same authentic action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongComponentBlockSum_eq_residualPairing
    {Component : Type*} [AddCommGroup Component] [Module Real Component]
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (componentCovector : Component →ₗ[Real] Real)
    (inclusion : Component →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (hRestriction : componentCovector =
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point).comp inclusion)
    (representation : SeparatingPDEResidualRepresentation componentCovector)
    (variation : Component) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
          period hPeriod configuration.physical (inclusion variation)) =
      representation.pairing representation.residual variation := by
  rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_restrict_apply_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint inclusion variation]
  rw [← hRestriction]
  exact representation.represents variation

/-- Any separating SpinC residual has the same exact action pairing. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCBlockSum_eq_residualPairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (representation : SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point))
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical variation) =
      representation.pairing representation.residual variation := by
  rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEuler_apply_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint variation]
  exact representation.represents variation

/-- Gate marker: both bulk and SpinC pure tests evaluate the authentic
nine-block Euler derivative. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_component_block_pairing_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (bulkVariation : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (spinCVariation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point bulkVariation =
      fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection
          period hPeriod configuration.physical bulkVariation) ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point spinCVariation =
      fullCoupledEulerBlockSum
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical spinCVariation) :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_apply_eq_nineBlockSum
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint bulkVariation,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEuler_apply_eq_nineBlockSum
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint spinCVariation⟩

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
end JanusFormal
