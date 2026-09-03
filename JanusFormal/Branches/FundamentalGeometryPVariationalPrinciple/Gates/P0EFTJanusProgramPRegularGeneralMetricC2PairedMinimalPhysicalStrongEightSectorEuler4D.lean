import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEulerNineBlockDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D

/-! # Eight physical sectors of the authentic strong Euler equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D

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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEulerNineBlockDecomposition4D

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

/-- Algebraic covector underlying the authentic strong Euler one-form. -/
noncomputable def regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →ₗ[Real] Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point).toLinearMap

/-- Strong Euler covector transported to bulk and SpinC coordinates. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSectorEulerCovectorAt :=
  (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point).comp
    (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap

def regularGeneralMetricC2PairedMinimalPhysicalStrongBulkEulerCovectorAt :=
  productCovectorFirst
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSectorEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt :=
  productCovectorSecond
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSectorEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

/-- Bulk covector transported to its seven genuinely free field families. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt :=
  (regularGeneralMetricC2PairedMinimalPhysicalStrongBulkEulerCovectorAt period
    hPeriod configuration data analysis realization plusBase minusBase hBase
      measure point).comp
    (globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap

def regularGeneralMetricC2PairedMinimalPhysicalStrongMetricEulerCovectorAt :=
  productCovectorFirst
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt :=
  productCovectorFirst (productCovectorSecond
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point))

def regularGeneralMetricC2PairedMinimalPhysicalStrongNormalEulerCovectorAt :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)))

def regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostEulerCovectorAt :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point))))

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricEulerCovectorAt :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point)))))

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureEulerCovectorAt :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond (productCovectorSecond
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point))))))

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt :=
  productCovectorSecond (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond (productCovectorSecond
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point))))))

/-- Seven bulk equations plus the primitive SpinC matter equation. -/
def RegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEulerSystemAt :
    Prop :=
  (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongNormalEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ∧
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0) ∧
  regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point = 0

/-- Algebraically, the strong Euler covector vanishes exactly when its eight
physical sector restrictions vanish. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovector_eq_zero_iff_eightSectors :
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEulerSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point := by
  let euler :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point
  let sectorEquiv := globalMinimalPhysicalTangentSectorEquiv period hPeriod
    configuration.physical
  let sectors := euler.comp sectorEquiv.symm.toLinearMap
  let bulk := productCovectorFirst sectors
  let sevenEquiv := globalMinimalPhysicalSevenBulkEquiv period hPeriod
  let seven := bulk.comp sevenEquiv.symm.toLinearMap
  change euler = 0 ↔
    (productCovectorFirst seven = 0 ∧
      productCovectorFirst (productCovectorSecond seven) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond seven)) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond seven))) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond seven)))) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond
              (productCovectorSecond seven))))) = 0 ∧
      productCovectorSecond
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond
              (productCovectorSecond seven))))) = 0) ∧
    productCovectorSecond sectors = 0
  rw [← sevenBulkCovector_eq_zero_iff period hPeriod seven]
  rw [covector_comp_equiv_symm_eq_zero_iff sevenEquiv bulk]
  rw [← productCovector_eq_zero_iff sectors]
  exact (covector_comp_equiv_symm_eq_zero_iff sectorEquiv euler).symm

/-- The actual continuous strong Euler one-form vanishes exactly when the
eight physical component equations hold. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_eightSectors :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEulerSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovector_eq_zero_iff_eightSectors
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point]
  constructor
  · intro h
    simp [regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt,
      h]
  · intro h
    apply ContinuousLinearMap.ext
    intro direction
    have hApply := congrArg (fun covector => covector direction) h
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLinearCovectorAt]
      using hApply

/-- Gate marker: the authentic strong Euler equation is the exact eight-sector
physical system at every admissible point. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_eight_sector_euler_gate
    (_hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEulerSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point := by
  exact regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_eightSectors
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
end JanusFormal
