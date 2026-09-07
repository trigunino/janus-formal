import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongAbelianGaugeFixedAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D

/-! # Full BRST action on the original strong physical model

The existing strong Abelian gauge-fixed model and domain are retained. One
independent total diffeomorphism nonminimal triple is added in a common source
frame. Its metric pair is the bounded projection of the original physical
coordinates, so no second metric variable or rebuilt strong chart is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongFullBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusPairedMobileAbelianBRSTAction4D
open P0EFTJanusPairedStrongAbelianGaugeFixedAction4D
open P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
    period hPeriod plusBase minusBase)
  (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]

local notation "AbelianCore" => PairedStrongAbelianGaugeFixedCore period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure
local notation "AbelianDomain" => pairedStrongAbelianGaugeFixedDomain period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

/-- The original strong model, with one independent total B/antighost/ghost triple. -/
abbrev PairedStrongFullBRSTCore := AbelianCore × DiffeomorphismNonminimalC2Core period hPeriod

local notation "Core" => PairedStrongFullBRSTCore period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

def pairedStrongFullAbelianProjection : Core →L[Real] AbelianCore :=
  ContinuousLinearMap.fst Real _ _

local notation "projectAbelian" => pairedStrongFullAbelianProjection period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

/-- Three old-core projections recover the existing metric pair before adjoining the new fields. -/
def pairedStrongFullDiffeomorphismProjection :
    Core →L[Real] PairedMobileDiffeomorphismBRSTCore period hPeriod plusBase minusBase := by
  let oldProjection : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase →L[Real]
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase :=
    ContinuousLinearMap.fst Real _ _
  let relativeProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase :=
    ContinuousLinearMap.fst Real _ _
  let pairProjection :
      RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2PairedCore period hPeriod plusBase minusBase :=
    ContinuousLinearMap.fst Real _ _
  let metricProjection := pairProjection.comp (relativeProjection.comp (oldProjection.comp
    (pairedStrongAbelianBRSTProjection period hPeriod configuration data analysis realization
      plusBase minusBase hBase measure)))
  exact (metricProjection.comp projectAbelian).prod (ContinuousLinearMap.snd Real _ _)

local notation "projectDiffeomorphism" => pairedStrongFullDiffeomorphismProjection period hPeriod
  configuration data analysis realization plusBase minusBase hBase measure

@[simp] theorem pairedStrongFullAbelianProjection_apply (input : Core) :
    projectAbelian input = input.1 := rfl

@[simp] theorem pairedStrongFullDiffeomorphismProjection_apply (input : Core) :
    projectDiffeomorphism input =
      ((pairedStrongAbelianBRSTProjection period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure input.1).1.1.1, input.2) := rfl

def pairedStrongFullBRSTDomain : Set Core := AbelianDomain ×ˢ univ

local notation "Domain" => pairedStrongFullBRSTDomain period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

theorem pairedStrongFullBRSTDomain_isOpen : IsOpen Domain :=
  (pairedStrongAbelianGaugeFixedDomain_isOpen period hPeriod configuration data analysis
    realization plusBase minusBase hBase measure).prod isOpen_univ

theorem pairedStrongFullBRSTDomain_zero_mem : (0 : Core) ∈ Domain :=
  ⟨pairedStrongAbelianGaugeFixedDomain_zero_mem period hPeriod configuration data analysis
    realization plusBase minusBase hBase measure, mem_univ _⟩

theorem pairedStrongFullDiffeomorphismProjection_mem
    {input : Core} (hInput : input ∈ Domain) :
    projectDiffeomorphism input ∈
      pairedMobileDiffeomorphismBRSTDomain period hPeriod plusBase minusBase := by
  have h := pairedStrongAbelianBRSTProjection_mem period hPeriod configuration data analysis
    realization plusBase minusBase hBase measure hInput.1
  rw [pairedStrongFullDiffeomorphismProjection_apply]
  exact ⟨⟨h.1.1.1.1.1, h.1.1.1.2.1⟩, mem_univ _⟩

variable (source : RegularGeneralLorentzMetric period hPeriod)

/-- The existing physical/Abelian action plus the metric-dependent diagonal diffeomorphism action. -/
def pairedStrongFullBRSTAction (input : Core) : Real :=
  pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis realization
      plusBase minusBase hBase measure (projectAbelian input) +
    pairedMobileDiffeomorphismBRSTAction period hPeriod source plusBase minusBase couplings
      (projectDiffeomorphism input)

theorem pairedStrongFullBRSTAction_contDiffAt_two (input : Core) (hInput : input ∈ Domain) :
    ContDiffAt Real 2
      (pairedStrongFullBRSTAction period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure source) input := by
  have hAbelian := (pairedStrongAbelianGaugeFixedAction_contDiffAt_two period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    (projectAbelian input) hInput.1).comp input (projectAbelian).contDiff.contDiffAt
  have hMapped := pairedStrongFullDiffeomorphismProjection_mem period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure hInput
  have hDiffeomorphism :=
    ((pairedMobileDiffeomorphismBRSTAction_contDiffOn_two period hPeriod source plusBase minusBase
      couplings (projectDiffeomorphism input) hMapped).contDiffAt
        ((pairedMobileDiffeomorphismBRSTDomain_isOpen period hPeriod plusBase minusBase).mem_nhds
          hMapped)).comp input (projectDiffeomorphism).contDiff.contDiffAt
  have hResult := hAbelian.add hDiffeomorphism
  simp only [Function.comp_def] at hResult
  exact hResult

/-- Retain the established Euler term and add the actual mobile diffeomorphism derivative. -/
def pairedStrongFullBRSTEulerOperator (input : Core) : Core →L[Real] Real :=
  (pairedStrongAbelianGaugeFixedEulerOperator period hPeriod configuration data analysis realization
    plusBase minusBase hBase measure (projectAbelian input)).comp projectAbelian +
    (fderiv Real
      (pairedMobileDiffeomorphismBRSTAction period hPeriod source plusBase minusBase couplings)
      (projectDiffeomorphism input)).comp projectDiffeomorphism

theorem pairedStrongFullBRSTAction_hasFDerivAt (input : Core) (hInput : input ∈ Domain) :
    HasFDerivAt
      (pairedStrongFullBRSTAction period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure source)
      (pairedStrongFullBRSTEulerOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure source input) input := by
  have hAbelian := (pairedStrongAbelianGaugeFixedAction_hasFDerivAt period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    (projectAbelian input) hInput.1).comp input (projectAbelian).hasFDerivAt
  have hMapped := pairedStrongFullDiffeomorphismProjection_mem period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure hInput
  have hDiffeomorphism :=
    (pairedMobileDiffeomorphismBRSTAction_hasFDerivAt period hPeriod source plusBase minusBase
      couplings (projectDiffeomorphism input) hMapped).comp input (projectDiffeomorphism).hasFDerivAt
  have hResult := hAbelian.add hDiffeomorphism
  simp only [Function.comp_def] at hResult
  dsimp only [pairedStrongFullBRSTAction, pairedStrongFullBRSTEulerOperator]
  exact hResult

end
end P0EFTJanusPairedStrongFullBRSTAction4D
end JanusFormal
