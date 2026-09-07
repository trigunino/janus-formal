import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongSameActionChartData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileAbelianBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileAbelianBRSTSameAction4D

/-! # The strong physical action with the mobile Abelian BRST action

The original raw physical tangent keeps its established strong norm and
action family. Independent completed nonminimal coordinates are added as a
product. The existing bounded metric/gauge projection supplies the mobile
BRST input, retaining its metric and frame-transport derivatives.
The physical origin remains the original family's actual zero datum.
Nonminimal coordinates are total fields: core zero has zero Abelian
nonminimal fields. A stored nonzero choice is represented by its smooth lift.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongAbelianGaugeFixedAction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusPairedStrongSameActionChartData4D
open P0EFTJanusVariableMetricAbelianBRSTAction4D
open P0EFTJanusPairedMobileAbelianBRSTAction4D
open P0EFTJanusPairedMobileAbelianBRSTSameAction4D

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

private abbrev StrongChart :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
    period hPeriod configuration data analysis realization plusBase minusBase hBase measure

local notation "Chart" => StrongChart period hPeriod configuration data analysis realization
  plusBase minusBase hBase measure
local notation "Nonminimal" =>
  AbelianBRSTNonminimalCore period hPeriod × AbelianBRSTNonminimalCore period hPeriod

/-- The raw strong physical model and independently completed nonminimal fields. -/
abbrev PairedStrongAbelianGaugeFixedCore := (Chart).Model × Nonminimal

local notation "Core" => PairedStrongAbelianGaugeFixedCore period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

def pairedStrongAbelianPhysicalProjection : Core →L[Real] (Chart).Model :=
  ContinuousLinearMap.fst Real _ _

/-- Reuse the already proved bounded physical metric/gauge projection. -/
def pairedStrongAbelianBRSTProjection :
    Core →L[Real] PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase).prodMap
      (ContinuousLinearMap.id Real Nonminimal)

local notation "projectPhysical" => pairedStrongAbelianPhysicalProjection period hPeriod
  configuration data analysis realization plusBase minusBase hBase measure
local notation "projectBRST" => pairedStrongAbelianBRSTProjection period hPeriod
  configuration data analysis realization plusBase minusBase hBase measure

@[simp] theorem pairedStrongAbelianBRSTProjection_apply (input : Core) :
    projectBRST input =
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase input.1, input.2) := rfl

def pairedStrongAbelianGaugeFixedDomain : Set Core := (Chart).family.domain ×ˢ univ

local notation "Domain" => pairedStrongAbelianGaugeFixedDomain period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

theorem pairedStrongAbelianGaugeFixedDomain_isOpen : IsOpen Domain :=
  (Chart).isOpen_domain.prod isOpen_univ

theorem pairedStrongAbelianGaugeFixedDomain_zero_mem : (0 : Core) ∈ Domain :=
  ⟨(Chart).zero_mem_domain, Set.mem_univ _⟩

/-- Physical admissibility already ensures admissibility of the mobile BRST input. -/
theorem pairedStrongAbelianBRSTProjection_mem
    {input : Core} (hInput : input ∈ Domain) :
    projectBRST input ∈ pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase := by
  have hMetric :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain period hPeriod
      configuration.physical plusBase minusBase input.1).mp hInput.1
  exact ⟨⟨hMetric, Set.mem_univ _⟩, Set.mem_univ _⟩

/-- The exact origin is the original family's zero datum, including its installed geometry. -/
theorem pairedStrongAbelianPhysicalOrigin :
    ((Chart).family.datumAt 0 (Chart).zero_mem_domain).1 =
      (pairedStrongSameActionOriginConfiguration period hPeriod configuration data
        plusBase minusBase hBase).physical := rfl

/-- The true physical action plus the variable-metric, transported Abelian BRST action. -/
def pairedStrongAbelianGaugeFixedAction (input : Core) : Real :=
  globalCandidateALocalActionPullback period hPeriod (Chart) (projectPhysical input) +
    pairedMobileAbelianBRSTAction period hPeriod configuration.physical plusBase minusBase
      (projectBRST input)

theorem pairedStrongAbelianGaugeFixedAction_contDiffAt_two
    (input : Core) (hInput : input ∈ Domain) :
    ContDiffAt Real 2
      (pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
        realization plusBase minusBase hBase measure) input := by
  have hPhysical :=
    (globalCandidateALocalActionPullback_contDiffAt_two period hPeriod (Chart)
      (projectPhysical input) hInput.1).comp input (projectPhysical).contDiff.contDiffAt
  have hMapped := pairedStrongAbelianBRSTProjection_mem period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure hInput
  have hBRST :=
    ((pairedMobileAbelianBRSTAction_contDiffOn_two period hPeriod configuration.physical
      plusBase minusBase (projectBRST input) hMapped).contDiffAt
      ((pairedMobileAbelianBRSTDomain_isOpen period hPeriod plusBase minusBase).mem_nhds hMapped)
        ).comp input (projectBRST).contDiff.contDiffAt
  have hResult := hPhysical.add hBRST
  exact hResult

/-- The physical Euler term is retained; the BRST term includes both composition derivatives. -/
def pairedStrongAbelianGaugeFixedEulerOperator (input : Core) : Core →L[Real] Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod (Chart)
    (projectPhysical input)).comp projectPhysical +
    ((fderiv Real (pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase)
      (pairedMobileAbelianBRSTInput period hPeriod configuration.physical plusBase minusBase
        (projectBRST input))).comp
      (fderiv Real
        (pairedMobileAbelianBRSTInput period hPeriod configuration.physical plusBase minusBase)
        (projectBRST input))).comp projectBRST

/-- Sum and chain rules give the actual derivative on every admissible physical point. -/
theorem pairedStrongAbelianGaugeFixedAction_hasFDerivAt
    (input : Core) (hInput : input ∈ Domain) :
    HasFDerivAt
      (pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
        realization plusBase minusBase hBase measure)
      (pairedStrongAbelianGaugeFixedEulerOperator period hPeriod configuration data analysis
        realization plusBase minusBase hBase measure input) input := by
  have hPhysical :=
    (globalCandidateALocalAction_hasFDerivAt period hPeriod (Chart)
      (projectPhysical input) hInput.1).comp input (projectPhysical).hasFDerivAt
  have hMapped := pairedStrongAbelianBRSTProjection_mem period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure hInput
  have hBRST :=
    (pairedMobileAbelianBRSTAction_hasFDerivAt period hPeriod configuration.physical
      plusBase minusBase (projectBRST input) hMapped).comp input (projectBRST).hasFDerivAt
  have hResult := hPhysical.add hBRST
  exact hResult

/-- On the domain the physical summand is exactly the covariant action of the actual datum. -/
theorem pairedStrongAbelianGaugeFixedAction_eq_covariant_add_mobile
    (input : Core) (hInput : input ∈ Domain) :
    pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
        realization plusBase minusBase hBase measure input =
      globalCandidateACovariantAction period hPeriod
          ((Chart).family.datumAt (projectPhysical input) hInput.1).2 measure +
        pairedMobileAbelianBRSTAction period hPeriod configuration.physical plusBase minusBase
          (projectBRST input) := by
  unfold pairedStrongAbelianGaugeFixedAction
  rw [globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
    (Chart) (projectPhysical input) hInput.1]

/-- On smooth total nonminimal fields and canonical volume, this is the
original gauge-fixed action at the family's actual physical datum. No equality
between that datum and the separately supplied origin configuration is assumed. -/
theorem pairedStrongAbelianGaugeFixedAction_smooth_eq_CandidateA
    (hMeasure : measure = intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (nonminimal : Sector → GlobalAbelianNonminimalFields period hPeriod) :
    let datum := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
        direction hDirection
    pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
        realization plusBase minusBase hBase measure
        (direction,
          (smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .plus),
            smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .minus))) =
      globalCandidateAAbelianGaugeFixedAction period hPeriod
        { physical := datum.1
          nonminimal := { configuration.nonminimal with abelian := nonminimal } }
        datum.2 measure := by
  subst measure
  have hPhysical := pairedStrongAbelianGaugeFixedAction_eq_covariant_add_mobile period hPeriod
    configuration data analysis realization plusBase minusBase hBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (direction,
      (smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .plus),
        smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .minus)))
    ⟨hDirection, Set.mem_univ _⟩
  have hBRST := pairedMobileAbelianBRSTAction_eq_datumAt period hPeriod configuration.physical
    plusBase minusBase couplings data direction hDirection nonminimal
  have hSum := congrArg (fun action =>
    globalCandidateACovariantAction period hPeriod
      ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
        period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
          direction hDirection).2
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) + action) hBRST
  exact hPhysical.trans hSum

/-- Gate 645: a C² gauge-fixed action on the original raw strong physical model. -/
theorem paired_strong_abelian_gauge_fixed_action_gate
    (input : Core) (hInput : input ∈ Domain) :
    ContDiffAt Real 2
        (pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
          realization plusBase minusBase hBase measure) input ∧
      HasFDerivAt
        (pairedStrongAbelianGaugeFixedAction period hPeriod configuration data analysis
          realization plusBase minusBase hBase measure)
        (pairedStrongAbelianGaugeFixedEulerOperator period hPeriod configuration data analysis
          realization plusBase minusBase hBase measure input) input :=
  ⟨pairedStrongAbelianGaugeFixedAction_contDiffAt_two period hPeriod configuration data
      analysis realization plusBase minusBase hBase measure input hInput,
    pairedStrongAbelianGaugeFixedAction_hasFDerivAt period hPeriod configuration data
      analysis realization plusBase minusBase hBase measure input hInput⟩

end
end P0EFTJanusPairedStrongAbelianGaugeFixedAction4D
end JanusFormal
