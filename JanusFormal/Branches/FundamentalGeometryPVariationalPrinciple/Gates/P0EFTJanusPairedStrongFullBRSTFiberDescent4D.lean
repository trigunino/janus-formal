import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongFullBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongPhysicalFiberTransition4D

/-! # Full BRST descent along the original physical fibers

Translation between two representatives of the same physical target preserves
the original strong domain and all completed nonminimal fields. The actual
mobile BRST projections, action, and Euler covector agree along this translation.
The construction concerns this fixed physical family and gauge background.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongFullBRSTFiberDescent4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology
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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusPairedMobileAbelianBRSTAction4D
open P0EFTJanusPairedStrongAbelianGaugeFixedAction4D
open P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D
open P0EFTJanusPairedStrongFullBRSTAction4D
open P0EFTJanusPairedStrongPhysicalFiberTransition4D

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

local notation "Chart" => regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
  period hPeriod configuration data analysis realization plusBase minusBase hBase measure
local notation "Core" => PairedStrongFullBRSTCore period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure
local notation "Domain" => pairedStrongFullBRSTDomain period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure
local notation "projectBRST" => pairedStrongAbelianBRSTProjection period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure
local notation "projectDiffeomorphism" => pairedStrongFullDiffeomorphismProjection period hPeriod
  configuration data analysis realization plusBase minusBase hBase measure

/-- An affine homeomorphism of the existing full strong core, with identity derivative. -/
def pairedStrongFullBRSTFiberTranslation (first second : (Chart).Model) : Core ≃ₜ Core where
  toFun point := point + (((second - first), 0), 0)
  invFun point := point - (((second - first), 0), 0)
  left_inv point := add_sub_cancel_right point _
  right_inv point := sub_add_cancel point _
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

local notation "translate" => pairedStrongFullBRSTFiberTranslation period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

@[simp] theorem pairedStrongFullBRSTFiberTranslation_apply
    (first second : (Chart).Model) (point : Core) :
    translate first second point = point + (((second - first), 0), 0) := rfl

theorem pairedStrongFullBRSTFiberTranslation_hasFDerivAt
    (first second : (Chart).Model) (point : Core) :
    HasFDerivAt (translate first second) (ContinuousLinearMap.id Real Core) point :=
  (ContinuousLinearMap.id Real Core).hasFDerivAt.add_const (((second - first), 0), 0)

theorem pairedStrongFullBRSTFiberTranslation_contDiff
    (first second : (Chart).Model) : ContDiff Real ∞ (translate first second) :=
  contDiff_id.add contDiff_const

@[simp] theorem pairedStrongFullBRSTFiberTranslation_representative
    (first second : (Chart).Model)
    (abelian : AbelianBRSTNonminimalCore period hPeriod × AbelianBRSTNonminimalCore period hPeriod)
    (diffeomorphism : DiffeomorphismNonminimalC2Core period hPeriod) :
    translate first second ((first, abelian), diffeomorphism) =
      ((second, abelian), diffeomorphism) := by
  change ((first + (second - first), abelian + 0), diffeomorphism + 0) = _
  have hPoint : first + (second - first) = second := by abel
  rw [hPoint, add_zero, add_zero]

private theorem metricGaugeCore_fiber_eq
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1) :
    globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase first =
      globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase second := by
  obtain ⟨hMetric, hGauge, _⟩ := pairedStrongPhysicalTarget_active_eq period hPeriod
    configuration.physical plusBase minusBase first second hFirst hSecond hTarget
  simp only [globalMinimalPhysicalPairedMetricGaugeCoreLinearMap,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap,
    globalMinimalPhysicalPairedMetricCoreLinearMap,
    globalMinimalPhysicalPlusMetricC2MatrixLinearMap,
    globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap,
    globalMinimalPhysicalPairedGaugeCoefficientC2CoreLinearMap,
    globalMinimalPhysicalGaugeCoefficientLinearMap,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hMetric, hGauge]

/-- The native metric/gauge projection forgets precisely the physical-fiber displacement. -/
theorem pairedStrongFullBRSTFiberTranslation_abelianProjection
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (point : Core) :
    projectBRST (translate first second point).1 = projectBRST point.1 := by
  have hCore := metricGaugeCore_fiber_eq period hPeriod configuration data analysis realization
    plusBase minusBase hBase measure first second hFirst hSecond hTarget
  have hSame : projectBRST (second, 0) = projectBRST (first, 0) :=
    Prod.ext hCore.symm rfl
  have hSub := (projectBRST).map_sub (second, 0) (first, 0)
  simp only [Prod.mk_sub_mk, hSame, sub_self] at hSub
  have hAdd := (projectBRST).map_add point.1 (second - first, 0)
  rw [hSub, add_zero] at hAdd
  exact hAdd

theorem pairedStrongFullBRSTFiberTranslation_diffeomorphismProjection
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (point : Core) :
    projectDiffeomorphism (translate first second point) = projectDiffeomorphism point := by
  rw [pairedStrongFullDiffeomorphismProjection_apply,
    pairedStrongFullDiffeomorphismProjection_apply,
    pairedStrongFullBRSTFiberTranslation_abelianProjection period hPeriod configuration data
      analysis realization plusBase minusBase hBase measure first second hFirst hSecond hTarget]
  change ((projectBRST point.1).1.1.1, point.2 + 0) =
    ((projectBRST point.1).1.1.1, point.2)
  rw [add_zero]

/-- The affine overlap preserves the full domain, in both directions. -/
theorem pairedStrongFullBRSTFiberTranslation_mem_iff
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (point : Core) :
    translate first second point ∈ Domain ↔ point ∈ Domain := by
  constructor
  · intro hPoint
    have hBack := pairedStrongPhysicalFiberTranslation_mem period hPeriod configuration.physical
      plusBase minusBase second first hSecond hFirst hTarget.symm
      (point.1.1 + (second - first)) hPoint.1.1
    have hReturn : (point.1.1 + (second - first)) + (first - second) = point.1.1 := by abel
    have hDomainReturn := congrArg
      (fun value : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical =>
        value ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) hReturn
    exact ⟨⟨Eq.mp hDomainReturn hBack, mem_univ _⟩, mem_univ _⟩
  · intro hPoint
    exact ⟨⟨pairedStrongPhysicalFiberTranslation_mem period hPeriod configuration.physical
      plusBase minusBase first second hFirst hSecond hTarget point.1.1 hPoint.1.1,
        mem_univ _⟩, mem_univ _⟩

variable (source : RegularGeneralLorentzMetric period hPeriod)
local notation "Action" => pairedStrongFullBRSTAction period hPeriod configuration data analysis
  realization plusBase minusBase hBase measure source
local notation "Euler" => pairedStrongFullBRSTEulerOperator period hPeriod configuration data analysis
  realization plusBase minusBase hBase measure source

/-- Invariance of the actual physical plus mobile full-BRST action on the strong domain. -/
theorem pairedStrongFullBRSTFiberTranslation_action
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (point : Core) (hPoint : point ∈ Domain) :
    Action (translate first second point) = Action point := by
  have hPhysical := pairedStrongPhysicalFiberTranslation_action period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure first second hFirst hSecond
      hTarget point.1.1 hPoint.1.1
  have hAbelian := pairedStrongFullBRSTFiberTranslation_abelianProjection period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    first second hFirst hSecond hTarget point
  have hDiffeomorphism := pairedStrongFullBRSTFiberTranslation_diffeomorphismProjection
    period hPeriod configuration data analysis realization plusBase minusBase hBase measure
    first second hFirst hSecond hTarget point
  change
    (globalCandidateALocalActionPullback period hPeriod (Chart)
        (point.1.1 + (second - first)) +
      pairedMobileAbelianBRSTAction period hPeriod configuration.physical plusBase minusBase
        (projectBRST (translate first second point).1)) +
      pairedMobileDiffeomorphismBRSTAction period hPeriod source plusBase minusBase couplings
        (projectDiffeomorphism (translate first second point)) =
    (globalCandidateALocalActionPullback period hPeriod (Chart) point.1.1 +
      pairedMobileAbelianBRSTAction period hPeriod configuration.physical plusBase minusBase
        (projectBRST point.1)) +
      pairedMobileDiffeomorphismBRSTAction period hPeriod source plusBase minusBase couplings
        (projectDiffeomorphism point)
  rw [hPhysical, hAbelian, hDiffeomorphism]

/-- The identity derivative of the overlap identifies the genuine full Euler covectors. -/
theorem pairedStrongFullBRSTFiberTranslation_euler
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (point : Core) (hPoint : point ∈ Domain) :
    Euler (translate first second point) = Euler point := by
  have hMapped := (pairedStrongFullBRSTFiberTranslation_mem_iff period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure first second hFirst hSecond
      hTarget point).mpr hPoint
  have hComp := (pairedStrongFullBRSTAction_hasFDerivAt period hPeriod configuration data
    analysis realization plusBase minusBase hBase measure source
      (translate first second point) hMapped).comp point
        (pairedStrongFullBRSTFiberTranslation_hasFDerivAt period hPeriod configuration data
          analysis realization plusBase minusBase hBase measure first second point)
  simp only [Function.comp_def, ContinuousLinearMap.comp_id] at hComp
  have hEqual : (fun value => Action (translate first second value)) =ᶠ[𝓝 point] Action := by
    filter_upwards [(pairedStrongFullBRSTDomain_isOpen period hPeriod configuration data
      analysis realization plusBase minusBase hBase measure).mem_nhds hPoint] with value hValue
    exact pairedStrongFullBRSTFiberTranslation_action period hPeriod configuration data analysis
      realization plusBase minusBase hBase measure source first second hFirst hSecond hTarget
        value hValue
  exact (hEqual.hasFDerivAt_iff.mp hComp).unique
    (pairedStrongFullBRSTAction_hasFDerivAt period hPeriod configuration data analysis realization
      plusBase minusBase hBase measure source point hPoint)

/-- Both full action and Euler covector descend at representatives with the same completed fields. -/
theorem pairedStrongFullBRST_same_target
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 =
      ((Chart).family.datumAt second hSecond).1)
    (abelian : AbelianBRSTNonminimalCore period hPeriod × AbelianBRSTNonminimalCore period hPeriod)
    (diffeomorphism : DiffeomorphismNonminimalC2Core period hPeriod) :
    Action ((first, abelian), diffeomorphism) = Action ((second, abelian), diffeomorphism) ∧
      Euler ((first, abelian), diffeomorphism) = Euler ((second, abelian), diffeomorphism) := by
  have hPoint : ((first, abelian), diffeomorphism) ∈ Domain :=
    ⟨⟨hFirst, mem_univ _⟩, mem_univ _⟩
  have hAction := pairedStrongFullBRSTFiberTranslation_action period hPeriod configuration data
    analysis realization plusBase minusBase hBase measure source first second hFirst hSecond hTarget
      ((first, abelian), diffeomorphism) hPoint
  have hEuler := pairedStrongFullBRSTFiberTranslation_euler period hPeriod configuration data
    analysis realization plusBase minusBase hBase measure source first second hFirst hSecond hTarget
      ((first, abelian), diffeomorphism) hPoint
  rw [pairedStrongFullBRSTFiberTranslation_representative] at hAction hEuler
  exact ⟨hAction.symm, hEuler.symm⟩

end
end P0EFTJanusPairedStrongFullBRSTFiberDescent4D
end JanusFormal
