import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D

/-! # Actual strong-chart physical fibers and affine overlaps

The carrier below is exactly the represented admissible physical family.
Normal and physical-ghost coordinates are retained in the original strong
model; their fibers are handled by translations, without an injectivity claim.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongPhysicalFiberTransition4D

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
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

section Algebra

local instance minimalBulkAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup _
local instance minimalBulkModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module _
local instance minimalAddCommGroup (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup _
local instance minimalModule (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module _

variable (configuration : GlobalFieldConfiguration period hPeriod)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- Equality of actual targets recovers every non-erased coordinate. -/
theorem pairedStrongPhysicalTarget_active_eq
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hFirst : first ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hSecond : second ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hTarget : regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase first hFirst =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase second hSecond) :
    first.1.completeVariation.fullMetricPerturbation =
        second.1.completeVariation.fullMetricPerturbation ∧
      first.1.completeVariation.independent.gauge = second.1.completeVariation.independent.gauge ∧
      first.1.completeVariation.independent.llAuxMetric = second.1.completeVariation.independent.llAuxMetric ∧
      first.1.completeVariation.independent.llMeasure = second.1.completeVariation.independent.llMeasure ∧
      first.1.completeVariation.independent.llField = second.1.completeVariation.independent.llField ∧
      first.1.2 = second.1.2 := by
  have hPlus := congrArg (fun target => target.geometry.plusMetric.tensor) hTarget
  have hMinus := congrArg (fun target => target.geometry.minusMetric.tensor) hTarget
  simp only [regularGeneralMetricC2PairedMinimalPhysicalTarget,
    globalMinimalPhysicalConfigurationAt_geometry,
    globalMetricPerturbationPairLorentzChartGeometry_plusTensor] at hPlus
  simp only [regularGeneralMetricC2PairedMinimalPhysicalTarget,
    globalMinimalPhysicalConfigurationAt_geometry,
    globalMetricPerturbationPairLorentzChartGeometry_minusTensor] at hMinus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext sector
    cases sector
    · exact add_left_cancel hPlus
    · exact add_left_cancel hMinus
  · exact add_left_cancel (congrArg (fun target => target.coefficientFields.gauge) hTarget)
  · exact add_left_cancel (congrArg (fun target => target.coefficientFields.llAuxMetric) hTarget)
  · exact add_left_cancel (congrArg (fun target => target.coefficientFields.llMeasure) hTarget)
  · exact add_left_cancel (congrArg (fun target => target.coefficientFields.llField) hTarget)
  · exact add_left_cancel (congrArg (fun target => target.spinCMatter) hTarget)

/-- The displacement within an actual physical fiber, in its two erased slots. -/
def pairedStrongPhysicalFiberTest
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest period hPeriod :=
  ((second - first).1.completeVariation.normalDisplacement,
    (second - first).1.completeVariation.diffeomorphismGhost)

/-- The converse fiber theorem: equal physical targets differ only in the
normal and physical-ghost coordinates. -/
theorem pairedStrongPhysicalTarget_sub_eq_erased
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hFirst : first ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hSecond : second ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hTarget : regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase first hFirst =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase second hSecond) :
    second - first = regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
      period hPeriod configuration (pairedStrongPhysicalFiberTest period hPeriod configuration first second) := by
  obtain ⟨hMetric, hGauge, hAux, hMeasure, hField, hMatter⟩ :=
    pairedStrongPhysicalTarget_active_eq period hPeriod configuration plusBase minusBase
      first second hFirst hSecond hTarget
  apply (globalMinimalPhysicalTangentSectorEquiv period hPeriod configuration).injective
  apply Prod.ext
  · apply (globalMinimalPhysicalSevenBulkEquiv period hPeriod).injective
    change (second.1.completeVariation.fullMetricPerturbation - first.1.completeVariation.fullMetricPerturbation,
      (second.1.completeVariation.independent.gauge - first.1.completeVariation.independent.gauge,
        ((second - first).1.completeVariation.normalDisplacement,
          ((second - first).1.completeVariation.diffeomorphismGhost,
            (second.1.completeVariation.independent.llAuxMetric - first.1.completeVariation.independent.llAuxMetric,
              (second.1.completeVariation.independent.llMeasure - first.1.completeVariation.independent.llMeasure,
                second.1.completeVariation.independent.llField - first.1.completeVariation.independent.llField)))))) =
      (0, (0, ((second - first).1.completeVariation.normalDisplacement,
        ((second - first).1.completeVariation.diffeomorphismGhost, (0, (0, 0))))))
    simp only [hMetric, hGauge, hAux, hMeasure, hField, sub_self]
  · change second.1.2 - first.1.2 = 0
    exact sub_eq_zero.mpr hMatter.symm

/-- Translation within a physical fiber stays in the exact admissible domain. -/
theorem pairedStrongPhysicalFiberTranslation_mem
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hFirst : first ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hSecond : second ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hTarget : regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase first hFirst =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase second hSecond)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase) :
    point + (second - first) ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase := by
  rw [pairedStrongPhysicalTarget_sub_eq_erased period hPeriod configuration
    plusBase minusBase first second hFirst hSecond hTarget]
  simpa only [one_smul] using
    regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period hPeriod
      configuration plusBase minusBase point hPoint
      (pairedStrongPhysicalFiberTest period hPeriod configuration first second) 1

end Algebra

private theorem pairedTargetDatum_congr
    {couplings : GlobalCandidateAActionCouplings} {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (firstTarget secondTarget : GlobalFieldConfiguration period hPeriod)
    (firstPlus firstMinus secondPlus secondMinus : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFirst : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase firstPlus firstMinus)
    (hSecond : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase secondPlus secondMinus)
    (hFirstGeometry : firstTarget.geometry = regularGeneralMetricC2PairedLorentzChartGeometry
      period hPeriod plusBase minusBase firstPlus firstMinus hFirst)
    (hSecondGeometry : secondTarget.geometry = regularGeneralMetricC2PairedLorentzChartGeometry
      period hPeriod plusBase minusBase secondPlus secondMinus hSecond)
    (firstVariation secondVariation : Sector → SmoothAbelianGaugePotential period hPeriod)
    (hTarget : firstTarget = secondTarget) (hPlus : firstPlus = secondPlus)
    (hMinus : firstMinus = secondMinus) (hVariation : firstVariation = secondVariation) :
    regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod configuration firstTarget
      couplings data plusBase minusBase firstPlus firstMinus hFirst hFirstGeometry firstVariation =
    regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod configuration secondTarget
      couplings data plusBase minusBase secondPlus secondMinus hSecond hSecondGeometry secondVariation := by
  subst secondTarget
  subst secondPlus
  subst secondMinus
  subst secondVariation
  rfl

private theorem pairedGravity_congr
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (firstPlus firstMinus secondPlus secondMinus : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFirst : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase firstPlus firstMinus)
    (hSecond : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase secondPlus secondMinus)
    (hPlus : firstPlus = secondPlus) (hMinus : firstMinus = secondMinus) :
    regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase firstPlus firstMinus hFirst =
      regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase secondPlus secondMinus hSecond ∧
    regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase firstPlus firstMinus hFirst =
      regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase secondPlus secondMinus hSecond := by
  subst secondPlus
  subst secondMinus
  exact ⟨rfl, rfl⟩

/-- Equal physical targets give equal complete dependent action data in this family. -/
theorem pairedStrongPhysicalTarget_datum_eq
    {couplings : GlobalCandidateAActionCouplings} {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (first second : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hFirst : first ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hSecond : second ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase)
    (hTarget : regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase first hFirst =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase second hSecond) :
    regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase first hFirst =
    regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase second hSecond := by
  have hActive := pairedStrongPhysicalTarget_active_eq period hPeriod configuration
    plusBase minusBase first second hFirst hSecond hTarget
  have hPlus := congrFun hActive.1 .plus
  have hMinus := congrFun hActive.1 .minus
  have hGravity := pairedGravity_congr period hPeriod plusBase minusBase _ _ _ _
    hFirst hSecond hPlus hMinus
  unfold regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum
  apply pairedTargetDatum_congr period hPeriod configuration data plusBase minusBase
  · exact hTarget
  · exact hPlus
  · exact hMinus
  · funext sector
    cases sector
    · simp only [regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation]
      apply congrArg₂ _
      · exact congrArg (fun gravity => gravity.metric) hGravity.1
      · exact congrArg Prod.fst hActive.2.1
    · simp only [regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation]
      apply congrArg₂ _
      · exact congrArg (fun gravity => gravity.metric) hGravity.2
      · exact congrArg Prod.snd hActive.2.1

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section Calculus

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]

local notation "Chart" => regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
  period hPeriod configuration data analysis realization plusBase minusBase hBase measure

/-- The exact physical action is preserved by every physical-fiber translation. -/
theorem pairedStrongPhysicalFiberTranslation_action
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 = ((Chart).family.datumAt second hSecond).1)
    (point : (Chart).Model) (hPoint : point ∈ (Chart).family.domain) :
    globalCandidateALocalActionPullback period hPeriod Chart (point + (second - first)) =
      globalCandidateALocalActionPullback period hPeriod Chart point := by
  have hFiber := pairedStrongPhysicalTarget_sub_eq_erased period hPeriod
    configuration.physical plusBase minusBase first second hFirst hSecond hTarget
  have hAction := regularGeneralMetricC2PairedMinimalPhysicalStrongErasedAction_line
    period hPeriod configuration data analysis realization plusBase minusBase hBase measure
      point hPoint (pairedStrongPhysicalFiberTest period hPeriod configuration.physical first second) 1
  simp only [one_smul] at hAction
  refine Eq.trans ?_ hAction
  apply congrArg (globalCandidateALocalActionPullback period hPeriod Chart)
  apply Subtype.ext
  exact congrArg (fun displacement : GlobalMinimalPhysicalFieldTangent period hPeriod
    configuration.physical => point.1 + displacement.1) hFiber

/-- Concrete affine overlap on the original strong norm, including all fibers. -/
def pairedStrongPhysicalFiberTransition
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 = ((Chart).family.datumAt second hSecond).1) :
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod Chart Chart first second where
  first_mem_domain := hFirst
  second_mem_domain := hSecond
  toFun := fun point => point + (second - first)
  derivative := ContinuousLinearEquiv.refl Real (Chart).Model
  maps_point := by abel
  hasFDerivAt := (ContinuousLinearMap.id Real (Chart).Model).hasFDerivAt.add_const (second - first)
  action_eventuallyEq := by
    filter_upwards [(Chart).isOpen_domain.mem_nhds hFirst] with point hPoint
    exact (pairedStrongPhysicalFiberTranslation_action period hPeriod configuration data
      analysis realization plusBase minusBase hBase measure first second hFirst hSecond
        hTarget point hPoint).symm

/-- Physical Euler covectors agree at all representatives of the same target. -/
theorem pairedStrongPhysicalFiberTransition_euler
    (first second : (Chart).Model)
    (hFirst : first ∈ (Chart).family.domain) (hSecond : second ∈ (Chart).family.domain)
    (hTarget : ((Chart).family.datumAt first hFirst).1 = ((Chart).family.datumAt second hSecond).1) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod Chart first =
      globalCandidateALocalEulerLagrangeOperator period hPeriod Chart second := by
  have hTransition := globalCandidateALocalEulerLagrangeOperator_transition period hPeriod
    (pairedStrongPhysicalFiberTransition period hPeriod configuration data analysis
      realization plusBase minusBase hBase measure first second hFirst hSecond hTarget)
  simpa only [pairedStrongPhysicalFiberTransition, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.comp_id] using hTransition

/-- A concrete physical atlas covering exactly the full admissible image of
this strong family; no other root branches or configurations are claimed. -/
def pairedStrongPhysicalVariationalAtlas :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace) (NullFace := NullFace) measure where
  Index := Unit
  chart := fun _ => Chart
  carrier := {target | ∃ (point : (Chart).Model) (hPoint : point ∈ (Chart).family.domain),
    ((Chart).family.datumAt point hPoint).1 = target}
  cover := by
    rintro target ⟨point, hPoint, hTarget⟩
    exact ⟨(), point, hPoint, hTarget⟩
  transition := by
    intro _ _ first second hFirst hSecond hTarget
    exact pairedStrongPhysicalFiberTransition period hPeriod configuration data analysis
      realization plusBase minusBase hBase measure first second hFirst hSecond hTarget

end Calculus
end
end P0EFTJanusPairedStrongPhysicalFiberTransition4D
end JanusFormal
