import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D

/-!
# Remainder regularity data for the three fixed LL carriers

This file isolates the three analytic inputs required to extend the authentic
LL cross-block covectors continuously and smoothly to their fixed carriers.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  llAuxMetricFixedNormedAddCommGroup
  llAuxMetricFixedInnerProductSpace
  llAuxMetricFixedNormedSpace
  llAuxMetricFixedModule
  llMeasureFixedNormedAddCommGroup
  llMeasureFixedInnerProductSpace
  llMeasureFixedNormedSpace
  llMeasureFixedModule
  llFieldFixedNormedAddCommGroup
  llFieldFixedInnerProductSpace
  llFieldFixedNormedSpace
  llFieldFixedModule
attribute [local instance 10002]
  llAuxMetricFixedSeminormedAddCommGroup
  llAuxMetricFixedAddCommGroup
  llAuxMetricFixedTopologicalSpace
  llMeasureFixedSeminormedAddCommGroup
  llMeasureFixedAddCommGroup
  llMeasureFixedTopologicalSpace
  llFieldFixedSeminormedAddCommGroup
  llFieldFixedAddCommGroup
  llFieldFixedTopologicalSpace
attribute [local instance 10003]
  llAuxMetricFixedPseudoMetricSpace
  llAuxMetricFixedUniformSpace
  llMeasureFixedPseudoMetricSpace
  llMeasureFixedUniformSpace
  llFieldFixedPseudoMetricSpace
  llFieldFixedUniformSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section RegularityData

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev AuxMetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev MeasureHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev FieldHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period hPeriod
    configuration data analysis chartData

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance llCommonFixedAmbientInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
    period hPeriod configuration data analysis

local instance llAuxMetricFixedCompleteSpace :
    CompleteSpace
      (AuxMetricHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace
    period hPeriod configuration data analysis chartData

local instance llMeasureFixedCompleteSpace :
    CompleteSpace
      (MeasureHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace period
    hPeriod configuration data analysis chartData

local instance llFieldFixedCompleteSpace :
    CompleteSpace
      (FieldHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace period
    hPeriod configuration data analysis chartData

local instance llAuxMetricDualNormedAddCommGroup :
    NormedAddCommGroup
      (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance llAuxMetricDualNormedSpace :
    NormedSpace Real
      (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedSpace

local instance llMeasureDualNormedAddCommGroup :
    NormedAddCommGroup
      (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance llMeasureDualNormedSpace :
    NormedSpace Real
      (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedSpace

local instance llFieldDualNormedAddCommGroup :
    NormedAddCommGroup
      (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance llFieldDualNormedSpace :
    NormedSpace Real
      (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ContinuousLinearMap.toNormedSpace

/-- The three missing cross-block covectors on their fixed LL carriers. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D where
  auxMetricCovector :
    FullChart period hPeriod configuration data analysis chartData →
      AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real
  auxMetricRepresents : ∀ state test,
    auxMetricCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
        period hPeriod configuration data analysis chartData state).remainder test
  auxMetricContDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    inferInstance inferInstance ∞ auxMetricCovector
  measureCovector :
    FullChart period hPeriod configuration data analysis chartData →
      MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real
  measureRepresents : ∀ state test,
    measureCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
        period hPeriod configuration data analysis chartData state).remainder test
  measureContDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    inferInstance inferInstance ∞ measureCovector
  fieldCovector :
    FullChart period hPeriod configuration data analysis chartData →
      FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real
  fieldRepresents : ∀ state test,
    fieldCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
        period hPeriod configuration data analysis chartData state).remainder test
  fieldContDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    inferInstance inferInstance ∞ fieldCovector

/-- Construct the three LL remainder covectors from smooth fixed-carrier Riesz
representatives. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D.ofRieszRepresentatives
    (auxMetricRepresentative :
      FullChart period hPeriod configuration data analysis chartData →
        AuxMetricHilbert period hPeriod configuration data analysis chartData)
    (measureRepresentative :
      FullChart period hPeriod configuration data analysis chartData →
        MeasureHilbert period hPeriod configuration data analysis chartData)
    (fieldRepresentative :
      FullChart period hPeriod configuration data analysis chartData →
        FieldHilbert period hPeriod configuration data analysis chartData)
    (auxMetricPairing : ∀ state test,
      inner Real (auxMetricRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state).remainder
            test)
    (measurePairing : ∀ state test,
      inner Real (measureRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
          period hPeriod configuration data analysis chartData state).remainder
            test)
    (fieldPairing : ∀ state test,
      inner Real (fieldRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
          period hPeriod configuration data analysis chartData state).remainder
            test)
    (auxMetricContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ auxMetricRepresentative)
    (measureContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MeasureHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ measureRepresentative)
    (fieldContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (FieldHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ fieldRepresentative) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
      period hPeriod configuration data analysis chartData where
  auxMetricCovector := fun state =>
    InnerProductSpace.toDual Real
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)
      (auxMetricRepresentative state)
  auxMetricRepresents := by
    intro state test
    change
      inner Real (auxMetricRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) = _
    exact auxMetricPairing state test
  auxMetricContDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)
      (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (AuxMetricHilbert period hPeriod configuration data analysis chartData))
      auxMetricRepresentative
      (@ContinuousLinearMap.contDiff Real
        (AuxMetricHilbert period hPeriod configuration data analysis chartData)
        (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
          Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (AuxMetricHilbert period hPeriod configuration data analysis
            chartData)).toContinuousLinearEquiv.toContinuousLinearMap)
      auxMetricContDiff
  measureCovector := fun state =>
    InnerProductSpace.toDual Real
      (MeasureHilbert period hPeriod configuration data analysis chartData)
      (measureRepresentative state)
  measureRepresents := by
    intro state test
    change
      inner Real (measureRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) = _
    exact measurePairing state test
  measureContDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (MeasureHilbert period hPeriod configuration data analysis chartData)
      (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (MeasureHilbert period hPeriod configuration data analysis chartData))
      measureRepresentative
      (@ContinuousLinearMap.contDiff Real
        (MeasureHilbert period hPeriod configuration data analysis chartData)
        (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
          Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (MeasureHilbert period hPeriod configuration data analysis
            chartData)).toContinuousLinearEquiv.toContinuousLinearMap)
      measureContDiff
  fieldCovector := fun state =>
    InnerProductSpace.toDual Real
      (FieldHilbert period hPeriod configuration data analysis chartData)
      (fieldRepresentative state)
  fieldRepresents := by
    intro state test
    change
      inner Real (fieldRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) = _
    exact fieldPairing state test
  fieldContDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (FieldHilbert period hPeriod configuration data analysis chartData)
      (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (FieldHilbert period hPeriod configuration data analysis chartData))
      fieldRepresentative
      (@ContinuousLinearMap.contDiff Real
        (FieldHilbert period hPeriod configuration data analysis chartData)
        (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
          Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (FieldHilbert period hPeriod configuration data analysis
            chartData)).toContinuousLinearEquiv.toContinuousLinearMap)
      fieldContDiff

theorem llThreeSlotRemainderRegularityData_auxMetricCovector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.auxMetricCovector = second.auxMetricCovector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData).equalizer
        (first.auxMetricCovector state).continuous
        (second.auxMetricCovector state).continuous
        (by
          funext test
          exact (first.auxMetricRepresents state test).trans
            (second.auxMetricRepresents state test).symm)
  exact congrFun hFunctions value

theorem llThreeSlotRemainderRegularityData_measureCovector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.measureCovector = second.measureCovector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData).equalizer
        (first.measureCovector state).continuous
        (second.measureCovector state).continuous
        (by
          funext test
          exact (first.measureRepresents state test).trans
            (second.measureRepresents state test).symm)
  exact congrFun hFunctions value

theorem llThreeSlotRemainderRegularityData_fieldCovector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.fieldCovector = second.fieldCovector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData).equalizer
        (first.fieldCovector state).continuous
        (second.fieldCovector state).continuous
        (by
          funext test
          exact (first.fieldRepresents state test).trans
            (second.fieldRepresents state test).symm)
  exact congrFun hFunctions value

/-- Fixed-carrier Riesz representative of the LL auxiliary-metric remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    AuxMetricHilbert period hPeriod configuration data analysis chartData :=
  (InnerProductSpace.toDual Real
    (AuxMetricHilbert period hPeriod configuration data analysis chartData)).symm
      (regularity.auxMetricCovector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : AuxMetricHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.auxMetricCovector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    (AuxMetricHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)).symm
    regularity.auxMetricCovector
    (@ContinuousLinearMap.contDiff Real
      (AuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (AuxMetricHilbert period hPeriod configuration data analysis chartData)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (AuxMetricHilbert period hPeriod configuration data analysis
          chartData)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.auxMetricContDiff

/-- Fixed-carrier Riesz representative of the LL measure remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MeasureHilbert period hPeriod configuration data analysis chartData :=
  (InnerProductSpace.toDual Real
    (MeasureHilbert period hPeriod configuration data analysis chartData)).symm
      (regularity.measureCovector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MeasureHilbert period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.measureCovector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MeasureHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    (MeasureHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (MeasureHilbert period hPeriod configuration data analysis chartData)).symm
    regularity.measureCovector
    (@ContinuousLinearMap.contDiff Real
      (MeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (MeasureHilbert period hPeriod configuration data analysis chartData)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (MeasureHilbert period hPeriod configuration data analysis
          chartData)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.measureContDiff

/-- Fixed-carrier Riesz representative of the LL-field remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    FieldHilbert period hPeriod configuration data analysis chartData :=
  (InnerProductSpace.toDual Real
    (FieldHilbert period hPeriod configuration data analysis chartData)).symm
      (regularity.fieldCovector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : FieldHilbert period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.fieldCovector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (FieldHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    (FieldHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (FieldHilbert period hPeriod configuration data analysis chartData)).symm
    regularity.fieldCovector
    (@ContinuousLinearMap.contDiff Real
      (FieldHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (FieldHilbert period hPeriod configuration data analysis chartData)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (FieldHilbert period hPeriod configuration data analysis
          chartData)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.fieldContDiff

/-- Gate 310: the three LL remainder covectors are unique and yield smooth
fixed-carrier Riesz representatives. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_remainder_regularity_data_gate
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    (first.auxMetricCovector = second.auxMetricCovector ∧
      first.measureCovector = second.measureCovector ∧
      first.fieldCovector = second.fieldCovector) ∧
      (@ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (AuxMetricHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData first) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (MeasureHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData first) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (FieldHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData first)) :=
  ⟨⟨llThreeSlotRemainderRegularityData_auxMetricCovector_unique period hPeriod
        configuration data analysis chartData first second,
      ⟨llThreeSlotRemainderRegularityData_measureCovector_unique period hPeriod
          configuration data analysis chartData first second,
        llThreeSlotRemainderRegularityData_fieldCovector_unique period hPeriod
          configuration data analysis chartData first second⟩⟩,
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_contDiff
        period hPeriod configuration data analysis chartData first,
      ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_contDiff
          period hPeriod configuration data analysis chartData first,
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_contDiff
          period hPeriod configuration data analysis chartData first⟩⟩⟩

end RegularityData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
end JanusFormal
