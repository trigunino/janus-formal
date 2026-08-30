import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedSmoothWeakStrongResidual4D

/-!
# Nonlinear Candidate-A Euler residual on the common Hilbert space

A bounded realization into an admissible local variational chart pulls the
exact nonlinear action and Euler covector back to the common augmented Hilbert
space.  Frechet--Riesz then gives its strong nonlinear residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Affine realization of a common Hilbert state in the local chart model. -/
def globalCandidateANonlinearHilbertChartPoint
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    chart.Model :=
  basePoint + chartRealization state

/-- Exact nonlinear local action pulled back to the common Hilbert space. -/
def globalCandidateANonlinearHilbertAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model) :
    CommonAugmentedHilbert period hPeriod configuration data analysis → Real :=
  fun state ↦ globalCandidateALocalActionPullback period hPeriod chart
    (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
      data analysis chart basePoint chartRealization state)

/-- Nonlinear Euler covector after pullback to the common Hilbert space. -/
noncomputable def globalCandidateANonlinearHilbertEulerCovector
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod chart
    (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
      data analysis chart basePoint chartRealization state)).comp chartRealization

/-- Strong nonlinear Euler residual furnished by Frechet--Riesz. -/
noncomputable def globalCandidateANonlinearHilbertRieszResidual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (InnerProductSpace.toDual Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis)).symm
      (globalCandidateANonlinearHilbertEulerCovector period hPeriod
        configuration data analysis chart basePoint chartRealization state)

theorem globalCandidateANonlinearHilbertAction_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    HasFDerivAt
      (globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis chart basePoint chartRealization)
      (globalCandidateANonlinearHilbertEulerCovector period hPeriod
        configuration data analysis chart basePoint chartRealization state)
      state := by
  have hDerivative :=
    (globalCandidateALocalAction_hasFDerivAt period hPeriod chart
      (basePoint + chartRealization state) hState).comp state
        (chartRealization.hasFDerivAt.const_add basePoint)
  convert hDerivative using 1 <;>
    rfl

theorem globalCandidateANonlinearHilbertAction_fderiv
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    fderiv Real
      (globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis chart basePoint chartRealization) state =
      globalCandidateANonlinearHilbertEulerCovector period hPeriod
        configuration data analysis chart basePoint chartRealization state :=
  (globalCandidateANonlinearHilbertAction_hasFDerivAt period hPeriod
    configuration data analysis chart basePoint chartRealization state
      hState).fderiv

theorem globalCandidateANonlinearHilbertRieszResidual_pairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real
      (globalCandidateANonlinearHilbertRieszResidual period hPeriod
        configuration data analysis chart basePoint chartRealization state) test =
      globalCandidateANonlinearHilbertEulerCovector period hPeriod
        configuration data analysis chart basePoint chartRealization state test := by
  unfold globalCandidateANonlinearHilbertRieszResidual
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateANonlinearHilbertEulerCovector_eq_zero_iff_rieszResidual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    globalCandidateANonlinearHilbertEulerCovector period hPeriod configuration
        data analysis chart basePoint chartRealization state = 0 ↔
      globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis chart basePoint chartRealization state = 0 := by
  constructor
  · intro hCovector
    simp [globalCandidateANonlinearHilbertRieszResidual, hCovector]
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro test
    rw [← globalCandidateANonlinearHilbertRieszResidual_pairing period hPeriod
      configuration data analysis chart basePoint chartRealization state test,
      hResidual, inner_zero_left]
    rfl

theorem globalCandidateANonlinearHilbertAction_fderiv_eq_zero_iff_rieszResidual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    fderiv Real
        (globalCandidateANonlinearHilbertAction period hPeriod configuration data
          analysis chart basePoint chartRealization) state = 0 ↔
      globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis chart basePoint chartRealization state = 0 := by
  rw [globalCandidateANonlinearHilbertAction_fderiv period hPeriod configuration
    data analysis chart basePoint chartRealization state hState]
  exact globalCandidateANonlinearHilbertEulerCovector_eq_zero_iff_rieszResidual
    period hPeriod configuration data analysis chart basePoint chartRealization
      state

theorem globalCandidateANonlinearHilbertAction_eq_covariant_of_mem
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis chart basePoint chartRealization state =
      globalCandidateACovariantAction period hPeriod
        (chart.family.datumAt
          (globalCandidateANonlinearHilbertChartPoint period hPeriod
            configuration data analysis chart basePoint chartRealization state)
          hState).2 measure := by
  exact globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
    chart _ hState

end
end P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
end JanusFormal
