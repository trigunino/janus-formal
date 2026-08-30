import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D

/-!
# Linearization of the nonlinear Hilbert Euler residual

The derivative of the pulled nonlinear Euler covector is the genuine local
Hessian pulled through the same bounded chart realization.  Its Riesz inverse
is therefore the derivative of the nonlinear strong residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D

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

private def realRieszInverseCLM
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] : (H →L[Real] Real) →L[Real] H :=
  (InnerProductSpace.toDual Real H).symm.toContinuousLinearEquiv.toContinuousLinearMap

section

variable
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

/-- The genuine local Hessian pulled through the bounded realization in both
slots. -/
noncomputable def globalCandidateANonlinearHilbertHessian :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        Real :=
  ((ContinuousLinearMap.compL Real
      (CommonAugmentedHilbert period hPeriod configuration data analysis)
      chart.Model Real).flip chartRealization).comp
    ((globalCandidateALocalHessian period hPeriod chart
      (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
        data analysis chart basePoint chartRealization state)).comp
      chartRealization)

/-- This pulled Hessian is the actual derivative of the nonlinear Euler
covector. -/
theorem globalCandidateANonlinearHilbertEulerCovector_hasFDerivAt
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    HasFDerivAt
      (globalCandidateANonlinearHilbertEulerCovector period hPeriod configuration
        data analysis chart basePoint chartRealization)
      (globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state) state := by
  have hEuler :=
    (globalCandidateALocalHessian_hasFDerivAt period hPeriod chart
      (basePoint + chartRealization state) hState).comp state
        (chartRealization.hasFDerivAt.const_add basePoint)
  have hConstant : HasFDerivAt
      (fun _ : CommonAugmentedHilbert period hPeriod configuration data analysis ↦
        chartRealization) 0 state :=
    hasFDerivAt_const (𝕜 := Real) chartRealization state
  have hComposed := hEuler.clm_comp hConstant
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hComposed
  convert hComposed using 1 <;>
    rfl

theorem globalCandidateANonlinearHilbertEulerCovector_fderiv
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    fderiv Real
        (globalCandidateANonlinearHilbertEulerCovector period hPeriod
          configuration data analysis chart basePoint chartRealization) state =
      globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state :=
  (globalCandidateANonlinearHilbertEulerCovector_hasFDerivAt period hPeriod
    configuration data analysis chart basePoint chartRealization state
      hState).fderiv

theorem globalCandidateANonlinearHilbertHessian_pairing
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state first second =
      globalCandidateALocalHessian period hPeriod chart
        (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
          data analysis chart basePoint chartRealization state)
        (chartRealization first) (chartRealization second) := by
  rfl

theorem globalCandidateANonlinearHilbertHessian_symmetric
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state first second =
      globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state second first := by
  rw [globalCandidateANonlinearHilbertHessian_pairing period hPeriod
      configuration data analysis chart basePoint chartRealization state,
    globalCandidateANonlinearHilbertHessian_pairing period hPeriod
      configuration data analysis chart basePoint chartRealization state]
  exact globalCandidateALocalHessian_symmetric period hPeriod chart _ hState _ _

/-- Riesz representative of the pulled nonlinear Hessian. -/
noncomputable def globalCandidateANonlinearHilbertRieszLinearization :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (realRieszInverseCLM
    (CommonAugmentedHilbert period hPeriod configuration data analysis)).comp
    (globalCandidateANonlinearHilbertHessian period hPeriod configuration data
      analysis chart basePoint chartRealization state)

/-- The strong Riesz linearization is the actual derivative of the nonlinear
strong residual. -/
theorem globalCandidateANonlinearHilbertRieszResidual_hasFDerivAt
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    HasFDerivAt
      (globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis chart basePoint chartRealization)
      (globalCandidateANonlinearHilbertRieszLinearization period hPeriod
        configuration data analysis chart basePoint chartRealization state)
      state := by
  let rieszInverse := realRieszInverseCLM
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
  have hRiesz : HasFDerivAt (fun covector ↦ rieszInverse covector) rieszInverse
      (globalCandidateANonlinearHilbertEulerCovector period hPeriod configuration
        data analysis chart basePoint chartRealization state) :=
    rieszInverse.hasFDerivAt
  have hDerivative := hRiesz.comp state
    (globalCandidateANonlinearHilbertEulerCovector_hasFDerivAt period hPeriod
      configuration data analysis chart basePoint chartRealization state hState)
  convert hDerivative using 1 <;>
    rfl

theorem globalCandidateANonlinearHilbertRieszResidual_fderiv
    (hState : globalCandidateANonlinearHilbertChartPoint period hPeriod
      configuration data analysis chart basePoint chartRealization state ∈
        chart.family.domain) :
    fderiv Real
        (globalCandidateANonlinearHilbertRieszResidual period hPeriod
          configuration data analysis chart basePoint chartRealization) state =
      globalCandidateANonlinearHilbertRieszLinearization period hPeriod
        configuration data analysis chart basePoint chartRealization state :=
  (globalCandidateANonlinearHilbertRieszResidual_hasFDerivAt period hPeriod
    configuration data analysis chart basePoint chartRealization state
      hState).fderiv

theorem globalCandidateANonlinearHilbertRieszLinearization_pairing
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real
        (globalCandidateANonlinearHilbertRieszLinearization period hPeriod
          configuration data analysis chart basePoint chartRealization state
            first) second =
      globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart basePoint chartRealization state first second := by
  unfold globalCandidateANonlinearHilbertRieszLinearization
  exact InnerProductSpace.toDual_symm_apply

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D
end JanusFormal
