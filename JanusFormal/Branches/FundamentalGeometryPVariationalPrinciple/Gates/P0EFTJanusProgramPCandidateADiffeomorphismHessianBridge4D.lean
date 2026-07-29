import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D

/-!
# Candidate-A nonlinear diffeomorphism/Hessian bridge

The nonlinear flow Noether identity already says that the exact Euler
covector annihilates the field-dependent diffeomorphism generator at every
configuration.  Differentiating that identity gives the correct Hessian
statement: at a critical configuration, the genuine Candidate-A Hessian
annihilates every differentiable flow generator.

No affine-generator shortcut and no nine-block invariance inhabitant are
introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateADiffeomorphismHessianBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusNonlinearGaugeFlowNoether

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
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Exact linearized Noether identity for a field-dependent diffeomorphism
generator.  Away from a critical point, differentiating the generator
contributes the displayed Euler term. -/
theorem globalCandidateAHessian_diffeomorphismFlow_linearizedNoether
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (configuration direction : chart.Configuration)
    (generatorDerivative :
      chart.Configuration →L[Real] chart.Configuration)
    (hGenerator :
      HasFDerivAt (symmetry.flow ghost).generator generatorDerivative
        configuration) :
    globalCandidateAHessian period hPeriod chart configuration direction
          ((symmetry.flow ghost).generator configuration) +
        globalEulerLagrangeOperator period hPeriod chart configuration
          (generatorDerivative direction) = 0 := by
  have hApplied :=
    (globalCandidateAHessian_hasFDerivAt
      period hPeriod chart configuration).clm_apply hGenerator
  have hFunction :
      (fun point : chart.Configuration =>
        globalEulerLagrangeOperator period hPeriod chart point
          ((symmetry.flow ghost).generator point)) =
        fun _ => (0 : Real) := by
    funext point
    exact globalEuler_annihilates_diffeomorphismFlowGenerator
      period hPeriod chart symmetry ghost point
  have hZero :
      HasFDerivAt
        (fun point : chart.Configuration =>
          globalEulerLagrangeOperator period hPeriod chart point
            ((symmetry.flow ghost).generator point))
        (0 : chart.Configuration →L[Real] Real) configuration := by
    rw [hFunction]
    exact hasFDerivAt_const (x := configuration) (c := (0 : Real))
  have hDerivativeEq := hApplied.unique hZero
  have hDirection := congrArg
    (fun derivative : chart.Configuration →L[Real] Real =>
      derivative direction) hDerivativeEq
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, add_comm] using hDirection

/-- At a critical configuration, the actual Candidate-A Hessian annihilates
the differentiable generator of every invariant nonlinear diffeomorphism
flow in its second argument. -/
theorem globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_right_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (configuration direction : chart.Configuration)
    (generatorDerivative :
      chart.Configuration →L[Real] chart.Configuration)
    (hGenerator :
      HasFDerivAt (symmetry.flow ghost).generator generatorDerivative
        configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0) :
    globalCandidateAHessian period hPeriod chart configuration direction
        ((symmetry.flow ghost).generator configuration) = 0 := by
  have hLinearized :=
    globalCandidateAHessian_diffeomorphismFlow_linearizedNoether
      period hPeriod chart symmetry ghost configuration direction
      generatorDerivative hGenerator
  simpa [hCritical] using hLinearized

/-- Symmetry of the genuine Hessian gives the corresponding kernel statement
in its first argument. -/
theorem globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_left_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (configuration direction : chart.Configuration)
    (generatorDerivative :
      chart.Configuration →L[Real] chart.Configuration)
    (hGenerator :
      HasFDerivAt (symmetry.flow ghost).generator generatorDerivative
        configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0) :
    globalCandidateAHessian period hPeriod chart configuration
        ((symmetry.flow ghost).generator configuration) direction = 0 := by
  rw [globalCandidateAHessian_symmetric period hPeriod chart configuration
    ((symmetry.flow ghost).generator configuration) direction]
  exact
    globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_right_at_critical
      period hPeriod chart symmetry ghost configuration direction
      generatorDerivative hGenerator hCritical

/-- The same right-kernel statement on the genuine smooth global tangent,
once a supplied dense chart bridge identifies one tangent with the nonlinear
diffeomorphism generator. -/
theorem globalCandidateAHessianOnSmoothGlobalCore_annihilates_diffeomorphism_right_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge :
      ProgramPGlobalVariationalChartCoreBridge4D
        period hPeriod configuration chart)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (direction gaugeDirection :
      GlobalFieldTangent period hPeriod configuration)
    (generatorDerivative :
      chart.Configuration →L[Real] chart.Configuration)
    (hGenerator :
      HasFDerivAt (symmetry.flow ghost).generator generatorDerivative
        bridge.baseConfiguration)
    (hGaugeDirection :
      bridge.tangentAnalysis gaugeDirection =
        (symmetry.flow ghost).generator bridge.baseConfiguration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart
        bridge.baseConfiguration = 0) :
    globalCandidateAHessianOnSmoothGlobalCore period hPeriod configuration
        chart bridge direction gaugeDirection = 0 := by
  unfold globalCandidateAHessianOnSmoothGlobalCore
  rw [hGaugeDirection]
  exact
    globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_right_at_critical
      period hPeriod chart symmetry ghost bridge.baseConfiguration
      (bridge.tangentAnalysis direction) generatorDerivative hGenerator
      hCritical

/-- Symmetry gives the corresponding left-kernel statement on the genuine
smooth global tangent. -/
theorem globalCandidateAHessianOnSmoothGlobalCore_annihilates_diffeomorphism_left_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge :
      ProgramPGlobalVariationalChartCoreBridge4D
        period hPeriod configuration chart)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (gaugeDirection direction :
      GlobalFieldTangent period hPeriod configuration)
    (generatorDerivative :
      chart.Configuration →L[Real] chart.Configuration)
    (hGenerator :
      HasFDerivAt (symmetry.flow ghost).generator generatorDerivative
        bridge.baseConfiguration)
    (hGaugeDirection :
      bridge.tangentAnalysis gaugeDirection =
        (symmetry.flow ghost).generator bridge.baseConfiguration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart
        bridge.baseConfiguration = 0) :
    globalCandidateAHessianOnSmoothGlobalCore period hPeriod configuration
        chart bridge gaugeDirection direction = 0 := by
  rw [globalCandidateAHessianOnSmoothGlobalCore_symmetric period hPeriod
    configuration chart bridge gaugeDirection direction]
  exact
    globalCandidateAHessianOnSmoothGlobalCore_annihilates_diffeomorphism_right_at_critical
      period hPeriod configuration chart bridge symmetry ghost direction
      gaugeDirection generatorDerivative hGenerator hGaugeDirection hCritical

end
end P0EFTJanusProgramPCandidateADiffeomorphismHessianBridge4D
end JanusFormal
