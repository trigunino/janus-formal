import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateADiffeomorphismHessianBridge4D

/-!
# Candidate-A critical diffeomorphism Hessian quotient

At a critical configuration, differentiable generators of exact nonlinear
diffeomorphism flows span a two-sided kernel submodule of the genuine
Candidate-A Hessian.  Hence the Hessian descends algebraically both by these
directions alone and, when the exact paired `U(1)²` symmetry is supplied, by
their sum with the physical gauge directions.

Every statement is conditional on the nonlinear symmetry, pointwise
differentiability of all its generators, and criticality.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateACriticalDiffeomorphismHessianQuotient4D

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
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPCandidateADiffeomorphismHessianBridge4D
open P0EFTJanusFrechetPullbackQuotientHessian

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

/-- Public differentiability hypothesis for every field-dependent
diffeomorphism-flow generator at one chart configuration. -/
structure GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration) : Prop where
  differentiableAt : ∀ ghost : CInfinityDiffeomorphismGhost period hPeriod,
    DifferentiableAt Real (symmetry.flow ghost).generator configuration

/-- Span of all nonlinear diffeomorphism-flow generators evaluated at one
configuration.  The dependence on the base configuration is essential. -/
def globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration) :
    Submodule Real chart.Configuration :=
  Submodule.span Real
    (Set.range fun ghost : CInfinityDiffeomorphismGhost period hPeriod =>
      (symmetry.flow ghost).generator configuration)

/-- At a critical point, the algebraic Hessian kills the full span of
nonlinear diffeomorphism-flow generators in its first argument. -/
theorem globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_left_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart symmetry configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
        period hPeriod chart symmetry configuration)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        gauge direction = 0 := by
  refine Submodule.span_induction
    (p := fun gauge _ =>
      globalCandidateAHessianLinear period hPeriod chart configuration
        gauge direction = 0)
    ?_ ?_ ?_ ?_ hGauge
  · rintro generator ⟨ghost, rfl⟩
    exact
      globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_left_at_critical
        period hPeriod chart symmetry ghost configuration direction
        (fderiv Real (symmetry.flow ghost).generator configuration)
        (hDifferentiable.differentiableAt ghost).hasFDerivAt hCritical
  · simp
  · intro first second _ _ hFirst hSecond
    simp [hFirst, hSecond]
  · intro scalar generator _ hGenerator
    simp [hGenerator]

/-- At a critical point, the algebraic Hessian kills the full span of
nonlinear diffeomorphism-flow generators in its second argument. -/
theorem globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_right_at_critical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart symmetry configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
        period hPeriod chart symmetry configuration)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        direction gauge = 0 := by
  refine Submodule.span_induction
    (p := fun gauge _ =>
      globalCandidateAHessianLinear period hPeriod chart configuration
        direction gauge = 0)
    ?_ ?_ ?_ ?_ hGauge
  · rintro generator ⟨ghost, rfl⟩
    exact
      globalCandidateAHessian_annihilates_diffeomorphismFlowGenerator_right_at_critical
        period hPeriod chart symmetry ghost configuration direction
        (fderiv Real (symmetry.flow ghost).generator configuration)
        (hDifferentiable.differentiableAt ghost).hasFDerivAt hCritical
  · simp
  · intro first second _ _ hFirst hSecond
    simp [hFirst, hSecond]
  · intro scalar generator _ hGenerator
    simp [hGenerator]

/-- Algebraic Hessian descended by the nonlinear diffeomorphism directions
at a supplied critical configuration. -/
noncomputable def globalCandidateAHessianCriticalDiffeomorphismFlowQuotient
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart symmetry configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0) :
    (chart.Configuration ⧸
        globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
          period hPeriod chart symmetry configuration) →ₗ[Real]
      (chart.Configuration ⧸
        globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
          period hPeriod chart symmetry configuration) →ₗ[Real] Real :=
  quotientHessian
    (globalCandidateAHessianLinear period hPeriod chart configuration)
    (globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
      period hPeriod chart symmetry configuration)
    (globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_left_at_critical
      period hPeriod chart symmetry configuration hDifferentiable hCritical)
    (globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_right_at_critical
      period hPeriod chart symmetry configuration hDifferentiable hCritical)

@[simp]
theorem globalCandidateAHessianCriticalDiffeomorphismFlowQuotient_mkQ
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart symmetry configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (first second : chart.Configuration) :
    globalCandidateAHessianCriticalDiffeomorphismFlowQuotient
        period hPeriod chart symmetry configuration hDifferentiable hCritical
        ((globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
          period hPeriod chart symmetry configuration).mkQ first)
        ((globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
          period hPeriod chart symmetry configuration).mkQ second) =
      globalCandidateAHessian period hPeriod chart configuration first second :=
  rfl

theorem globalCandidateAHessianCriticalDiffeomorphismFlowQuotient_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart symmetry configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (first second :
      chart.Configuration ⧸
        globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
          period hPeriod chart symmetry configuration) :
    globalCandidateAHessianCriticalDiffeomorphismFlowQuotient
        period hPeriod chart symmetry configuration hDifferentiable hCritical
        first second =
      globalCandidateAHessianCriticalDiffeomorphismFlowQuotient
        period hPeriod chart symmetry configuration hDifferentiable hCritical
        second first := by
  obtain ⟨first, rfl⟩ :=
    (globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
      period hPeriod chart symmetry configuration).mkQ_surjective first
  obtain ⟨second, rfl⟩ :=
    (globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
      period hPeriod chart symmetry configuration).mkQ_surjective second
  exact globalCandidateAHessian_symmetric
    period hPeriod chart configuration first second

/-- Total critical gauge submodule: exact paired `U(1)²` directions plus
the span of the nonlinear diffeomorphism-flow generators at the base point. -/
def globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration) :
    Submodule Real chart.Configuration :=
  globalCandidateAGaugeDirectionSubmodule period hPeriod chart physical ⊔
    globalCandidateADiffeomorphismFlowDirectionSubmoduleAt
      period hPeriod chart diffeomorphism configuration

/-- The critical Hessian kills the combined paired-`U(1)²` and nonlinear
diffeomorphism gauge submodule in its first argument. -/
theorem globalCandidateAHessianLinear_annihilates_criticalDiffeomorphismGauge_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart diffeomorphism configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
        period hPeriod chart physical diffeomorphism configuration)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        gauge direction = 0 := by
  rcases Submodule.mem_sup.mp hGauge with
    ⟨physicalDirection, hPhysical, diffeomorphismDirection, hDiffeomorphism, rfl⟩
  have hPhysicalZero :=
    globalCandidateAHessianLinear_annihilates_gauge_left
      period hPeriod chart physical configuration physicalDirection
      hPhysical direction
  have hDiffeomorphismZero :=
    globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_left_at_critical
      period hPeriod chart diffeomorphism configuration hDifferentiable
      hCritical diffeomorphismDirection hDiffeomorphism direction
  simp [hPhysicalZero, hDiffeomorphismZero]

/-- The critical Hessian kills the combined paired-`U(1)²` and nonlinear
diffeomorphism gauge submodule in its second argument. -/
theorem globalCandidateAHessianLinear_annihilates_criticalDiffeomorphismGauge_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart diffeomorphism configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
        period hPeriod chart physical diffeomorphism configuration)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        direction gauge = 0 := by
  rcases Submodule.mem_sup.mp hGauge with
    ⟨physicalDirection, hPhysical, diffeomorphismDirection, hDiffeomorphism, rfl⟩
  have hPhysicalZero :=
    globalCandidateAHessianLinear_annihilates_gauge_right
      period hPeriod chart physical configuration physicalDirection
      hPhysical direction
  have hDiffeomorphismZero :=
    globalCandidateAHessianLinear_annihilates_diffeomorphismFlow_right_at_critical
      period hPeriod chart diffeomorphism configuration hDifferentiable
      hCritical diffeomorphismDirection hDiffeomorphism direction
  simp [hPhysicalZero, hDiffeomorphismZero]

/-- Algebraic Hessian descended by the combined paired-`U(1)²` and nonlinear
diffeomorphism directions at a supplied critical configuration. -/
noncomputable def globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart diffeomorphism configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0) :
    (chart.Configuration ⧸
        globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
          period hPeriod chart physical diffeomorphism configuration) →ₗ[Real]
      (chart.Configuration ⧸
        globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
          period hPeriod chart physical diffeomorphism configuration) →ₗ[Real]
        Real :=
  quotientHessian
    (globalCandidateAHessianLinear period hPeriod chart configuration)
    (globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
      period hPeriod chart physical diffeomorphism configuration)
    (globalCandidateAHessianLinear_annihilates_criticalDiffeomorphismGauge_left
      period hPeriod chart physical diffeomorphism configuration
      hDifferentiable hCritical)
    (globalCandidateAHessianLinear_annihilates_criticalDiffeomorphismGauge_right
      period hPeriod chart physical diffeomorphism configuration
      hDifferentiable hCritical)

@[simp]
theorem globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient_mkQ
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart diffeomorphism configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (first second : chart.Configuration) :
    globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient
        period hPeriod chart physical diffeomorphism configuration
        hDifferentiable hCritical
        ((globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
          period hPeriod chart physical diffeomorphism configuration).mkQ first)
        ((globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
          period hPeriod chart physical diffeomorphism configuration).mkQ second) =
      globalCandidateAHessian period hPeriod chart configuration first second :=
  rfl

theorem globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (hDifferentiable :
      GlobalCandidateADiffeomorphismFlowGeneratorDifferentiabilityAt
        period hPeriod chart diffeomorphism configuration)
    (hCritical :
      globalEulerLagrangeOperator period hPeriod chart configuration = 0)
    (first second :
      chart.Configuration ⧸
        globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
          period hPeriod chart physical diffeomorphism configuration) :
    globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient
        period hPeriod chart physical diffeomorphism configuration
        hDifferentiable hCritical first second =
      globalCandidateAHessianCriticalDiffeomorphismGaugeQuotient
        period hPeriod chart physical diffeomorphism configuration
        hDifferentiable hCritical second first := by
  obtain ⟨first, rfl⟩ :=
    (globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
      period hPeriod chart physical diffeomorphism configuration).mkQ_surjective
      first
  obtain ⟨second, rfl⟩ :=
    (globalCandidateACriticalDiffeomorphismGaugeDirectionSubmodule
      period hPeriod chart physical diffeomorphism configuration).mkQ_surjective
      second
  exact globalCandidateAHessian_symmetric
    period hPeriod chart configuration first second

end
end P0EFTJanusProgramPCandidateACriticalDiffeomorphismHessianQuotient4D
end JanusFormal
