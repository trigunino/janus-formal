import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBRSTFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalyticSpine4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackQuotientHessian

/-!
# Exact frontier of the global Hessian problem

On every regular Program-P variational chart, the Hessian is the actual
Frechet derivative of the assembled Euler one-form and is symmetric.  Given
the exact dense-core bridge, it pulls back to a symmetric form on the genuine
global smooth tangent.

The historical monolithic D7/D9/D10 contract is retained only as a legacy
compatibility type.  It is not the current analytic target: the D10 Hilbert
coordinate is already a split direct factor, while the genuine remaining
inputs are the dense variational-chart core, primitive SpinC Fourier
realization, block-operator identification and gauge descent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusFrechetPullbackQuotientHessian
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D

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

/-- The actual chartwise Hessian of Candidate A. -/
noncomputable def globalCandidateAHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    chart.Configuration →L[Real] chart.Configuration →L[Real] Real :=
  fderiv Real
    (globalEulerLagrangeOperator period hPeriod chart) configuration

theorem globalCandidateAHessian_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    HasFDerivAt
      (globalEulerLagrangeOperator period hPeriod chart)
      (globalCandidateAHessian period hPeriod chart configuration)
      configuration := by
  exact
    (globalEulerLagrangeOperator_differentiable
      period hPeriod chart).differentiableAt.hasFDerivAt

theorem globalCandidateAHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration first second : chart.Configuration) :
    globalCandidateAHessian period hPeriod chart configuration first second =
      globalCandidateAHessian period hPeriod chart configuration second first := by
  exact
    globalCandidateA_nonlinearHelmholtz
      period hPeriod chart configuration first second

/-- Exact Noether degeneracy of the genuine Hessian in its second argument.
No critical-point hypothesis is needed because the Euler covector annihilates
the fixed physical gauge generator at every chart configuration. -/
theorem globalCandidateAHessian_annihilates_ghost_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration direction : chart.Configuration)
    (ghost : PhysicalPairedGaugeGhost period hPeriod) :
    globalCandidateAHessian period hPeriod chart configuration direction
        (symmetry.generator ghost) = 0 := by
  have hApplied :=
    (globalCandidateAHessian_hasFDerivAt
      period hPeriod chart configuration).clm_apply
        (hasFDerivAt_const (x := configuration)
          (c := symmetry.generator ghost))
  have hFunction :
      (fun point : chart.Configuration =>
        globalEulerLagrangeOperator period hPeriod chart point
          (symmetry.generator ghost)) =
        fun _ => (0 : Real) := by
    funext point
    exact globalEuler_annihilates_arbitrary_ghost
      period hPeriod chart symmetry point ghost
  have hZero :
      HasFDerivAt
        (fun point : chart.Configuration =>
          globalEulerLagrangeOperator period hPeriod chart point
            (symmetry.generator ghost))
        (0 : chart.Configuration →L[Real] Real) configuration := by
    rw [hFunction]
    exact hasFDerivAt_const (x := configuration) (c := (0 : Real))
  have hDerivativeEq := hApplied.unique hZero
  have hDirection := congrArg
    (fun derivative : chart.Configuration →L[Real] Real =>
      derivative direction) hDerivativeEq
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
    map_zero, zero_add, add_zero] using hDirection

/-- Symmetry gives the corresponding degeneracy in the first argument. -/
theorem globalCandidateAHessian_annihilates_ghost_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration direction : chart.Configuration)
    (ghost : PhysicalPairedGaugeGhost period hPeriod) :
    globalCandidateAHessian period hPeriod chart configuration
        (symmetry.generator ghost) direction = 0 := by
  rw [globalCandidateAHessian_symmetric
    period hPeriod chart configuration (symmetry.generator ghost) direction]
  exact globalCandidateAHessian_annihilates_ghost_right
    period hPeriod chart symmetry configuration direction ghost

/-- The physical paired gauge directions as a genuine submodule of the
regular chart tangent. -/
def globalCandidateAGaugeDirectionSubmodule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart) :
    Submodule Real chart.Configuration :=
  LinearMap.range symmetry.generator

/-- Algebraic bilinear form underlying the genuine continuous Hessian. -/
noncomputable def globalCandidateAHessianLinear
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    chart.Configuration →ₗ[Real] chart.Configuration →ₗ[Real] Real :=
  continuousHessianToLinear
    (globalCandidateAHessian period hPeriod chart configuration)

theorem globalCandidateAHessianLinear_annihilates_gauge_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateAGaugeDirectionSubmodule
        period hPeriod chart symmetry)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        gauge direction = 0 := by
  rcases hGauge with ⟨ghost, rfl⟩
  exact globalCandidateAHessian_annihilates_ghost_left
    period hPeriod chart symmetry configuration direction ghost

theorem globalCandidateAHessianLinear_annihilates_gauge_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateAGaugeDirectionSubmodule
        period hPeriod chart symmetry)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        direction gauge = 0 := by
  rcases hGauge with ⟨ghost, rfl⟩
  exact globalCandidateAHessian_annihilates_ghost_right
    period hPeriod chart symmetry configuration direction ghost

/-- Canonical algebraic descent of the true Hessian to the physical paired
gauge quotient. -/
noncomputable def globalCandidateAHessianGaugeQuotient
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration) :
    (chart.Configuration ⧸
        globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry) →ₗ[Real]
      (chart.Configuration ⧸
        globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry) →ₗ[Real] Real :=
  quotientHessian
    (globalCandidateAHessianLinear period hPeriod chart configuration)
    (globalCandidateAGaugeDirectionSubmodule period hPeriod chart symmetry)
    (globalCandidateAHessianLinear_annihilates_gauge_left
      period hPeriod chart symmetry configuration)
    (globalCandidateAHessianLinear_annihilates_gauge_right
      period hPeriod chart symmetry configuration)

@[simp]
theorem globalCandidateAHessianGaugeQuotient_mkQ
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration first second : chart.Configuration) :
    globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration
        ((globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry).mkQ first)
        ((globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry).mkQ second) =
      globalCandidateAHessian period hPeriod chart configuration
        first second :=
  rfl

theorem globalCandidateAHessianGaugeQuotient_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (first second :
      chart.Configuration ⧸
        globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry) :
    globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration first second =
      globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration second first := by
  obtain ⟨first, rfl⟩ :=
    (globalCandidateAGaugeDirectionSubmodule
      period hPeriod chart symmetry).mkQ_surjective first
  obtain ⟨second, rfl⟩ :=
    (globalCandidateAGaugeDirectionSubmodule
      period hPeriod chart symmetry).mkQ_surjective second
  exact globalCandidateAHessian_symmetric
    period hPeriod chart configuration first second

/-- Hessian pulled back from the regular chart to the genuine smooth global
tangent through its dense injective analysis map. -/
noncomputable def globalCandidateAHessianOnSmoothGlobalCore
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
    (first second : GlobalFieldTangent period hPeriod configuration) :
    Real :=
  globalCandidateAHessian period hPeriod chart bridge.baseConfiguration
    (bridge.tangentAnalysis first) (bridge.tangentAnalysis second)

theorem globalCandidateAHessianOnSmoothGlobalCore_symmetric
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
    (first second : GlobalFieldTangent period hPeriod configuration) :
    globalCandidateAHessianOnSmoothGlobalCore
        period hPeriod configuration chart bridge first second =
      globalCandidateAHessianOnSmoothGlobalCore
        period hPeriod configuration chart bridge second first :=
  globalCandidateAHessian_symmetric period hPeriod chart
    bridge.baseConfiguration (bridge.tangentAnalysis first)
      (bridge.tangentAnalysis second)

/-- Current first residual: dense identification of the genuine smooth
tangent with a core of the regular action chart. -/
abbrev GlobalHessianVariationalCoreContract4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :=
  ProgramPGlobalVariationalChartCoreBridge4D
    period hPeriod configuration chart

/-- Current independent SpinC Fourier residual. -/
abbrev GlobalHessianSpinCGeometricFourierContract4D :=
  ProgramPGlobalSpinCGeometricFourierContract4D period hPeriod

/-- Historical over-strong aggregate, retained for downstream compatibility.
New proofs should use the split contracts above and the constructed analytic
spine instead. -/
abbrev LegacyGlobalHessianFredholmAgreementContract4D
    (Spinor : Type*)
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :=
  RemainingProgramPD7D9D10DomainAgreement4D
    period hPeriod Spinor domain

theorem global_hessian_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (∀ configuration,
      HasFDerivAt
        (globalEulerLagrangeOperator period hPeriod chart)
        (globalCandidateAHessian period hPeriod chart configuration)
        configuration) ∧
      ∀ configuration first second,
        globalCandidateAHessian period hPeriod chart configuration first second =
          globalCandidateAHessian period hPeriod chart configuration second first :=
  ⟨globalCandidateAHessian_hasFDerivAt period hPeriod chart,
    globalCandidateAHessian_symmetric period hPeriod chart⟩

end
end P0EFTJanusProgramPGlobalHessianFrontier4D
end JanusFormal
