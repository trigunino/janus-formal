import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBRSTFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalyticSpine4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
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
inputs are the dense variational-chart core, nine-block diffeomorphism
invariance and the non-SpinC block-operator identification.  The primitive
SpinC Fourier sector is now unconditionally unitary and intertwines the
genuine smooth action Hessian `2D + m²` with its maximal self-adjoint
Fredholm multiplier.  Exact linear symmetries combine with the physical
`U(1)²` symmetry, including a specialization to genuine smooth
diffeomorphism ghosts.  A zero-Hessian no-go records why arbitrary couplings
cannot imply the final infinite-dimensional Fredholm realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
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
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
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
    zero_apply, ContinuousLinearMap.flip_apply,
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

/-- Noether degeneracy for an arbitrary certified linear gauge parameter
space, including a future smooth diffeomorphism/BRST generator. -/
theorem globalCandidateAHessian_annihilates_linearGauge_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter)
    (configuration direction : chart.Configuration)
    (gauge : GaugeParameter) :
    globalCandidateAHessian period hPeriod chart configuration direction
        (symmetry.generator gauge) = 0 := by
  have hApplied :=
    (globalCandidateAHessian_hasFDerivAt
      period hPeriod chart configuration).clm_apply
        (hasFDerivAt_const (x := configuration)
          (c := symmetry.generator gauge))
  have hFunction :
      (fun point : chart.Configuration =>
        globalEulerLagrangeOperator period hPeriod chart point
          (symmetry.generator gauge)) =
        fun _ => (0 : Real) := by
    funext point
    exact globalEuler_annihilates_linearGauge
      period hPeriod chart symmetry point gauge
  have hZero :
      HasFDerivAt
        (fun point : chart.Configuration =>
          globalEulerLagrangeOperator period hPeriod chart point
            (symmetry.generator gauge))
        (0 : chart.Configuration →L[Real] Real) configuration := by
    rw [hFunction]
    exact hasFDerivAt_const (x := configuration) (c := (0 : Real))
  have hDerivativeEq := hApplied.unique hZero
  have hDirection := congrArg
    (fun derivative : chart.Configuration →L[Real] Real =>
      derivative direction) hDerivativeEq
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.flip_apply,
    map_zero, zero_add, add_zero] using hDirection

theorem globalCandidateAHessian_annihilates_linearGauge_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter)
    (configuration direction : chart.Configuration)
    (gauge : GaugeParameter) :
    globalCandidateAHessian period hPeriod chart configuration
        (symmetry.generator gauge) direction = 0 := by
  rw [globalCandidateAHessian_symmetric
    period hPeriod chart configuration (symmetry.generator gauge) direction]
  exact globalCandidateAHessian_annihilates_linearGauge_right
    period hPeriod chart symmetry configuration direction gauge

/-- Range submodule of an arbitrary exact linear gauge symmetry. -/
def globalCandidateALinearGaugeDirectionSubmodule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter) :
    Submodule Real chart.Configuration :=
  LinearMap.range symmetry.generator

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

theorem globalCandidateAHessianLinear_annihilates_linearGauge_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter)
    (configuration gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateALinearGaugeDirectionSubmodule
        period hPeriod chart symmetry)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        gauge direction = 0 := by
  rcases hGauge with ⟨parameter, rfl⟩
  exact globalCandidateAHessian_annihilates_linearGauge_left
    period hPeriod chart symmetry configuration direction parameter

theorem globalCandidateAHessianLinear_annihilates_linearGauge_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter)
    (configuration gauge : chart.Configuration)
    (hGauge :
      gauge ∈ globalCandidateALinearGaugeDirectionSubmodule
        period hPeriod chart symmetry)
    (direction : chart.Configuration) :
    globalCandidateAHessianLinear period hPeriod chart configuration
        direction gauge = 0 := by
  rcases hGauge with ⟨parameter, rfl⟩
  exact globalCandidateAHessian_annihilates_linearGauge_right
    period hPeriod chart symmetry configuration direction parameter

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

/-- The descended paired-`U(1)²` Hessian is canonical. -/
theorem globalCandidateAHessianGaugeQuotient_unique
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (candidate :
      (chart.Configuration ⧸
          globalCandidateAGaugeDirectionSubmodule
            period hPeriod chart symmetry) →ₗ[Real]
        (chart.Configuration ⧸
          globalCandidateAGaugeDirectionSubmodule
            period hPeriod chart symmetry) →ₗ[Real] Real)
    (hCandidate : ∀ first second : chart.Configuration,
      candidate
          ((globalCandidateAGaugeDirectionSubmodule
            period hPeriod chart symmetry).mkQ first)
          ((globalCandidateAGaugeDirectionSubmodule
            period hPeriod chart symmetry).mkQ second) =
        globalCandidateAHessian period hPeriod chart configuration
          first second) :
    candidate =
      globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration := by
  unfold globalCandidateAHessianGaugeQuotient
  exact quotientHessian_unique
    (globalCandidateAHessianLinear period hPeriod chart configuration)
    (globalCandidateAGaugeDirectionSubmodule period hPeriod chart symmetry)
    (globalCandidateAHessianLinear_annihilates_gauge_left
      period hPeriod chart symmetry configuration)
    (globalCandidateAHessianLinear_annihilates_gauge_right
      period hPeriod chart symmetry configuration)
    candidate hCandidate

/-- Chartwise package obtained from every supplied exact physical symmetry,
the Noether identity and nonlinear Helmholtz symmetry.  No critical-point
hypothesis is used. -/
structure GlobalCandidateAHessianGaugeDescentCertificate4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration) : Prop where
  derivative :
    HasFDerivAt
      (globalEulerLagrangeOperator period hPeriod chart)
      (globalCandidateAHessian period hPeriod chart configuration)
      configuration
  symmetric : ∀ first second,
    globalCandidateAHessian period hPeriod chart configuration first second =
      globalCandidateAHessian period hPeriod chart configuration second first
  annihilatesGaugeLeft : ∀ ghost direction,
    globalCandidateAHessian period hPeriod chart configuration
        (symmetry.generator ghost) direction = 0
  annihilatesGaugeRight : ∀ ghost direction,
    globalCandidateAHessian period hPeriod chart configuration
        direction (symmetry.generator ghost) = 0
  quotientExact : ∀ first second,
    globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration
        ((globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry).mkQ first)
        ((globalCandidateAGaugeDirectionSubmodule
          period hPeriod chart symmetry).mkQ second) =
      globalCandidateAHessian period hPeriod chart configuration first second
  quotientSymmetric : ∀ first second,
    globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration first second =
      globalCandidateAHessianGaugeQuotient
        period hPeriod chart symmetry configuration second first

theorem globalCandidateAHessianGaugeDescentCertificate4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration) :
    GlobalCandidateAHessianGaugeDescentCertificate4D
      period hPeriod chart symmetry configuration where
  derivative :=
    globalCandidateAHessian_hasFDerivAt
      period hPeriod chart configuration
  symmetric :=
    globalCandidateAHessian_symmetric
      period hPeriod chart configuration
  annihilatesGaugeLeft := fun ghost direction =>
    globalCandidateAHessian_annihilates_ghost_left
      period hPeriod chart symmetry configuration direction ghost
  annihilatesGaugeRight := fun ghost direction =>
    globalCandidateAHessian_annihilates_ghost_right
      period hPeriod chart symmetry configuration direction ghost
  quotientExact :=
    globalCandidateAHessianGaugeQuotient_mkQ
      period hPeriod chart symmetry configuration
  quotientSymmetric :=
    globalCandidateAHessianGaugeQuotient_symmetric
      period hPeriod chart symmetry configuration

/-- Exact combined `U(1)² × GaugeParameter` symmetry.  Taking
`GaugeParameter` to be the smooth diffeomorphism/BRST ghost space gives the
total gauge object required by the global Hessian. -/
def globalCandidateACombinedGaugeSymmetry
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (additional :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter) :
    GlobalCandidateALinearGaugeSymmetry period hPeriod chart
      (PhysicalPairedGaugeGhost period hPeriod × GaugeParameter) :=
  physical.toLinearGaugeSymmetry.prod period hPeriod additional

/-- The total gauge submodule generated by the paired physical ghosts and an
additional exact linear symmetry. -/
def globalCandidateACombinedGaugeDirectionSubmodule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (additional :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter) :
    Submodule Real chart.Configuration :=
  globalCandidateALinearGaugeDirectionSubmodule period hPeriod chart
    (globalCandidateACombinedGaugeSymmetry
      period hPeriod physical additional)

/-- The exact total `U(1)² × Diff` gauge submodule when the full action
diffeomorphism certificate is supplied. -/
def globalCandidateATotalDiffeomorphismGaugeDirectionSubmodule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismGaugeSymmetry
        period hPeriod chart) :
    Submodule Real chart.Configuration :=
  globalCandidateACombinedGaugeDirectionSubmodule
    period hPeriod chart physical diffeomorphism

theorem globalCandidateAGaugeDirectionSubmodule_le_combined
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (additional :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter) :
    globalCandidateAGaugeDirectionSubmodule period hPeriod chart physical ≤
      globalCandidateACombinedGaugeDirectionSubmodule
        period hPeriod chart physical additional := by
  rintro direction ⟨ghost, rfl⟩
  refine ⟨(ghost, 0), ?_⟩
  simp [globalCandidateACombinedGaugeSymmetry,
    GlobalCandidateALinearGaugeSymmetry.prod]

/-- Exact terminal analytic datum still required after the constructed
paired-`U(1)²` quotient.  The supplied total gauge submodule may additionally
contain diffeomorphism/BRST directions.  Closed range and finite kernel and
cokernel state precisely the full Fredholm obligation. -/
structure ProgramPGlobalHessianFredholmRealization4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (Analysis : Type*)
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis] where
  totalGaugeDirections : Submodule Real chart.Configuration
  pairedU1Gauge_le :
    globalCandidateAGaugeDirectionSubmodule period hPeriod chart symmetry ≤
      totalGaugeDirections
  hessianGaugeLeft :
    ∀ gauge ∈ totalGaugeDirections, ∀ direction,
      globalCandidateAHessianLinear period hPeriod chart configuration
          gauge direction = 0
  hessianGaugeRight :
    ∀ gauge ∈ totalGaugeDirections, ∀ direction,
      globalCandidateAHessianLinear period hPeriod chart configuration
          direction gauge = 0
  coreAnalysis :
    (chart.Configuration ⧸ totalGaugeDirections) →ₗ[Real] Analysis
  coreAnalysis_injective : Function.Injective coreAnalysis
  coreAnalysis_denseRange : DenseRange coreAnalysis
  operator : Analysis →L[Real] Analysis
  operator_selfAdjoint : IsSelfAdjoint operator
  operator_range_closed :
    IsClosed (LinearMap.range operator.toLinearMap : Set Analysis)
  operator_kernel_finite :
    FiniteDimensional Real (LinearMap.ker operator.toLinearMap)
  operator_cokernel_finite :
    FiniteDimensional Real
      (Analysis ⧸ LinearMap.range operator.toLinearMap)
  pairing_agreement : ∀ first second,
    inner Real (operator (coreAnalysis first)) (coreAnalysis second) =
      quotientHessian
        (globalCandidateAHessianLinear period hPeriod chart configuration)
        totalGaugeDirections hessianGaugeLeft hessianGaugeRight first second

/-- Once an additional exact symmetry is supplied, only the analytic
operator data remain: the combined gauge submodule and its two-sided Hessian
annihilation are now theorems. -/
structure ProgramPGlobalHessianCombinedGaugeOperatorData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (additional :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter)
    (configuration : chart.Configuration)
    (Analysis : Type*)
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis] where
  coreAnalysis :
    (chart.Configuration ⧸
      globalCandidateACombinedGaugeDirectionSubmodule
        period hPeriod chart physical additional) →ₗ[Real] Analysis
  coreAnalysis_injective : Function.Injective coreAnalysis
  coreAnalysis_denseRange : DenseRange coreAnalysis
  operator : Analysis →L[Real] Analysis
  operator_selfAdjoint : IsSelfAdjoint operator
  operator_range_closed :
    IsClosed (LinearMap.range operator.toLinearMap : Set Analysis)
  operator_kernel_finite :
    FiniteDimensional Real (LinearMap.ker operator.toLinearMap)
  operator_cokernel_finite :
    FiniteDimensional Real
      (Analysis ⧸ LinearMap.range operator.toLinearMap)
  pairing_agreement : ∀ first second,
    inner Real (operator (coreAnalysis first)) (coreAnalysis second) =
      quotientHessian
        (globalCandidateAHessianLinear period hPeriod chart configuration)
        (globalCandidateACombinedGaugeDirectionSubmodule
          period hPeriod chart physical additional)
        (globalCandidateAHessianLinear_annihilates_linearGauge_left
          period hPeriod chart
            (globalCandidateACombinedGaugeSymmetry
              period hPeriod physical additional)
            configuration)
        (globalCandidateAHessianLinear_annihilates_linearGauge_right
          period hPeriod chart
            (globalCandidateACombinedGaugeSymmetry
              period hPeriod physical additional)
            configuration)
        first second

/-- Terminal operator datum specialized to the genuine smooth
diffeomorphism ghosts.  Gauge annihilation is already derived from Noether;
the remaining fields are purely analytic and the Hessian pairing equality. -/
abbrev ProgramPGlobalHessianDiffeomorphismGaugeOperatorData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismGaugeSymmetry
        period hPeriod chart)
    (configuration : chart.Configuration)
    (Analysis : Type*)
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis] :=
  ProgramPGlobalHessianCombinedGaugeOperatorData4D
    period hPeriod chart physical diffeomorphism configuration Analysis

/-- Canonical promotion of combined-gauge operator data to the exact terminal
Fredholm realization. -/
def ProgramPGlobalHessianCombinedGaugeOperatorData4D.toFredholmRealization
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace GaugeParameter : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [AddCommGroup GaugeParameter] [Module Real GaugeParameter]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {physical : GlobalCandidateAGhostSymmetry period hPeriod chart}
    {additional :
      GlobalCandidateALinearGaugeSymmetry period hPeriod chart GaugeParameter}
    {configuration : chart.Configuration}
    {Analysis : Type*}
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis]
    (data :
      ProgramPGlobalHessianCombinedGaugeOperatorData4D
        period hPeriod chart physical additional configuration Analysis) :
    ProgramPGlobalHessianFredholmRealization4D
      period hPeriod chart physical configuration Analysis where
  totalGaugeDirections :=
    globalCandidateACombinedGaugeDirectionSubmodule
      period hPeriod chart physical additional
  pairedU1Gauge_le :=
    globalCandidateAGaugeDirectionSubmodule_le_combined
      period hPeriod chart physical additional
  hessianGaugeLeft :=
    globalCandidateAHessianLinear_annihilates_linearGauge_left
      period hPeriod chart
        (globalCandidateACombinedGaugeSymmetry
          period hPeriod physical additional)
        configuration
  hessianGaugeRight :=
    globalCandidateAHessianLinear_annihilates_linearGauge_right
      period hPeriod chart
        (globalCandidateACombinedGaugeSymmetry
          period hPeriod physical additional)
        configuration
  coreAnalysis := data.coreAnalysis
  coreAnalysis_injective := data.coreAnalysis_injective
  coreAnalysis_denseRange := data.coreAnalysis_denseRange
  operator := data.operator
  operator_selfAdjoint := data.operator_selfAdjoint
  operator_range_closed := data.operator_range_closed
  operator_kernel_finite := data.operator_kernel_finite
  operator_cokernel_finite := data.operator_cokernel_finite
  pairing_agreement := data.pairing_agreement

/-- A zero Hessian is incompatible with the advertised Fredholm realization on an
infinite-dimensional Hilbert completion.  Hence chartwise `C²` regularity
alone cannot prove the terminal Fredholm statement; nondegenerate elliptic
input on the physical couplings is logically necessary. -/
theorem no_globalHessianFredholmRealization_of_zero_hessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {physical : GlobalCandidateAGhostSymmetry period hPeriod chart}
    {configuration : chart.Configuration}
    {Analysis : Type*}
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis]
    (hInfinite : ¬ FiniteDimensional Real Analysis)
    (realization :
      ProgramPGlobalHessianFredholmRealization4D
        period hPeriod chart physical configuration Analysis)
    (hZero :
      globalCandidateAHessianLinear period hPeriod chart configuration = 0) :
    False := by
  have hOperatorCore :
      ∀ state,
        realization.operator (realization.coreAnalysis state) = 0 := by
    intro state
    obtain ⟨first, rfl⟩ :=
      realization.totalGaugeDirections.mkQ_surjective state
    apply realization.coreAnalysis_denseRange.eq_zero_of_inner_left (𝕜 := Real)
    intro test
    obtain ⟨second, rfl⟩ :=
      realization.totalGaugeDirections.mkQ_surjective test
    rw [realization.pairing_agreement, quotientHessian_mkQ, hZero]
    rfl
  have hOperatorFunction :
      (fun state : Analysis => realization.operator state) =
        fun _ => (0 : Analysis) :=
    realization.coreAnalysis_denseRange.equalizer
      realization.operator.continuous continuous_const
      (by
        funext state
        exact hOperatorCore state)
  have hOperatorZero : realization.operator = 0 := by
    apply ContinuousLinearMap.ext
    intro state
    exact congrFun hOperatorFunction state
  have hKernelTop :
      LinearMap.ker realization.operator.toLinearMap =
        (⊤ : Submodule Real Analysis) := by
    rw [hOperatorZero]
    exact LinearMap.ker_zero
  letI : FiniteDimensional Real (⊤ : Submodule Real Analysis) := by
    rw [← hKernelTop]
    exact realization.operator_kernel_finite
  apply hInfinite
  exact
    (Submodule.topEquiv :
      (⊤ : Submodule Real Analysis) ≃ₗ[Real] Analysis).finiteDimensional

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

/-- Historical SpinC Fourier contract, retained for compatibility.  The
unconditional construction below supersedes it. -/
abbrev LegacyGlobalHessianSpinCGeometricFourierContract4D :=
  ProgramPGlobalSpinCGeometricFourierContract4D period hPeriod

/-- Fredholm conclusion for the exact primitive SpinC action Hessian. -/
abbrev GlobalHessianSpinCGeometricFredholm4D
    (massSquared : Real) :=
  IsClosed
      (LinearMap.range
        (primitiveSpinCGeometricSignedActionHessianOperator
          period hPeriod massSquared).toFun :
        Set (ComplexDiagonalHilbert
          PrimitiveSpinCGeometricSignedMode)) ∧
    FiniteDimensional Complex
      (LinearMap.ker
        (primitiveSpinCGeometricSignedActionHessianOperator
          period hPeriod massSquared).toFun) ∧
    FiniteDimensional Complex
      (ComplexDiagonalOperatorCokernel
        PrimitiveSpinCGeometricSignedMode
        (fun mode =>
          primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared))

/-- Unconditional geometric closure of the complete primitive SpinC sector
of the Program-P Hessian. -/
structure GlobalHessianSpinCGeometricClosure4D
    (massSquared : Real) where
  exactUnitary :
    ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter
  exactUnitary_on_single :
    ∀ mode coefficient,
      exactUnitary (lp.single 2 mode coefficient) =
        coefficient •
          primitiveSpinCGeometricSignedDiracModeVector
            period hPeriod mode
  finiteCoreIntertwining :
    ∀ coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients,
      primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod coefficients) =
        primitiveSpinCGeometricSignedDiracFiniteSynthesis period hPeriod
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared coefficients)
  coefficientSelfAdjoint :
    IsSelfAdjoint
      (primitiveSpinCGeometricSignedActionHessianOperator
        period hPeriod massSquared)
  coefficientFredholm :
    GlobalHessianSpinCGeometricFredholm4D
      period hPeriod massSquared

def globalHessianSpinCGeometricClosure4D
    (massSquared : Real) :
    GlobalHessianSpinCGeometricClosure4D
      period hPeriod massSquared where
  exactUnitary :=
    primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
  exactUnitary_on_single :=
    primitiveSpinCGeometricSignedDiracModeUnitary_single period hPeriod
  finiteCoreIntertwining :=
    primitiveSpinCGeometricSignedDiracFiniteSynthesis_intertwines_hessian
      period hPeriod massSquared
  coefficientSelfAdjoint :=
    primitiveSpinCGeometricSignedActionHessianOperator_selfAdjoint
      period hPeriod massSquared
  coefficientFredholm :=
    primitiveSpinCGeometricSignedActionHessianOperator_fredholm
      period hPeriod massSquared

theorem global_hessian_spinc_geometric_gate
    (massSquared : Real) :
    Nonempty
      (GlobalHessianSpinCGeometricClosure4D
        period hPeriod massSquared) :=
  ⟨globalHessianSpinCGeometricClosure4D
    period hPeriod massSquared⟩

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
