import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLHessianFredholm4D

/-!
# Unbounded global Hessian realization

A differential Hessian is naturally a densely defined closed operator, not
a bounded endomorphism of the whole ambient Hilbert space.  This gate promotes
the corrected D10-free gauge/ghost + primitive SpinC + LL analytic target
directly through Mathlib's `LinearPMap`.  The smooth gauge quotient maps into
its genuine operator domain, and the Hessian pairing is tested against the
ambient inclusion of that domain.  The remaining core-agreement datum is not
claimed here for the still-missing global gauge-fixed action blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianUnboundedRealization4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPGlobalGaugeFixedLLHessianFredholm4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
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

local instance programPGlobalGaugeFixedLLHessianHilbertRealLinearPMapStar
    (ι : Type*)
    (llData : PositiveLLH1Data period hPeriod) :
    Star (ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData) :=
  LinearPMap.instStar

/-- Honest terminal analytic realization of the gauge-reduced Hessian.
The operator domain is the maximal domain carried by `operator`; no bounded
extension to all of `Analysis` is required. -/
structure ProgramPGlobalHessianUnboundedFredholmRealization4D
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
  operator : Analysis →ₗ.[Real] Analysis
  operator_domain_dense : Dense (operator.domain : Set Analysis)
  operator_selfAdjoint : IsSelfAdjoint operator
  operator_range_closed :
    IsClosed (LinearMap.range operator.toFun : Set Analysis)
  operator_kernel_finite :
    FiniteDimensional Real (LinearMap.ker operator.toFun)
  operator_cokernel_finite :
    FiniteDimensional Real
      (Analysis ⧸ LinearMap.range operator.toFun)
  smoothCore :
    (chart.Configuration ⧸ totalGaugeDirections) →ₗ[Real]
      operator.domain
  smoothCore_injective : Function.Injective smoothCore
  smoothCore_denseRange :
    DenseRange (fun state => ((smoothCore state : operator.domain) : Analysis))
  pairing_agreement : ∀ first second,
    inner Real
        (operator (smoothCore first))
        ((smoothCore second : operator.domain) : Analysis) =
      quotientHessian
        (globalCandidateAHessianLinear period hPeriod chart configuration)
        totalGaugeDirections hessianGaugeLeft hessianGaugeRight first second

theorem
    ProgramPGlobalHessianUnboundedFredholmRealization4D.operator_isClosed
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {symmetry : GlobalCandidateAGhostSymmetry period hPeriod chart}
    {configuration : chart.Configuration}
    {Analysis : Type*}
    [NormedAddCommGroup Analysis]
    [InnerProductSpace Real Analysis]
    [CompleteSpace Analysis]
    (realization :
      ProgramPGlobalHessianUnboundedFredholmRealization4D
        period hPeriod chart symmetry configuration Analysis) :
    realization.operator.IsClosed :=
  realization.operator_selfAdjoint.isClosed

/-- A zero quotient Hessian is incompatible with the advertised unbounded
Fredholm realization on an infinite-dimensional Hilbert completion. -/
theorem
    no_globalHessianUnboundedFredholmRealization_of_zero_quotientHessian
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
      ProgramPGlobalHessianUnboundedFredholmRealization4D
        period hPeriod chart physical configuration Analysis)
    (hZero : ∀ first second,
      quotientHessian
          (globalCandidateAHessianLinear
            period hPeriod chart configuration)
          realization.totalGaugeDirections
          realization.hessianGaugeLeft realization.hessianGaugeRight
          first second =
        0) :
    False := by
  have hOperatorCore :
      ∀ state, realization.operator (realization.smoothCore state) = 0 := by
    intro state
    apply realization.smoothCore_denseRange.eq_zero_of_inner_left
      (𝕜 := Real)
    intro test
    rw [realization.pairing_agreement, hZero]
  have hFormalAdjoint :
      realization.operator.IsFormalAdjoint realization.operator := by
    have hAdjoint :=
      LinearPMap.adjoint_isFormalAdjoint
        realization.operator_selfAdjoint.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp
      realization.operator_selfAdjoint] at hAdjoint
    exact hAdjoint
  have hOperatorDomain :
      ∀ state : realization.operator.domain,
        realization.operator state = 0 := by
    intro state
    apply realization.smoothCore_denseRange.eq_zero_of_inner_left
      (𝕜 := Real)
    intro test
    rw [hFormalAdjoint state (realization.smoothCore test),
      hOperatorCore, inner_zero_right]
  have hKernelTop :
      LinearMap.ker realization.operator.toFun =
        (⊤ : Submodule Real realization.operator.domain) := by
    ext state
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact hOperatorDomain state
  letI : FiniteDimensional Real
      (⊤ : Submodule Real realization.operator.domain) := by
    rw [← hKernelTop]
    exact realization.operator_kernel_finite
  letI : FiniteDimensional Real realization.operator.domain :=
    (Submodule.topEquiv :
      (⊤ : Submodule Real realization.operator.domain) ≃ₗ[Real]
        realization.operator.domain).finiteDimensional
  have hDomainTop :
      realization.operator.domain = (⊤ : Submodule Real Analysis) := by
    exact
      realization.operator.domain.closed_of_finiteDimensional
        |>.submodule_topologicalClosure_eq.symm.trans
          (Submodule.dense_iff_topologicalClosure_eq_top.mp
            realization.operator_domain_dense)
  letI : FiniteDimensional Real (⊤ : Submodule Real Analysis) := by
    rw [← hDomainTop]
    infer_instance
  apply hInfinite
  exact
    (Submodule.topEquiv :
      (⊤ : Submodule Real Analysis) ≃ₗ[Real] Analysis).finiteDimensional

/-- Residual agreement datum after choosing an exact additional gauge
symmetry and the constructed D10-free real Fredholm operator.  It still
requires a dense smooth quotient core and the exact Hessian pairing identity;
the structure does not assert that the current action supplies the global
Lorenz/de Donder, typed nonminimal, or other omitted physical blocks. -/
structure ProgramPGlobalHessianCombinedGaugeSpectralCoreAgreement4D
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
    (analysisData :
      GlobalAnalysisData period hPeriod
        (chart.family.configurationAt configuration))
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  smoothCore :
    (chart.Configuration ⧸
      globalCandidateACombinedGaugeDirectionSubmodule
        period hPeriod chart physical additional) →ₗ[Real]
      (programPGlobalGaugeFixedLLHessianOperator period hPeriod covector
        couplings.matterMassSquared
        (analysisData.llH1Data period hPeriod)).domain
  smoothCore_injective : Function.Injective smoothCore
  smoothCore_denseRange :
    DenseRange (fun state =>
      ((smoothCore state :
        (programPGlobalGaugeFixedLLHessianOperator period hPeriod covector
          couplings.matterMassSquared
          (analysisData.llH1Data period hPeriod)).domain) :
        ProgramPGlobalGaugeFixedLLHessianHilbert period hPeriod ι
          (analysisData.llH1Data period hPeriod)))
  pairing_agreement : ∀ first second,
    inner Real
        (programPGlobalGaugeFixedLLHessianOperator period hPeriod covector
          couplings.matterMassSquared
          (analysisData.llH1Data period hPeriod) (smoothCore first))
        ((smoothCore second :
          (programPGlobalGaugeFixedLLHessianOperator period hPeriod covector
            couplings.matterMassSquared
            (analysisData.llH1Data period hPeriod)).domain) :
          ProgramPGlobalGaugeFixedLLHessianHilbert period hPeriod ι
            (analysisData.llH1Data period hPeriod)) =
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

/-- Promotion theorem: the spectral construction discharges density,
self-adjointness, closed range and finite kernel/cokernel. -/
def ProgramPGlobalHessianCombinedGaugeSpectralCoreAgreement4D.toRealization
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
    {analysisData :
      GlobalAnalysisData period hPeriod
        (chart.family.configurationAt configuration)}
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    {d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (agreement :
      ProgramPGlobalHessianCombinedGaugeSpectralCoreAgreement4D
        period hPeriod chart physical additional configuration analysisData
        d9Ellipticity) :
    ProgramPGlobalHessianUnboundedFredholmRealization4D
      period hPeriod chart physical configuration
        (ProgramPGlobalGaugeFixedLLHessianHilbert period hPeriod ι
          (analysisData.llH1Data period hPeriod)) where
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
  operator :=
    programPGlobalGaugeFixedLLHessianOperator period hPeriod covector
      couplings.matterMassSquared (analysisData.llH1Data period hPeriod)
  operator_domain_dense :=
    programPGlobalGaugeFixedLLHessian_domain_dense period hPeriod covector
      couplings.matterMassSquared (analysisData.llH1Data period hPeriod)
  operator_selfAdjoint :=
    programPGlobalGaugeFixedLLHessian_selfAdjoint period hPeriod covector
      couplings.matterMassSquared (analysisData.llH1Data period hPeriod)
  operator_range_closed :=
    (programPGlobalGaugeFixedLLHessian_fredholm
      period hPeriod d9Ellipticity
        couplings.matterMassSquared
        (analysisData.llH1Data period hPeriod)).1
  operator_kernel_finite :=
    (programPGlobalGaugeFixedLLHessian_fredholm
      period hPeriod d9Ellipticity
        couplings.matterMassSquared
        (analysisData.llH1Data period hPeriod)).2.1
  operator_cokernel_finite :=
    (programPGlobalGaugeFixedLLHessian_fredholm
      period hPeriod d9Ellipticity
        couplings.matterMassSquared
        (analysisData.llH1Data period hPeriod)).2.2
  smoothCore := agreement.smoothCore
  smoothCore_injective := agreement.smoothCore_injective
  smoothCore_denseRange := agreement.smoothCore_denseRange
  pairing_agreement := agreement.pairing_agreement

/-- Diffeomorphism-specialized form of the final core agreement.  Once the
nine-block diffeomorphism symmetry is constructed, no separate gauge or
Fredholm hypothesis remains. -/
abbrev ProgramPGlobalHessianDiffeomorphismSpectralCoreAgreement4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (physical : GlobalCandidateAGhostSymmetry period hPeriod chart)
    (diffeomorphism :
      GlobalCandidateADiffeomorphismGaugeSymmetry period hPeriod chart)
    (configuration : chart.Configuration)
    (analysisData :
      GlobalAnalysisData period hPeriod
        (chart.family.configurationAt configuration))
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector) :=
  ProgramPGlobalHessianCombinedGaugeSpectralCoreAgreement4D
    period hPeriod chart physical diffeomorphism configuration analysisData
      d9Ellipticity

/-- The former bounded realization remains a special case target only.
Every genuinely differential realization should use the unbounded structure
above; no upper symbol bound is part of its Fredholm obligation. -/
abbrev LegacyProgramPGlobalHessianBoundedFredholmRealization4D :=
  ProgramPGlobalHessianFredholmRealization4D

end
end P0EFTJanusProgramPGlobalHessianUnboundedRealization4D
end JanusFormal
