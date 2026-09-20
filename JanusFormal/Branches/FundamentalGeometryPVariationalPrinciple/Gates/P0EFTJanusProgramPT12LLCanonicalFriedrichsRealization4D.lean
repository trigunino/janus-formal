import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D

/-!
# Canonical Friedrichs realization of the reduced LL Jacobi operator

The positive compact response `I I†` is injective with dense range. Its inverse
on that range is a positive self-adjoint realization extending the existing
closed reduced Jacobi operator. Every nonnegative shifted weak solution belongs
to this domain and is a genuine right inverse there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12HilbertEnergyShift4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
open P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev inclusion
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  canonicalLLH1ToFluxL2 period hPeriod analysis

private abbrev response
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  canonicalLLWeakL2Inverse period hPeriod analysis

/-! ## The positive compact response -/

theorem canonicalLLWeakL2Inverse_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (source : CanonicalLLL2 period hPeriod analysis) :
    inner Real source
        (canonicalLLWeakL2Inverse period hPeriod analysis source) =
      ‖(inclusion period hPeriod analysis).adjoint source‖ ^ 2 := by
  change inner Real source
      (inclusion period hPeriod analysis
        ((inclusion period hPeriod analysis).adjoint source)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left
      (inclusion period hPeriod analysis)
      ((inclusion period hPeriod analysis).adjoint source) source,
    real_inner_self_eq_norm_sq]

theorem canonicalLLWeakL2Inverse_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (canonicalLLWeakL2Inverse period hPeriod analysis) := by
  have hInjective := energyShiftL2Solution_injective
    (inclusion period hPeriod analysis)
    (canonicalLLH1ToFluxL2_injective period hPeriod analysis)
    (canonicalLLH1ToFluxL2_denseRange period hPeriod analysis)
    0 (le_refl 0)
  simpa only [energyShiftL2Solution, energyShiftSolution_zero,
    canonicalLLWeakL2Inverse] using hInjective

theorem canonicalLLWeakL2Inverse_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsSelfAdjoint
      (canonicalLLWeakL2Inverse period hPeriod analysis) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  change inner Real
      (inclusion period hPeriod analysis
        ((inclusion period hPeriod analysis).adjoint first)) second =
    inner Real first
      (inclusion period hPeriod analysis
        ((inclusion period hPeriod analysis).adjoint second))
  calc
    _ = inner Real
        ((inclusion period hPeriod analysis).adjoint first)
        ((inclusion period hPeriod analysis).adjoint second) := by
      exact (ContinuousLinearMap.adjoint_inner_right
        (inclusion period hPeriod analysis)
        ((inclusion period hPeriod analysis).adjoint first) second).symm
    _ = _ := ContinuousLinearMap.adjoint_inner_left
      (inclusion period hPeriod analysis)
      ((inclusion period hPeriod analysis).adjoint second) first

theorem canonicalLLWeakL2Inverse_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange (canonicalLLWeakL2Inverse period hPeriod analysis) := by
  let R := response period hPeriod analysis
  have hOrthogonal :
      R.toLinearMap.rangeᗮ =
        (⊥ : Submodule Real (CanonicalLLL2 period hPeriod analysis)) := by
    rw [R.orthogonal_range,
      (canonicalLLWeakL2Inverse_isSelfAdjoint
        period hPeriod analysis).adjoint_eq]
    exact LinearMap.ker_eq_bot.mpr
      (canonicalLLWeakL2Inverse_injective period hPeriod analysis)
  have hClosure :
      R.toLinearMap.range.topologicalClosure =
        (⊤ : Submodule Real (CanonicalLLL2 period hPeriod analysis)) := by
    rw [← R.toLinearMap.range.orthogonal_orthogonal_eq_closure,
      hOrthogonal, Submodule.bot_orthogonal_eq_top]
  rw [denseRange_iff_closure_range]
  change closure
      (R.toLinearMap.range : Set (CanonicalLLL2 period hPeriod analysis)) =
    Set.univ
  rw [← Submodule.topologicalClosure_coe, hClosure]
  rfl

theorem canonicalLLWeakL2Inverse_isCompact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator
      (canonicalLLWeakL2Inverse period hPeriod analysis) := by
  change IsCompactOperator
    ((inclusion period hPeriod analysis).comp
      (inclusion period hPeriod analysis).adjoint)
  exact (canonicalLLH1ToFluxL2_isCompact period hPeriod analysis).comp_clm
    (inclusion period hPeriod analysis).adjoint

/-! ## Inverse-response realization -/

def canonicalLLFriedrichsRangeEquiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CanonicalLLL2 period hPeriod analysis ≃ₗ[Real]
      LinearMap.range
        (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap :=
  LinearEquiv.ofInjective
    (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap
    (canonicalLLWeakL2Inverse_injective period hPeriod analysis)

def canonicalLLFriedrichsJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CanonicalLLL2 period hPeriod analysis →ₗ.[Real]
      CanonicalLLL2 period hPeriod analysis where
  domain := LinearMap.range
    (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap
  toFun :=
    (canonicalLLFriedrichsRangeEquiv period hPeriod analysis).symm.toLinearMap

theorem canonicalLLFriedrichsJacobi_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).domain =
      LinearMap.range
        (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap :=
  rfl

def canonicalLLFriedrichsDomainElement
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (source : CanonicalLLL2 period hPeriod analysis) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
  ⟨canonicalLLWeakL2Inverse period hPeriod analysis source,
    LinearMap.mem_range_self
      (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap source⟩

@[simp]
theorem canonicalLLFriedrichsJacobi_on_response
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLFriedrichsJacobi period hPeriod analysis
        (canonicalLLFriedrichsDomainElement period hPeriod analysis source) =
      source := by
  change (canonicalLLFriedrichsRangeEquiv
      period hPeriod analysis).symm
        (canonicalLLFriedrichsDomainElement
          period hPeriod analysis source) = source
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  rfl

@[simp]
theorem canonicalLLWeakL2Inverse_friedrichsJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (field : (canonicalLLFriedrichsJacobi
      period hPeriod analysis).domain) :
    canonicalLLWeakL2Inverse period hPeriod analysis
        (canonicalLLFriedrichsJacobi period hPeriod analysis field) =
      (field : CanonicalLLL2 period hPeriod analysis) := by
  change (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap
      ((canonicalLLFriedrichsRangeEquiv
        period hPeriod analysis).symm field) =
    (field : CanonicalLLL2 period hPeriod analysis)
  exact LinearEquiv.ofInjective_symm_apply
    (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap field

theorem canonicalLLFriedrichsJacobi_domain_dense
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Dense
      ((canonicalLLFriedrichsJacobi
        period hPeriod analysis).domain :
          Set (CanonicalLLL2 period hPeriod analysis)) := by
  rw [canonicalLLFriedrichsJacobi_domain, LinearMap.coe_range]
  exact canonicalLLWeakL2Inverse_denseRange period hPeriod analysis

theorem canonicalLLFriedrichsJacobi_isFormalAdjoint_self
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).IsFormalAdjoint
      (canonicalLLFriedrichsJacobi period hPeriod analysis) := by
  intro first second
  have hSymmetric :
      (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap.IsSymmetric :=
    (canonicalLLWeakL2Inverse_isSelfAdjoint
      period hPeriod analysis).isSymmetric
  calc
    inner Real
        (canonicalLLFriedrichsJacobi period hPeriod analysis first)
        (second : CanonicalLLL2 period hPeriod analysis) =
      inner Real
        (canonicalLLFriedrichsJacobi period hPeriod analysis first)
        (canonicalLLWeakL2Inverse period hPeriod analysis
          (canonicalLLFriedrichsJacobi period hPeriod analysis second)) := by
      rw [canonicalLLWeakL2Inverse_friedrichsJacobi]
    _ = inner Real
        (canonicalLLWeakL2Inverse period hPeriod analysis
          (canonicalLLFriedrichsJacobi period hPeriod analysis first))
        (canonicalLLFriedrichsJacobi period hPeriod analysis second) :=
      (hSymmetric
        (canonicalLLFriedrichsJacobi period hPeriod analysis first)
        (canonicalLLFriedrichsJacobi period hPeriod analysis second)).symm
    _ = inner Real (first : CanonicalLLL2 period hPeriod analysis)
        (canonicalLLFriedrichsJacobi period hPeriod analysis second) := by
      rw [canonicalLLWeakL2Inverse_friedrichsJacobi]

theorem canonicalLLFriedrichsJacobi_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsSelfAdjoint
      (canonicalLLFriedrichsJacobi period hPeriod analysis) := by
  let A := canonicalLLFriedrichsJacobi period hPeriod analysis
  let R := response period hPeriod analysis
  have hDense : Dense
      (A.domain : Set (CanonicalLLL2 period hPeriod analysis)) :=
    canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis
  have hFormal : A.IsFormalAdjoint A :=
    canonicalLLFriedrichsJacobi_isFormalAdjoint_self
      period hPeriod analysis
  have hOperatorLeAdjoint : A ≤ A.adjoint :=
    hFormal.le_adjoint hDense
  have hResponseSymmetric : R.toLinearMap.IsSymmetric :=
    (canonicalLLWeakL2Inverse_isSelfAdjoint
      period hPeriod analysis).isSymmetric
  have hAdjointDomain : A.adjoint.domain ≤ A.domain := by
    intro state hState
    let adjointState : A.adjoint.domain := ⟨state, hState⟩
    let image : CanonicalLLL2 period hPeriod analysis :=
      A.adjoint adjointState
    change state ∈ LinearMap.range R.toLinearMap
    refine ⟨image, ?_⟩
    apply ext_inner_left Real
    intro test
    let testState : A.domain :=
      canonicalLLFriedrichsDomainElement period hPeriod analysis test
    have hInner := (LinearPMap.adjoint_isFormalAdjoint hDense).symm
      testState adjointState
    change inner Real (A testState)
        (adjointState : CanonicalLLL2 period hPeriod analysis) =
      inner Real (testState : CanonicalLLL2 period hPeriod analysis) image
        at hInner
    rw [canonicalLLFriedrichsJacobi_on_response] at hInner
    change inner Real test state = inner Real (R test) image at hInner
    calc
      inner Real test (R image) = inner Real (R test) image :=
        (hResponseSymmetric test image).symm
      _ = inner Real test state := hInner.symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

theorem canonicalLLFriedrichsJacobi_isClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).IsClosed :=
  (canonicalLLFriedrichsJacobi_isSelfAdjoint
    period hPeriod analysis).isClosed

theorem canonicalLLFriedrichsJacobi_surjective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Surjective
      (canonicalLLFriedrichsJacobi period hPeriod analysis) :=
  fun source =>
    ⟨canonicalLLFriedrichsDomainElement period hPeriod analysis source,
      canonicalLLFriedrichsJacobi_on_response
        period hPeriod analysis source⟩

theorem canonicalLLFriedrichsJacobi_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (canonicalLLFriedrichsJacobi period hPeriod analysis) := by
  intro first second hEqual
  apply Subtype.ext
  rw [← canonicalLLWeakL2Inverse_friedrichsJacobi
      period hPeriod analysis first,
    ← canonicalLLWeakL2Inverse_friedrichsJacobi
      period hPeriod analysis second,
    hEqual]

theorem canonicalLLFriedrichsJacobi_compactInverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator
      (canonicalLLWeakL2Inverse period hPeriod analysis) :=
  canonicalLLWeakL2Inverse_isCompact period hPeriod analysis

theorem canonicalLLFriedrichsJacobi_range_eq_top
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    LinearMap.range
        (canonicalLLFriedrichsJacobi period hPeriod analysis).toFun =
      (⊤ : Submodule Real (CanonicalLLL2 period hPeriod analysis)) :=
  LinearMap.range_eq_top.mpr
    (canonicalLLFriedrichsJacobi_surjective period hPeriod analysis)

theorem canonicalLLFriedrichsJacobi_ker_eq_bot
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    LinearMap.ker
        (canonicalLLFriedrichsJacobi period hPeriod analysis).toFun =
      (⊥ : Submodule Real
        (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :=
  LinearMap.ker_eq_bot.mpr
    (canonicalLLFriedrichsJacobi_injective period hPeriod analysis)

theorem canonicalLLFriedrichsJacobi_range_isClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsClosed
      (LinearMap.range
        (canonicalLLFriedrichsJacobi period hPeriod analysis).toFun :
        Set (CanonicalLLL2 period hPeriod analysis)) := by
  rw [canonicalLLFriedrichsJacobi_range_eq_top]
  exact isClosed_univ

theorem canonicalLLFriedrichsJacobi_kernel_finite
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    FiniteDimensional Real
      (LinearMap.ker
        (canonicalLLFriedrichsJacobi period hPeriod analysis).toFun) := by
  rw [canonicalLLFriedrichsJacobi_ker_eq_bot]
  infer_instance

theorem canonicalLLFriedrichsJacobi_cokernel_finite
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    FiniteDimensional Real
      ((CanonicalLLL2 period hPeriod analysis) ⧸
        LinearMap.range
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).toFun) := by
  rw [canonicalLLFriedrichsJacobi_range_eq_top]
  exact FiniteDimensional.of_rank_eq_zero (by simp)

theorem canonicalLLFriedrichsJacobi_fredholm
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsClosed
        (LinearMap.range
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).toFun :
          Set (CanonicalLLL2 period hPeriod analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (canonicalLLFriedrichsJacobi period hPeriod analysis).toFun) ∧
      FiniteDimensional Real
        ((CanonicalLLL2 period hPeriod analysis) ⧸
          LinearMap.range
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).toFun) :=
  ⟨canonicalLLFriedrichsJacobi_range_isClosed
      period hPeriod analysis,
    canonicalLLFriedrichsJacobi_kernel_finite
      period hPeriod analysis,
    canonicalLLFriedrichsJacobi_cokernel_finite
      period hPeriod analysis⟩

/-! ## Agreement with the existing graph closure -/

theorem canonicalLLClosedJacobi_le_friedrichsJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    canonicalLLClosedJacobi period hPeriod analysis ≤
      canonicalLLFriedrichsJacobi period hPeriod analysis := by
  let C := canonicalLLClosedJacobi period hPeriod analysis
  let A := canonicalLLFriedrichsJacobi period hPeriod analysis
  let R := response period hPeriod analysis
  refine ⟨?_, ?_⟩
  · intro value hValue
    let x : C.domain := ⟨value, hValue⟩
    change value ∈ LinearMap.range R.toLinearMap
    exact ⟨C x,
      canonicalLLWeakL2Inverse_closed_left_inverse
        period hPeriod analysis x⟩
  · intro x y hxy
    apply canonicalLLWeakL2Inverse_injective period hPeriod analysis
    rw [canonicalLLWeakL2Inverse_friedrichsJacobi]
    exact (canonicalLLWeakL2Inverse_closed_left_inverse
      period hPeriod analysis x).trans hxy

theorem canonicalLLSmoothJacobi_le_friedrichsJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    llJacobiSmoothPMap period hPeriod
        (analysis.llH1Data period hPeriod).fields ≤
      canonicalLLFriedrichsJacobi period hPeriod analysis :=
  le_trans
    (llJacobiSmoothPMap_le_closed period hPeriod
      (analysis.llH1Data period hPeriod).fields)
    (canonicalLLClosedJacobi_le_friedrichsJacobi
      period hPeriod analysis)

def canonicalLLFriedrichsSmoothDomainElement
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction :
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
  canonicalLLFriedrichsDomainElement period hPeriod analysis
    (llStrongJacobiToL2 period hPeriod
      (analysis.llH1Data period hPeriod).fields direction.toTest)

@[simp]
theorem canonicalLLFriedrichsJacobi_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction :
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    canonicalLLFriedrichsJacobi period hPeriod analysis
        (canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis direction) =
      llStrongJacobiToL2 period hPeriod
        (analysis.llH1Data period hPeriod).fields direction.toTest :=
  canonicalLLFriedrichsJacobi_on_response period hPeriod analysis _

theorem canonicalLLFriedrichsSmoothDomainElement_value
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction :
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    ((canonicalLLFriedrichsSmoothDomainElement
        period hPeriod analysis direction :
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).domain) :
      CanonicalLLL2 period hPeriod analysis) =
      llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) direction := by
  change inclusion period hPeriod analysis
      ((inclusion period hPeriod analysis).adjoint
        (llStrongJacobiToL2 period hPeriod
          (analysis.llH1Data period hPeriod).fields direction.toTest)) = _
  rw [canonicalLLH1ToFluxL2_adjoint_strongJacobi,
    canonicalLLH1ToFluxL2_agrees_on_smooth]

theorem canonicalLLFriedrichsJacobi_smooth_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second :
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    inner Real
        (canonicalLLFriedrichsJacobi period hPeriod analysis
          (canonicalLLFriedrichsSmoothDomainElement
            period hPeriod analysis first))
        (canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis second :
            CanonicalLLL2 period hPeriod analysis) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (analysis.llH1Data period hPeriod).frame
        (analysis.llH1Data period hPeriod).fields
        first.toTest second.toTest
        (analysis.llH1Data period hPeriod).mu := by
  rw [canonicalLLFriedrichsJacobi_on_smooth,
    canonicalLLFriedrichsSmoothDomainElement_value]
  have hPair := canonicalLLH1ToFluxL2_strong_pairing
    period hPeriod analysis first
      (llH1SmoothEmbedding period hPeriod
        (analysis.llH1Data period hPeriod) second)
  rw [canonicalLLH1ToFluxL2_agrees_on_smooth] at hPair
  have hHessian :
      inner Real
          (llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) first)
          (llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) second) =
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (analysis.llH1Data period hPeriod).frame
          (analysis.llH1Data period hPeriod).fields
          first.toTest second.toTest
          (analysis.llH1Data period hPeriod).mu := by
    change weakLLJacobiH1Extension period hPeriod
      (analysis.llH1Data period hPeriod) first
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) second) = _
    exact weakLLJacobiH1Extension_apply_smooth
      period hPeriod (analysis.llH1Data period hPeriod) first second
  exact hPair.symm.trans hHessian

/-! ## Nonnegative shifted weak solutions -/

def canonicalLLFriedrichsShiftedJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) :
    CanonicalLLL2 period hPeriod analysis →ₗ.[Real]
      CanonicalLLL2 period hPeriod analysis :=
  let A := canonicalLLFriedrichsJacobi period hPeriod analysis
  ⟨A.domain, A.toFun + shift • A.domain.subtype⟩

theorem canonicalLLFriedrichsShiftedJacobi_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real)
    (field : (canonicalLLFriedrichsJacobi
      period hPeriod analysis).domain) :
    canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift field =
      canonicalLLFriedrichsJacobi period hPeriod analysis field +
        shift • (field : CanonicalLLL2 period hPeriod analysis) := by
  simp [canonicalLLFriedrichsShiftedJacobi]

theorem canonicalLLWeakL2Inverse_shifted_residual
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLWeakL2Inverse period hPeriod analysis
        (source - shift •
          canonicalLLShiftedWeakL2Solution
            period hPeriod analysis shift hShift source) =
      canonicalLLShiftedWeakL2Solution
        period hPeriod analysis shift hShift source := by
  let I := inclusion period hPeriod analysis
  let w := canonicalLLShiftedWeakH1Solution
    period hPeriod analysis shift hShift source
  let u := canonicalLLShiftedWeakL2Solution
    period hPeriod analysis shift hShift source
  let residual := source - shift • u
  have hWeak : ∀ v : CanonicalLLEnergy period hPeriod analysis,
      inner Real w v + shift * inner Real u (I v) =
        inner Real source (I v) :=
    canonicalLLShiftedWeakH1Solution_pairing
      period hPeriod analysis shift hShift source
  have hAdjoint : w = I.adjoint residual := by
    apply ext_inner_right Real
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    calc
      inner Real w v =
          inner Real source (I v) - shift * inner Real u (I v) :=
        eq_sub_of_add_eq (hWeak v)
      _ = inner Real residual (I v) := by
        simp [residual, inner_sub_left, real_inner_smul_left]
  change I (I.adjoint residual) = u
  rw [← hAdjoint]
  rfl

theorem canonicalLLShiftedWeakL2Solution_mem_friedrichsDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLShiftedWeakL2Solution
        period hPeriod analysis shift hShift source ∈
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain := by
  rw [canonicalLLFriedrichsJacobi_domain]
  exact ⟨source - shift •
      canonicalLLShiftedWeakL2Solution
        period hPeriod analysis shift hShift source,
    canonicalLLWeakL2Inverse_shifted_residual
      period hPeriod analysis shift hShift source⟩

def canonicalLLFriedrichsShiftedWeakDomainElement
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
  ⟨canonicalLLShiftedWeakL2Solution
      period hPeriod analysis shift hShift source,
    canonicalLLShiftedWeakL2Solution_mem_friedrichsDomain
      period hPeriod analysis shift hShift source⟩

theorem canonicalLLFriedrichsJacobi_shiftedWeak_action
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLFriedrichsJacobi period hPeriod analysis
        (canonicalLLFriedrichsShiftedWeakDomainElement
          period hPeriod analysis shift hShift source) =
      source - shift •
        canonicalLLShiftedWeakL2Solution
          period hPeriod analysis shift hShift source := by
  apply canonicalLLWeakL2Inverse_injective period hPeriod analysis
  rw [canonicalLLWeakL2Inverse_friedrichsJacobi]
  exact (canonicalLLWeakL2Inverse_shifted_residual
    period hPeriod analysis shift hShift source).symm

theorem canonicalLLFriedrichsShiftedJacobi_right_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift
        (canonicalLLFriedrichsShiftedWeakDomainElement
          period hPeriod analysis shift hShift source) =
      source := by
  rw [canonicalLLFriedrichsShiftedJacobi_apply,
    canonicalLLFriedrichsJacobi_shiftedWeak_action]
  change
    (source - shift •
        canonicalLLShiftedWeakL2Solution
          period hPeriod analysis shift hShift source) +
      shift • canonicalLLShiftedWeakL2Solution
        period hPeriod analysis shift hShift source = source
  abel

theorem canonicalLLFriedrichsShiftedJacobi_surjective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Surjective
      (canonicalLLFriedrichsShiftedJacobi
        period hPeriod analysis shift) :=
  fun source =>
    ⟨canonicalLLFriedrichsShiftedWeakDomainElement
        period hPeriod analysis shift hShift source,
      canonicalLLFriedrichsShiftedJacobi_right_inverse
        period hPeriod analysis shift hShift source⟩

theorem canonicalLLFriedrichsJacobi_certificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Dense
        ((canonicalLLFriedrichsJacobi
          period hPeriod analysis).domain :
            Set (CanonicalLLL2 period hPeriod analysis)) ∧
      IsSelfAdjoint
        (canonicalLLFriedrichsJacobi period hPeriod analysis) ∧
      (canonicalLLFriedrichsJacobi period hPeriod analysis).IsClosed ∧
      Function.Bijective
        (canonicalLLFriedrichsJacobi period hPeriod analysis) ∧
      IsCompactOperator
        (canonicalLLWeakL2Inverse period hPeriod analysis) ∧
      canonicalLLClosedJacobi period hPeriod analysis ≤
        canonicalLLFriedrichsJacobi period hPeriod analysis ∧
      ∀ shift : Real, 0 ≤ shift →
        Function.Surjective
          (canonicalLLFriedrichsShiftedJacobi
            period hPeriod analysis shift) := by
  exact
    ⟨canonicalLLFriedrichsJacobi_domain_dense
        period hPeriod analysis,
      canonicalLLFriedrichsJacobi_isSelfAdjoint
        period hPeriod analysis,
      canonicalLLFriedrichsJacobi_isClosed
        period hPeriod analysis,
      ⟨canonicalLLFriedrichsJacobi_injective
          period hPeriod analysis,
        canonicalLLFriedrichsJacobi_surjective
          period hPeriod analysis⟩,
      canonicalLLFriedrichsJacobi_compactInverse
        period hPeriod analysis,
      canonicalLLClosedJacobi_le_friedrichsJacobi
        period hPeriod analysis,
      fun shift hShift =>
        canonicalLLFriedrichsShiftedJacobi_surjective
          period hPeriod analysis shift hShift⟩

end
end P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
end JanusFormal
