import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Index zero for the physical Friedrichs fibres

A self-adjoint partial operator identifies its kernel with the orthogonal
complement of its range.  Closed range then identifies the cokernel with the
same finite-dimensional space, so its Fredholm index vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalIndexZero4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

theorem linearPMap_selfAdjoint_isFormalAdjoint
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    operator.IsFormalAdjoint operator := by
  have hFormal :=
    LinearPMap.adjoint_isFormalAdjoint hSelfAdjoint.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hSelfAdjoint] at hFormal

theorem linearPMap_selfAdjoint_mem_domain_of_mem_range_orthogonal
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {state : E}
    (hState : state ∈ (LinearMap.range operator.toFun)ᗮ) :
    state ∈ operator.domain := by
  have hOrthogonal :
      ∀ image, image ∈ LinearMap.range operator.toFun →
        inner Real state image = 0 := by
    rwa [Submodule.mem_orthogonal'] at hState
  have hAdjointDomain : state ∈ operator.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨0, ?_⟩
    intro source
    rw [inner_zero_left]
    exact (hOrthogonal (operator source) ⟨source, rfl⟩).symm
  rw [LinearPMap.isSelfAdjoint_def.mp hSelfAdjoint] at hAdjointDomain
  exact hAdjointDomain

theorem linearPMap_selfAdjoint_apply_eq_zero_of_mem_range_orthogonal
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (state : (LinearMap.range operator.toFun)ᗮ) :
    operator ⟨state.1,
      linearPMap_selfAdjoint_mem_domain_of_mem_range_orthogonal
        operator hSelfAdjoint state.2⟩ = 0 := by
  have hOrthogonal :
      ∀ image, image ∈ LinearMap.range operator.toFun →
        inner Real state.1 image = 0 := by
    exact
      (Submodule.mem_orthogonal'
        (LinearMap.range operator.toFun) state.1).mp state.2
  let domainState : operator.domain :=
    ⟨state.1,
      linearPMap_selfAdjoint_mem_domain_of_mem_range_orthogonal
        operator hSelfAdjoint state.2⟩
  apply hSelfAdjoint.dense_domain.eq_zero_of_inner_left (𝕜 := Real)
  intro test hTest
  let domainTest : operator.domain := ⟨test, hTest⟩
  calc
    inner Real (operator domainState) test =
        inner Real (domainState : E) (operator domainTest) :=
      linearPMap_selfAdjoint_isFormalAdjoint operator hSelfAdjoint
        domainState domainTest
    _ = 0 := hOrthogonal (operator domainTest) ⟨domainTest, rfl⟩

/-- The kernel of a self-adjoint partial operator is canonically equivalent
to the orthogonal complement of its range. -/
def linearPMapSelfAdjointKernelEquivRangeOrthogonal
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    LinearMap.ker operator.toFun ≃ₗ[Real]
      (LinearMap.range operator.toFun)ᗮ where
  toFun state := ⟨state.1.1, by
    rw [Submodule.mem_orthogonal']
    intro image hImage
    obtain ⟨source, rfl⟩ := hImage
    calc
      inner Real state.1.1 (operator source) =
          inner Real (operator source) state.1.1 := real_inner_comm _ _
      _ = inner Real source.1 (operator state.1) :=
        linearPMap_selfAdjoint_isFormalAdjoint operator hSelfAdjoint
          source state.1
      _ = 0 := by
        have hZero := LinearMap.mem_ker.mp state.2
        change operator state.1 = 0 at hZero
        rw [hZero, inner_zero_right]
    ⟩
  invFun state :=
    ⟨⟨state.1,
        linearPMap_selfAdjoint_mem_domain_of_mem_range_orthogonal
          operator hSelfAdjoint state.2⟩,
      LinearMap.mem_ker.mpr
        (linearPMap_selfAdjoint_apply_eq_zero_of_mem_range_orthogonal
          operator hSelfAdjoint state)⟩
  left_inv state := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv state := by
    apply Subtype.ext
    rfl
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar state := by
    apply Subtype.ext
    rfl

/-- A self-adjoint partial operator with closed range and finite kernel has
Fredholm index zero. -/
theorem linearPMap_selfAdjoint_index_zero
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (LinearMap.range operator.toFun : Set E))
    [FiniteDimensional Real (LinearMap.ker operator.toFun)] :
    operator.toFun.index = 0 := by
  letI : CompleteSpace (LinearMap.range operator.toFun) :=
    hClosed.completeSpace_coe
  letI : FiniteDimensional Real (LinearMap.range operator.toFun)ᗮ :=
    (linearPMapSelfAdjointKernelEquivRangeOrthogonal
      operator hSelfAdjoint).finiteDimensional
  letI : FiniteDimensional Real
      (E ⧸ LinearMap.range operator.toFun) :=
    (LinearMap.range operator.toFun).quotientEquivOrthogonal.symm.toLinearEquiv.finiteDimensional
  have hFinrank :
      Module.finrank Real (E ⧸ LinearMap.range operator.toFun) =
        Module.finrank Real (LinearMap.ker operator.toFun) := by
    calc
      Module.finrank Real (E ⧸ LinearMap.range operator.toFun) =
          Module.finrank Real (LinearMap.range operator.toFun)ᗮ :=
        (LinearMap.range operator.toFun).quotientEquivOrthogonal.toLinearEquiv.finrank_eq
      _ = Module.finrank Real (LinearMap.ker operator.toFun) :=
        (linearPMapSelfAdjointKernelEquivRangeOrthogonal
          operator hSelfAdjoint).symm.finrank_eq
  rw [LinearMap.index_eq_finrank_sub, hFinrank, sub_self]

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
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- Every physical Friedrichs fibre has Fredholm index zero. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_index_zero
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).toFun.index = 0 := by
  have hFredholm :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_fredholm
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  exact @linearPMap_selfAdjoint_index_zero
    _ _ _ _
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter)
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_selfAdjoint
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter)
    hFredholm.1 hFredholm.2.1

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalIndexZero4D
end JanusFormal
