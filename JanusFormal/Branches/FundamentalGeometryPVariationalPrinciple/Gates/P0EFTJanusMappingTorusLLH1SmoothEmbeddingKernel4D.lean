import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

/-! Exact kernel consequences of the canonical smooth inclusion into the intrinsic LL H1 completion. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem llH1SmoothEmbedding_injective (data : PositiveLLH1Data period hPeriod) :
    Function.Injective (llH1SmoothEmbedding period hPeriod data) := by
  intro first second h
  change (first : LLH1Space period hPeriod data) = (second : LLH1Space period hPeriod data) at h
  exact UniformSpace.Completion.coe_injective _ h

theorem llH1SmoothEmbedding_eq_zero_iff (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    llH1SmoothEmbedding period hPeriod data direction = 0 ↔ direction = 0 := by
  constructor
  · intro h
    apply llH1SmoothEmbedding_injective period hPeriod data
    simpa using h
  · rintro rfl
    exact map_zero _

theorem llH1SmoothEmbedding_eq_zero_consequences (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data)
    (h : llH1SmoothEmbedding period hPeriod data direction = 0) :
    direction.toTest = 0 ∧ ‖direction‖ = 0 ∧
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) data.fields
        direction.toTest direction.toTest data.mu = 0 := by
  have hdirection := (llH1SmoothEmbedding_eq_zero_iff period hPeriod data direction).mp h
  subst direction
  refine ⟨LLH1Smooth.toTest_zero period hPeriod data, norm_zero, ?_⟩
  rw [← llH1Smooth_inner period hPeriod data (0 : LLH1Smooth period hPeriod data) 0]
  simp

end
end P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
end JanusFormal
