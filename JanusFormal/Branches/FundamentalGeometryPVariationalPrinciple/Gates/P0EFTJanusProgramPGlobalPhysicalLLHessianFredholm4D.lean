import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearPMapProdIdentityFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

/-!
# Legacy D10-extended spectral target with the exact LL energy block

The first-order D9/matter/D10 Fredholm operator is enlarged by the identity
Riesz representative on the completed LL energy space.  The LL frame is part
of the positive H1 data, so the global data can select the same canonical
divergence-free frame as the unchanged action.

Only the LL summand is identified here with the unchanged action Hessian.
Because D10 is not an action field, this extended operator remains a
regulator-compatible target rather than the physical global Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalPhysicalLLHessianFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open MeasureTheory
open scoped ENNReal lp LinearPMap
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D
open P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

local instance
    physicalSpectralModeDecidableEq
    (ι : Type*) [DecidableEq ι]
    (spectralData : ProductThroatSpectralData) :
    DecidableEq
      (ProgramPGlobalPhysicalSpectralHessianMode ι spectralData) :=
  Classical.decEq _

local instance
    physicalHilbertRealLinearPMapStar
    (ι : Type*) (spectralData : ProductThroatSpectralData) :
    Star (ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData →ₗ.[Real]
      ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData) :=
  LinearPMap.instStar

/-- Hilbert sum of the physical spectral block and the exact LL energy
completion. -/
abbrev ProgramPGlobalPhysicalLLHessianHilbert
    (ι : Type*)
    (spectralData : ProductThroatSpectralData)
    (llData : PositiveLLH1Data period hPeriod) :=
  WithLp 2
    (ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData ×
      LLH1Space period hPeriod llData)

local instance
    physicalLLHilbertRealLinearPMapStar
    (ι : Type*) (spectralData : ProductThroatSpectralData)
    (llData : PositiveLLH1Data period hPeriod) :
    Star (ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData →ₗ.[Real]
      ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData) :=
  LinearPMap.instStar

/-- Maximal first-order physical operator with the exact LL identity block. -/
abbrev programPGlobalPhysicalLLHessianOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData →ₗ.[Real]
      ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData :=
  linearPMapProdIdentity
    (F := LLH1Space period hPeriod llData)
    (programPGlobalPhysicalSpectralHessianRealMaximalOperator
      period hPeriod covector spectralData matterMass)

/-- Smooth LL directions embedded in the LL factor of the global operator
domain. -/
def programPGlobalPhysicalLLHessianLLCore
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod llData →ₗ[Real]
      (programPGlobalPhysicalLLHessianOperator
        period hPeriod covector spectralData matterMass llData).domain where
  toFun := fun direction =>
    ⟨WithLp.toLp 2
      (0, llH1SmoothEmbedding period hPeriod llData direction), by
    exact ⟨Submodule.zero_mem _, Submodule.mem_top⟩⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    change WithLp.toLp 2
        ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
          llH1SmoothEmbedding period hPeriod llData (first + second)) =
      WithLp.toLp 2
          ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
            llH1SmoothEmbedding period hPeriod llData first) +
        WithLp.toLp 2
          ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
            llH1SmoothEmbedding period hPeriod llData second)
    rw [map_add, ← WithLp.toLp_add]
    simp
  map_smul' := by
    intro scalar direction
    apply Subtype.ext
    change WithLp.toLp 2
        ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
          llH1SmoothEmbedding period hPeriod llData (scalar • direction)) =
      scalar • WithLp.toLp 2
        ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
          llH1SmoothEmbedding period hPeriod llData direction)
    rw [map_smul, ← WithLp.toLp_smul]
    simp

@[simp]
theorem programPGlobalPhysicalLLHessianLLCore_coe
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod llData) :
    (((programPGlobalPhysicalLLHessianLLCore
        period hPeriod covector spectralData matterMass llData direction :
      (programPGlobalPhysicalLLHessianOperator
        period hPeriod covector spectralData matterMass llData).domain) :
      ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData)) =
      WithLp.toLp 2
        ((0 : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData),
          llH1SmoothEmbedding period hPeriod llData direction) :=
  rfl

/-- On the smooth LL core, the added identity block represents exactly the
selected framed PT-symmetric LL Hessian. -/
theorem programPGlobalPhysicalLLHessian_LL_pairing
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod llData) :
    inner Real
        (programPGlobalPhysicalLLHessianOperator
          period hPeriod covector spectralData matterMass llData
          (programPGlobalPhysicalLLHessianLLCore
            period hPeriod covector spectralData matterMass llData direction))
        ((programPGlobalPhysicalLLHessianLLCore
          period hPeriod covector spectralData matterMass llData test :
            (programPGlobalPhysicalLLHessianOperator
              period hPeriod covector spectralData matterMass llData).domain) :
          ProgramPGlobalPhysicalLLHessianHilbert
            period hPeriod ι spectralData llData) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        llData.frame llData.fields direction.toTest test.toTest llData.mu := by
  unfold programPGlobalPhysicalLLHessianOperator
  have hApply :=
    linearPMapProdIdentity_apply
      (F := LLH1Space period hPeriod llData)
      (programPGlobalPhysicalSpectralHessianRealMaximalOperator
        period hPeriod covector spectralData matterMass)
      (programPGlobalPhysicalLLHessianLLCore
        period hPeriod covector spectralData matterMass llData direction)
  rw [hApply, WithLp.prod_inner_apply]
  simp only [programPGlobalPhysicalLLHessianLLCore_coe,
    inner_zero_right, zero_add]
  rw [llH1SmoothEmbedding_apply, llH1SmoothEmbedding_apply,
    UniformSpace.Completion.inner_coe]
  exact llH1Smooth_inner period hPeriod llData direction test

/-- Consequently the LL block is the actual mixed Hessian of the unchanged
PT-symmetric LL action, not an auxiliary quadratic form. -/
theorem programPGlobalPhysicalLLHessian_LL_actualAction_pairing
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod llData) :
    inner Real
        (programPGlobalPhysicalLLHessianOperator
          period hPeriod covector spectralData matterMass llData
          (programPGlobalPhysicalLLHessianLLCore
            period hPeriod covector spectralData matterMass llData direction))
        ((programPGlobalPhysicalLLHessianLLCore
          period hPeriod covector spectralData matterMass llData test :
            (programPGlobalPhysicalLLHessianOperator
              period hPeriod covector spectralData matterMass llData).domain) :
          ProgramPGlobalPhysicalLLHessianHilbert
            period hPeriod ι spectralData llData) =
      globalPTSymmetricDifferentialLLActionMixedHessian period hPeriod
        llData.frame llData.fields direction.toTest test.toTest llData.mu := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [globalPTSymmetricDifferentialLLActionMixedHessian_eq_fluxHessian]
  exact programPGlobalPhysicalLLHessian_LL_pairing
    period hPeriod covector spectralData matterMass llData direction test

theorem programPGlobalPhysicalLLHessian_domain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    Dense
      ((programPGlobalPhysicalLLHessianOperator
        period hPeriod covector spectralData matterMass llData).domain :
        Set (ProgramPGlobalPhysicalLLHessianHilbert
          period hPeriod ι spectralData llData)) :=
  linearPMapProdIdentity_domain_dense
    (F := LLH1Space period hPeriod llData)
    (programPGlobalPhysicalSpectralHessianRealMaximalOperator
      period hPeriod covector spectralData matterMass)
    (programPGlobalPhysicalSpectralHessianRealDomain_dense
      period hPeriod covector spectralData matterMass)

theorem programPGlobalPhysicalLLHessian_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint
      (programPGlobalPhysicalLLHessianOperator
        period hPeriod covector spectralData matterMass llData) := by
  apply linearPMapProdIdentity_selfAdjoint
  exact complexDiagonalNativeRealOperator_isSelfAdjoint
    (ProgramPGlobalPhysicalSpectralHessianMode ι spectralData)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector spectralData matterMass)

theorem programPGlobalPhysicalLLHessian_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    (programPGlobalPhysicalLLHessianOperator
      period hPeriod covector spectralData matterMass llData).IsClosed :=
  (programPGlobalPhysicalLLHessian_selfAdjoint
    period hPeriod covector spectralData matterMass llData).isClosed

theorem programPGlobalPhysicalLLHessian_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    IsClosed
        (LinearMap.range
          (programPGlobalPhysicalLLHessianOperator
            period hPeriod covector spectralData matterMass llData).toFun :
          Set (ProgramPGlobalPhysicalLLHessianHilbert
            period hPeriod ι spectralData llData)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalPhysicalLLHessianOperator
            period hPeriod covector spectralData matterMass llData).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalPhysicalLLHessianHilbert
            period hPeriod ι spectralData llData ⧸
          LinearMap.range
            (programPGlobalPhysicalLLHessianOperator
              period hPeriod covector spectralData matterMass llData).toFun) :=
  linearPMapProdIdentity_fredholm
    (F := LLH1Space period hPeriod llData)
    (programPGlobalPhysicalSpectralHessianRealMaximalOperator
      period hPeriod covector spectralData matterMass)
    (programPGlobalPhysicalSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity spectralData matterMass)

end
end P0EFTJanusProgramPGlobalPhysicalLLHessianFredholm4D
end JanusFormal
