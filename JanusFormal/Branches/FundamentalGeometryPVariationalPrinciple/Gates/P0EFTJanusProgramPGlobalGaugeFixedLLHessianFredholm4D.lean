import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearPMapProdIdentityFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

/-!
# D10-free spectral target with the exact LL energy block

The D9 gauge--ghost/matter spectral Fredholm operator is enlarged by the identity
Riesz representative on the completed LL energy space.  No D10 mode is
introduced.  On smooth LL directions, the added block is exactly the mixed
Hessian of the unchanged PT-symmetric LL action.  Only this LL summand has
the same-action identification here; the remaining global action/chart
agreement is not claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedLLHessianFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open MeasureTheory
open scoped ENNReal lp LinearPMap
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusComplexDiagonalNativeRealSelfAdjoint4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

local instance gaugeFixedSpectralModeDecidableEq
    (ι : Type*) [DecidableEq ι] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode ι) :=
  Classical.decEq _

local instance gaugeFixedHilbertRealLinearPMapStar
    (ι : Type*) :
    Star (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι →ₗ.[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) :=
  LinearPMap.instStar

/-- Hilbert sum of the D10-free spectral block and the exact LL
energy completion. -/
abbrev ProgramPGlobalGaugeFixedLLHessianHilbert
    (ι : Type*)
    (llData : PositiveLLH1Data period hPeriod) :=
  WithLp 2
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι ×
      LLH1Space period hPeriod llData)

local instance gaugeFixedLLHilbertRealLinearPMapStar
    (ι : Type*)
    (llData : PositiveLLH1Data period hPeriod) :
    Star (ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData) :=
  LinearPMap.instStar

/-- Maximal D10-free spectral operator with the exact LL identity block. -/
abbrev programPGlobalGaugeFixedLLHessianOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData :=
  linearPMapProdIdentity
    (F := LLH1Space period hPeriod llData)
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass)

/-- Smooth LL directions embedded in the LL factor of the global operator
domain. -/
def programPGlobalGaugeFixedLLHessianLLCore
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod llData →ₗ[Real]
      (programPGlobalGaugeFixedLLHessianOperator
        period hPeriod covector matterMass llData).domain where
  toFun := fun direction =>
    ⟨WithLp.toLp 2
      (0, llH1SmoothEmbedding period hPeriod llData direction), by
    exact ⟨Submodule.zero_mem _, Submodule.mem_top⟩⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    change WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
          llH1SmoothEmbedding period hPeriod llData (first + second)) =
      WithLp.toLp 2
          ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
            llH1SmoothEmbedding period hPeriod llData first) +
        WithLp.toLp 2
          ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
            llH1SmoothEmbedding period hPeriod llData second)
    rw [map_add, ← WithLp.toLp_add]
    simp
  map_smul' := by
    intro scalar direction
    apply Subtype.ext
    change WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
          llH1SmoothEmbedding period hPeriod llData (scalar • direction)) =
      scalar • WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
          llH1SmoothEmbedding period hPeriod llData direction)
    rw [map_smul, ← WithLp.toLp_smul]
    simp

@[simp]
theorem programPGlobalGaugeFixedLLHessianLLCore_coe
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod llData) :
    (((programPGlobalGaugeFixedLLHessianLLCore
        period hPeriod covector matterMass llData direction :
      (programPGlobalGaugeFixedLLHessianOperator
        period hPeriod covector matterMass llData).domain) :
      ProgramPGlobalGaugeFixedLLHessianHilbert
        period hPeriod ι llData)) =
      WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι),
          llH1SmoothEmbedding period hPeriod llData direction) :=
  rfl

/-- On the smooth LL core, the identity block represents exactly the selected
framed PT-symmetric LL Hessian. -/
theorem programPGlobalGaugeFixedLLHessian_LL_pairing
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod llData) :
    inner Real
        (programPGlobalGaugeFixedLLHessianOperator
          period hPeriod covector matterMass llData
          (programPGlobalGaugeFixedLLHessianLLCore
            period hPeriod covector matterMass llData direction))
        ((programPGlobalGaugeFixedLLHessianLLCore
          period hPeriod covector matterMass llData test :
            (programPGlobalGaugeFixedLLHessianOperator
              period hPeriod covector matterMass llData).domain) :
          ProgramPGlobalGaugeFixedLLHessianHilbert
            period hPeriod ι llData) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        llData.frame llData.fields direction.toTest test.toTest llData.mu := by
  unfold programPGlobalGaugeFixedLLHessianOperator
  have hApply :=
    linearPMapProdIdentity_apply
      (F := LLH1Space period hPeriod llData)
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass)
      (programPGlobalGaugeFixedLLHessianLLCore
        period hPeriod covector matterMass llData direction)
  rw [hApply, WithLp.prod_inner_apply]
  simp only [programPGlobalGaugeFixedLLHessianLLCore_coe,
    inner_zero_right, zero_add]
  rw [llH1SmoothEmbedding_apply, llH1SmoothEmbedding_apply,
    UniformSpace.Completion.inner_coe]
  exact llH1Smooth_inner period hPeriod llData direction test

/-- The LL block is the actual mixed Hessian of the unchanged PT-symmetric LL
action. -/
theorem programPGlobalGaugeFixedLLHessian_LL_actualAction_pairing
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod llData) :
    inner Real
        (programPGlobalGaugeFixedLLHessianOperator
          period hPeriod covector matterMass llData
          (programPGlobalGaugeFixedLLHessianLLCore
            period hPeriod covector matterMass llData direction))
        ((programPGlobalGaugeFixedLLHessianLLCore
          period hPeriod covector matterMass llData test :
            (programPGlobalGaugeFixedLLHessianOperator
              period hPeriod covector matterMass llData).domain) :
          ProgramPGlobalGaugeFixedLLHessianHilbert
            period hPeriod ι llData) =
      globalPTSymmetricDifferentialLLActionMixedHessian period hPeriod
        llData.frame llData.fields direction.toTest test.toTest llData.mu := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [globalPTSymmetricDifferentialLLActionMixedHessian_eq_fluxHessian]
  exact programPGlobalGaugeFixedLLHessian_LL_pairing
    period hPeriod covector matterMass llData direction test

theorem programPGlobalGaugeFixedLLHessian_domain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    Dense
      ((programPGlobalGaugeFixedLLHessianOperator
        period hPeriod covector matterMass llData).domain :
        Set (ProgramPGlobalGaugeFixedLLHessianHilbert
          period hPeriod ι llData)) :=
  linearPMapProdIdentity_domain_dense
    (F := LLH1Space period hPeriod llData)
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianRealDomain_dense
      period hPeriod covector matterMass)

theorem programPGlobalGaugeFixedLLHessian_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint
      (programPGlobalGaugeFixedLLHessianOperator
        period hPeriod covector matterMass llData) := by
  apply linearPMapProdIdentity_selfAdjoint
  exact complexDiagonalNativeRealOperator_isSelfAdjoint
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

theorem programPGlobalGaugeFixedLLHessian_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    (programPGlobalGaugeFixedLLHessianOperator
      period hPeriod covector matterMass llData).IsClosed :=
  (programPGlobalGaugeFixedLLHessian_selfAdjoint
    period hPeriod covector matterMass llData).isClosed

theorem programPGlobalGaugeFixedLLHessian_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod) :
    IsClosed
        (LinearMap.range
          (programPGlobalGaugeFixedLLHessianOperator
            period hPeriod covector matterMass llData).toFun :
          Set (ProgramPGlobalGaugeFixedLLHessianHilbert
            period hPeriod ι llData)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalGaugeFixedLLHessianOperator
            period hPeriod covector matterMass llData).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLHessianHilbert
            period hPeriod ι llData ⧸
          LinearMap.range
            (programPGlobalGaugeFixedLLHessianOperator
              period hPeriod covector matterMass llData).toFun) :=
  linearPMapProdIdentity_fredholm
    (F := LLH1Space period hPeriod llData)
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity matterMass)

end

end P0EFTJanusProgramPGlobalGaugeFixedLLHessianFredholm4D
end JanusFormal
