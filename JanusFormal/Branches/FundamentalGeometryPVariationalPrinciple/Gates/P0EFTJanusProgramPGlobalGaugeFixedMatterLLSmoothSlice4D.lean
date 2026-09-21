import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

/-!
# Matter--LL slice of the global smooth core

Finite primitive SpinC matter coefficients occupy the `Sum.inr` spectral
block, with zero D9 component.  Pairing this slice with the global
spectral--Friedrichs operator is exactly the matter graph form plus the smooth
LL Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal lp LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
attribute [local instance]
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterLLSmoothSliceModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

/-- Matter modes occupy precisely the right summand of the global spectral
mode family. -/
def programPGlobalGaugeFixedMatterModeEmbedding (iota : Type*) :
    ProgramPPrimitiveSpinCMatterMode ↪
      ProgramPGlobalGaugeFixedSpectralHessianMode iota :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Extend finite matter coefficients by zero on the D9 summand. -/
def programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
    {iota : Type*} [DecidableEq iota] :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ProgramPGlobalGaugeFixedSpectralFiniteCoefficients iota where
  toFun := Finsupp.embDomain
    (programPGlobalGaugeFixedMatterModeEmbedding iota)
  map_add' := Finsupp.embDomain_add _
  map_smul' scalar coefficients := by
    classical
    ext mode
    rcases mode with mode | mode
    · simp [programPGlobalGaugeFixedMatterModeEmbedding,
        Finsupp.embDomain_apply]
    · simp [programPGlobalGaugeFixedMatterModeEmbedding,
        Finsupp.embDomain_apply]

@[simp]
theorem programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding_d9
    {iota : Type*} [DecidableEq iota]
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (mode : iota × Fin 8) :
    programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
        (iota := iota) coefficients (.inl mode) = 0 := by
  simp [programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding,
    programPGlobalGaugeFixedMatterModeEmbedding, Finsupp.embDomain_apply]

@[simp]
theorem programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding_matter
    {iota : Type*} [DecidableEq iota]
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
        (iota := iota) coefficients (.inr mode) = coefficients mode := by
  exact Finsupp.embDomain_apply_self
    (programPGlobalGaugeFixedMatterModeEmbedding iota) coefficients mode

theorem programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding_injective
    {iota : Type*} [DecidableEq iota] :
    Function.Injective
      (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
        (iota := iota)) :=
  Finsupp.embDomain_injective
    (programPGlobalGaugeFixedMatterModeEmbedding iota)

/-- Finite matter coefficients paired with one smooth reduced LL direction. -/
abbrev ProgramPGlobalGaugeFixedMatterLLSmoothSlice
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)

/-- The matter--LL slice inside the global finite-spectral × smooth-LL core. -/
def programPGlobalGaugeFixedMatterLLSmoothSliceMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedMatterLLSmoothSlice
        period hPeriod analysis →ₗ[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
        period hPeriod iota analysis :=
  LinearMap.prodMap
    (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding (iota := iota))
    LinearMap.id

theorem programPGlobalGaugeFixedMatterLLSmoothSliceMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (programPGlobalGaugeFixedMatterLLSmoothSliceMap
        period hPeriod (iota := iota) analysis) := by
  intro first second hEqual
  change
    (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
        (iota := iota) first.1, first.2) =
      (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
        (iota := iota) second.1, second.2) at hEqual
  apply Prod.ext
  · apply programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding_injective
      (iota := iota)
    exact congrArg Prod.fst hEqual
  · have hSecond := congrArg (fun core => core.2) hEqual
    exact hSecond

private theorem programPPrimitiveSpinCMatterGraphFinite_pairing
    (matterMass : Real)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterGraphForm period hPeriod matterMass
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod matterMass first)
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod matterMass second) =
      ∑ mode ∈ first.support,
        (inner Complex
          (((programPPrimitiveSpinCMatterHessianWeight
              period hPeriod matterMass mode : Real) : Complex) * first mode)
          (second mode)).re := by
  rw [programPPrimitiveSpinCMatterGraphForm_comm,
    programPPrimitiveSpinCMatterGraphForm_apply,
    programPPrimitiveSpinCMatterGraphFinite_fst,
    programPPrimitiveSpinCMatterGraphFinite_snd]
  calc
    inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding
          (programPPrimitiveSpinCMatterFiniteHessian
            period hPeriod matterMass first)) =
      inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding
          (programPPrimitiveSpinCMatterFiniteHessian
            period hPeriod matterMass first))
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) :=
      real_inner_comm _ _
    _ = _ := by
      rw [real_inner_eq_re_inner, lp.inner_eq_tsum]
      simp_rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply,
        programPPrimitiveSpinCMatterFiniteHessian_apply]
      rw [tsum_eq_sum (s := first.support) (by
        intro mode hMode
        rw [Finsupp.notMem_support_iff.mp hMode]
        simp)]
      change RCLike.reCLM
          (∑ mode ∈ first.support,
            inner Complex
              (((programPPrimitiveSpinCMatterHessianWeight
                  period hPeriod matterMass mode : Real) : Complex) * first mode)
              (second mode)) = _
      rw [map_sum]
      rfl

private theorem programPGlobalGaugeFixedMatterFinite_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∑ mode ∈
        (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
          (iota := iota) first).support,
      (inner Complex
        ((programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass mode : Complex) *
          programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
            (iota := iota) first mode)
        (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
          (iota := iota) second mode)).re) =
      programPPrimitiveSpinCMatterGraphForm period hPeriod matterMass
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod matterMass first)
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod matterMass second) := by
  rw [programPPrimitiveSpinCMatterGraphFinite_pairing]
  change
    (∑ mode ∈
        (Finsupp.embDomain
          (programPGlobalGaugeFixedMatterModeEmbedding iota) first).support,
      (inner Complex
        ((programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass mode : Complex) *
          Finsupp.embDomain
            (programPGlobalGaugeFixedMatterModeEmbedding iota) first mode)
        (Finsupp.embDomain
          (programPGlobalGaugeFixedMatterModeEmbedding iota) second mode)).re) = _
  rw [Finsupp.support_embDomain, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro mode _
  rcases mode with ⟨sector, signedMode⟩
  rw [Finsupp.embDomain_apply_self, Finsupp.embDomain_apply_self]
  change
    (inner Complex
      ((programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass (.inr (sector, signedMode)) :
            Complex) * first (sector, signedMode))
      (second (sector, signedMode))).re = _
  rw [programPGlobalGaugeFixedSpectralHessianWeight_matter]
  rfl

/-- On the matter--LL slice, the global operator pairing is exactly the
primitive SpinC graph form plus the smooth reduced LL Hessian. -/
theorem programPGlobalGaugeFixedMatterLLSmoothSlice_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : ProgramPGlobalGaugeFixedMatterLLSmoothSlice
      period hPeriod analysis) :
    inner Real
        (programPGlobalGaugeFixedLLFriedrichsHessianOperator
          period hPeriod covector matterMass analysis
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
            period hPeriod covector matterMass analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap
              period hPeriod (iota := iota) analysis first)))
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
          period hPeriod covector matterMass analysis
          (programPGlobalGaugeFixedMatterLLSmoothSliceMap
            period hPeriod (iota := iota) analysis second) :
            ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
              period hPeriod iota analysis) =
      programPPrimitiveSpinCMatterGraphForm period hPeriod matterMass
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass first.1)
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass second.1) +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (analysis.llH1Data period hPeriod).frame
          (analysis.llH1Data period hPeriod).fields
          first.2.toTest second.2.toTest
          (analysis.llH1Data period hPeriod).mu := by
  rw [programPGlobalGaugeFixedLLFriedrichsSmoothCore_pairing]
  congr 1
  exact programPGlobalGaugeFixedMatterFinite_pairing
    period hPeriod covector matterMass first.1 second.1

end
end P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
end JanusFormal
