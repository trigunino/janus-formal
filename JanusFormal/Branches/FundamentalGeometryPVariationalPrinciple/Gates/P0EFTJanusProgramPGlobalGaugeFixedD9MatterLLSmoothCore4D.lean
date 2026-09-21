import Mathlib.LinearAlgebra.Finsupp.SumProd
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D

/-!
# Separated D9--matter--LL smooth core

The finite spectral core splits canonically into its D9 and primitive SpinC
summands.  On the resulting product core the global pairing is the exact D9
graph pairing, the matter graph form, and the smooth LL Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedD9MatterLLSmoothCore4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
attribute [local instance]
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

local instance d9MatterLLSmoothCoreModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

local instance d9MatterLLSmoothCoreD9RealInnerProductSpace
    (iota : Type*) :
    InnerProductSpace Real (D9GaugeGhostUnboundedHilbert iota) :=
  InnerProductSpace.complexToReal

/-- Finite coefficients in the complexified D9 gauge--ghost block. -/
abbrev ProgramPGlobalGaugeFixedD9FiniteCoefficients (iota : Type*) :=
  (iota × Fin 8) →₀ Complex

/-- Canonical splitting of the finite global spectral coefficients. -/
def programPGlobalGaugeFixedSpectralFiniteCoefficientsDecomposition
    (iota : Type*) :
    ProgramPGlobalGaugeFixedSpectralFiniteCoefficients iota ≃ₗ[Complex]
      ProgramPGlobalGaugeFixedD9FiniteCoefficients iota ×
        ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
  Finsupp.sumFinsuppLEquivProdFinsupp Complex

@[simp]
theorem programPGlobalGaugeFixedSpectralFiniteCoefficientsDecomposition_symm
    {iota : Type*}
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota ×
      ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (programPGlobalGaugeFixedSpectralFiniteCoefficientsDecomposition iota).symm
        coefficients =
      coefficients.1.sumElim coefficients.2 :=
  rfl

/-- Finite D9 coefficients included in the ambient complex `ℓ²` space. -/
def programPGlobalGaugeFixedD9FiniteHilbertEmbedding
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedD9FiniteCoefficients iota →ₗ[Complex]
      D9GaugeGhostUnboundedHilbert iota :=
  Finsupp.linearCombination Complex
    (complexDiagonalBasis (iota × Fin 8))

@[simp]
theorem programPGlobalGaugeFixedD9FiniteHilbertEmbedding_single
    {iota : Type*} [DecidableEq iota]
    (mode : iota × Fin 8) (coefficient : Complex) :
    programPGlobalGaugeFixedD9FiniteHilbertEmbedding
        (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [programPGlobalGaugeFixedD9FiniteHilbertEmbedding,
    Finsupp.linearCombination_single, complexDiagonalBasis_eq_single]
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [lp.single_apply]
  · simp [lp.single_apply, hOther]

@[simp]
theorem programPGlobalGaugeFixedD9FiniteHilbertEmbedding_apply
    {iota : Type*} [DecidableEq iota]
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota)
    (mode : iota × Fin 8) :
    programPGlobalGaugeFixedD9FiniteHilbertEmbedding coefficients mode =
      coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [programPGlobalGaugeFixedD9FiniteHilbertEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        programPGlobalGaugeFixedD9FiniteHilbertEmbedding
              (Finsupp.single other coefficient) mode +
            programPGlobalGaugeFixedD9FiniteHilbertEmbedding rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [programPGlobalGaugeFixedD9FiniteHilbertEmbedding_single,
        inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

/-- Finite coefficient realization of the exact D9 diagonal multiplier. -/
def programPGlobalGaugeFixedD9FiniteHessian
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    ProgramPGlobalGaugeFixedD9FiniteCoefficients iota →ₗ[Complex]
      ProgramPGlobalGaugeFixedD9FiniteCoefficients iota :=
  Finsupp.lsum Complex fun mode =>
    (Finsupp.lsingle mode).comp
      (((d9GaugeGhostUnboundedWeight covector mode : Real) : Complex) •
        (LinearMap.id : Complex →ₗ[Complex] Complex))

@[simp]
theorem programPGlobalGaugeFixedD9FiniteHessian_apply
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota)
    (mode : iota × Fin 8) :
    programPGlobalGaugeFixedD9FiniteHessian covector coefficients mode =
      (d9GaugeGhostUnboundedWeight covector mode : Complex) *
        coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [programPGlobalGaugeFixedD9FiniteHessian]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add, Finsupp.add_apply, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [programPGlobalGaugeFixedD9FiniteHessian]
        ring
      · simp [programPGlobalGaugeFixedD9FiniteHessian, hMode]

/-- Finite D9 coefficients as an element of the exact maximal graph. -/
def programPGlobalGaugeFixedD9FiniteGraph
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota) :
    D9GaugeGhostGraphDomain covector := by
  let state : D9GaugeGhostUnboundedHilbert iota :=
    programPGlobalGaugeFixedD9FiniteHilbertEmbedding coefficients
  let image : D9GaugeGhostUnboundedHilbert iota :=
    programPGlobalGaugeFixedD9FiniteHilbertEmbedding
      (programPGlobalGaugeFixedD9FiniteHessian covector coefficients)
  have hRelation : ∀ mode,
      image mode =
        (d9GaugeGhostUnboundedWeight covector mode : Complex) * state mode := by
    intro mode
    dsimp [image, state]
    rw [programPGlobalGaugeFixedD9FiniteHilbertEmbedding_apply,
      programPGlobalGaugeFixedD9FiniteHilbertEmbedding_apply,
      programPGlobalGaugeFixedD9FiniteHessian_apply]
  let domainState : (d9GaugeGhostUnboundedOperator covector).domain :=
    ⟨state, ⟨image, hRelation⟩⟩
  refine ⟨(state, image), ?_⟩
  apply (LinearPMap.mem_graph_iff
    (d9GaugeGhostUnboundedOperator covector)).2
  refine ⟨domainState, rfl, ?_⟩
  ext mode
  rw [d9GaugeGhostUnboundedOperator_apply]
  exact (hRelation mode).symm

@[simp]
theorem programPGlobalGaugeFixedD9FiniteGraph_fst
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota) :
    (programPGlobalGaugeFixedD9FiniteGraph covector coefficients).1.1 =
      programPGlobalGaugeFixedD9FiniteHilbertEmbedding coefficients :=
  rfl

@[simp]
theorem programPGlobalGaugeFixedD9FiniteGraph_snd
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (coefficients : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota) :
    (programPGlobalGaugeFixedD9FiniteGraph covector coefficients).1.2 =
      programPGlobalGaugeFixedD9FiniteHilbertEmbedding
        (programPGlobalGaugeFixedD9FiniteHessian covector coefficients) :=
  rfl

/-- Real graph pairing in the operator-first convention used by the global
spectral Hessian. -/
def programPGlobalGaugeFixedD9GraphPairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    D9GaugeGhostGraphDomain covector →L[Real]
      D9GaugeGhostGraphDomain covector →L[Real] Real :=
  (innerSL Real).bilinearComp
    ((d9GaugeGhostGraphOperator covector).restrictScalars Real)
    ((complexDiagonalGraphFstCLM (iota × Fin 8)
      (d9GaugeGhostUnboundedWeight covector)).restrictScalars Real)

@[simp]
theorem programPGlobalGaugeFixedD9GraphPairing_apply
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : D9GaugeGhostGraphDomain covector) :
    programPGlobalGaugeFixedD9GraphPairing covector first second =
      inner Real first.1.2 second.1.1 :=
  rfl

/-- Exact D9 graph pairing on finite coefficients. -/
theorem programPGlobalGaugeFixedD9FiniteGraph_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota) :
    programPGlobalGaugeFixedD9GraphPairing covector
        (programPGlobalGaugeFixedD9FiniteGraph covector first)
        (programPGlobalGaugeFixedD9FiniteGraph covector second) =
      ∑ mode ∈ first.support,
        (inner Complex
          ((d9GaugeGhostUnboundedWeight covector mode : Complex) * first mode)
          (second mode)).re := by
  rw [programPGlobalGaugeFixedD9GraphPairing_apply,
    programPGlobalGaugeFixedD9FiniteGraph_snd,
    programPGlobalGaugeFixedD9FiniteGraph_fst,
    real_inner_eq_re_inner, lp.inner_eq_tsum]
  simp_rw [programPGlobalGaugeFixedD9FiniteHilbertEmbedding_apply,
    programPGlobalGaugeFixedD9FiniteHessian_apply]
  rw [tsum_eq_sum (s := first.support) (by
    intro mode hMode
    rw [Finsupp.notMem_support_iff.mp hMode]
    simp)]
  change RCLike.reCLM
      (∑ mode ∈ first.support,
        inner Complex
          ((d9GaugeGhostUnboundedWeight covector mode : Complex) * first mode)
          (second mode)) = _
  rw [map_sum]
  rfl

/-- D9 and matter coefficients, followed by a smooth reduced LL direction. -/
abbrev ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  (ProgramPGlobalGaugeFixedD9FiniteCoefficients iota ×
      ProgramPPrimitiveSpinCMatterFiniteCoefficients) ×
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)

/-- The separated core is linearly equivalent to the global smooth core. -/
def programPGlobalGaugeFixedD9MatterLLSmoothCoreEquiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
        period hPeriod iota analysis ≃ₗ[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
        period hPeriod iota analysis :=
  LinearEquiv.prodCongr
    ((programPGlobalGaugeFixedSpectralFiniteCoefficientsDecomposition
      iota).symm.restrictScalars Real)
    (LinearEquiv.refl Real _)

/-- Linear inclusion of the separated coordinates into the global core. -/
def programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
        period hPeriod iota analysis →ₗ[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
        period hPeriod iota analysis :=
  (programPGlobalGaugeFixedD9MatterLLSmoothCoreEquiv
    period hPeriod iota analysis).toLinearMap

@[simp]
theorem programPGlobalGaugeFixedD9MatterLLSmoothCoreMap_fst
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
      period hPeriod iota analysis) :
    (programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
      period hPeriod iota analysis core).1 =
      core.1.1.sumElim core.1.2 :=
  rfl

@[simp]
theorem programPGlobalGaugeFixedD9MatterLLSmoothCoreMap_snd
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
      period hPeriod iota analysis) :
    (programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
      period hPeriod iota analysis core).2 = core.2 :=
  rfl

theorem programPGlobalGaugeFixedD9MatterLLSmoothCoreMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
        period hPeriod iota analysis) :=
  (programPGlobalGaugeFixedD9MatterLLSmoothCoreEquiv
    period hPeriod iota analysis).injective

private theorem programPGlobalGaugeFixedMatterGraphFinite_pairing
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

private theorem programPGlobalGaugeFixedD9MatterFinite_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (firstD9 secondD9 : ProgramPGlobalGaugeFixedD9FiniteCoefficients iota)
    (firstMatter secondMatter :
      ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∑ mode ∈ (firstD9.sumElim firstMatter).support,
      (inner Complex
        ((programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass mode : Complex) *
          firstD9.sumElim firstMatter mode)
        (secondD9.sumElim secondMatter mode)).re) =
      programPGlobalGaugeFixedD9GraphPairing covector
          (programPGlobalGaugeFixedD9FiniteGraph covector firstD9)
          (programPGlobalGaugeFixedD9FiniteGraph covector secondD9) +
        programPPrimitiveSpinCMatterGraphForm period hPeriod matterMass
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass firstMatter)
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass secondMatter) := by
  rw [Finsupp.sumElim_support, Finset.sum_disjSum]
  have hD9 := programPGlobalGaugeFixedD9FiniteGraph_pairing
    covector firstD9 secondD9
  have hMatter := programPGlobalGaugeFixedMatterGraphFinite_pairing
    period hPeriod matterMass firstMatter secondMatter
  rw [hD9]
  rw [hMatter]
  congr 1

/-- Exact global pairing after the canonical D9/matter split. -/
theorem programPGlobalGaugeFixedD9MatterLLSmoothCore_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : ProgramPGlobalGaugeFixedD9MatterLLSmoothCore
      period hPeriod iota analysis) :
    inner Real
        (programPGlobalGaugeFixedLLFriedrichsHessianOperator
          period hPeriod covector matterMass analysis
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
            period hPeriod covector matterMass analysis
            (programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
              period hPeriod iota analysis first)))
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
          period hPeriod covector matterMass analysis
          (programPGlobalGaugeFixedD9MatterLLSmoothCoreMap
            period hPeriod iota analysis second) :
            ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
              period hPeriod iota analysis) =
      (programPGlobalGaugeFixedD9GraphPairing covector
          (programPGlobalGaugeFixedD9FiniteGraph covector first.1.1)
          (programPGlobalGaugeFixedD9FiniteGraph covector second.1.1) +
        programPPrimitiveSpinCMatterGraphForm period hPeriod matterMass
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass first.1.2)
          (programPPrimitiveSpinCMatterGraphFinite
            period hPeriod matterMass second.1.2)) +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (analysis.llH1Data period hPeriod).frame
          (analysis.llH1Data period hPeriod).fields
          first.2.toTest second.2.toTest
          (analysis.llH1Data period hPeriod).mu := by
  rw [programPGlobalGaugeFixedLLFriedrichsSmoothCore_pairing]
  change
    (∑ mode ∈ (first.1.1.sumElim first.1.2).support,
      (inner Complex
        ((programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass mode : Complex) *
          first.1.1.sumElim first.1.2 mode)
        (second.1.1.sumElim second.1.2 mode)).re) + _ = _
  rw [programPGlobalGaugeFixedD9MatterFinite_pairing]
  rw [programPGlobalGaugeFixedD9MatterLLSmoothCoreMap_snd,
    programPGlobalGaugeFixedD9MatterLLSmoothCoreMap_snd]

end
end P0EFTJanusProgramPGlobalGaugeFixedD9MatterLLSmoothCore4D
end JanusFormal
