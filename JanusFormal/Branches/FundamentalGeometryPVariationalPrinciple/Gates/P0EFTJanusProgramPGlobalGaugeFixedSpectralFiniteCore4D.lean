import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D

/-!
# Finite core of the global gauge-fixed spectral Hessian

Finite-support coefficients give a concrete core of the maximal diagonal
spectral operator.  This file records its injection, ambient density, and
the exact operator and pairing formulas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

local instance spectralFiniteCoreModeDecidableEq
    (ι : Type*) [DecidableEq ι] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode ι) :=
  Classical.decEq _

local instance spectralFiniteCoreRealInnerProductSpace
    (ι : Type*) :
    InnerProductSpace Real
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) :=
  InnerProductSpace.complexToReal

/-- Arbitrary finite coefficients on the corrected D10-free spectral modes. -/
abbrev ProgramPGlobalGaugeFixedSpectralFiniteCoefficients (ι : Type*) :=
  ProgramPGlobalGaugeFixedSpectralHessianMode ι →₀ Complex

/-- Canonical finite-support inclusion in the ambient spectral Hilbert space. -/
def programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding
    {ι : Type*} [DecidableEq ι] :
    ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι →ₗ[Complex]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert ι :=
  Finsupp.linearCombination Complex
    (complexDiagonalBasis
      (ProgramPGlobalGaugeFixedSpectralHessianMode ι))

@[simp]
theorem programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_single
    {ι : Type*} [DecidableEq ι]
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (coefficient : Complex) :
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding
        (ι := ι) (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding,
    Finsupp.linearCombination_single, complexDiagonalBasis_eq_single]
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [lp.single_apply]
  · simp [lp.single_apply, hOther]

@[simp]
theorem programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_apply
    {ι : Type*} [DecidableEq ι]
    (coefficients : ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι)
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode ι) :
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding coefficients mode =
      coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding
              (Finsupp.single other coefficient) mode +
            programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_single,
        inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

/-- The finite coefficient inclusion is faithful. -/
theorem programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_injective
    {ι : Type*} [DecidableEq ι] :
    Function.Injective
      (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding (ι := ι)) := by
  intro first second hEqual
  ext mode
  have hMode := congrArg
    (fun state : ProgramPGlobalGaugeFixedSpectralHessianHilbert ι =>
      state mode) hEqual
  simpa using hMode

/-- Finite coefficients are dense in the ambient spectral Hilbert space. -/
theorem programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_range_dense
    {ι : Type*} [DecidableEq ι] :
    Dense
      ((LinearMap.range
        (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding (ι := ι)) :
          Submodule Complex
            (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) :
        Set (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) =
        (Submodule.span Complex
          (Set.range
            (complexDiagonalBasis
              (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
            ))).topologicalClosure :=
      (HilbertBasis.dense_span
        (complexDiagonalBasis
          (ProgramPGlobalGaugeFixedSpectralHessianMode ι))).symm
    _ ≤ (LinearMap.range
        (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding (ι := ι))
          ).topologicalClosure :=
      Submodule.topologicalClosure_mono
        (Submodule.span_le.mpr (by
          rintro _ ⟨mode, rfl⟩
          refine ⟨Finsupp.single mode 1, ?_⟩
          rw [programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_single,
            complexDiagonalBasis_eq_single]))

private def programPGlobalGaugeFixedSpectralFiniteHilbertRealEmbedding
    {ι : Type*} [DecidableEq ι] :
    ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι →ₗ[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert ι where
  toFun :=
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding (ι := ι)
  map_add' :=
    (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding
      (ι := ι)).map_add
  map_smul' scalar coefficients := by
    have hCoefficients :
        scalar • coefficients = (scalar : Complex) • coefficients := by
      ext mode
      rfl
    rw [hCoefficients, map_smul]
    exact (RCLike.real_smul_eq_coe_smul
      (K := Complex) scalar
        (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding
          coefficients)).symm

private theorem programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_mem_domain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (coefficients : ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι) :
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding coefficients ∈
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain := by
  change
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding coefficients ∈
      complexDiagonalDomain
        (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
        (programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass)
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      apply
        (complexDiagonalDomain
          (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)).add_mem
      · rw [programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding,
          Finsupp.linearCombination_single]
        exact
          (complexDiagonalDomain
            (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
            (programPGlobalGaugeFixedSpectralHessianWeight
              period hPeriod covector matterMass)).smul_mem coefficient
            (complexDiagonalBasis_mem_domain
              (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
              (programPGlobalGaugeFixedSpectralHessianWeight
                period hPeriod covector matterMass) mode)
      · exact inductionHypothesis

/-- Concrete finite-support core in the real maximal spectral domain. -/
def programPGlobalGaugeFixedSpectralFiniteCore
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι →ₗ[Real]
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain :=
  (programPGlobalGaugeFixedSpectralFiniteHilbertRealEmbedding (ι := ι)
    ).codRestrict
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain
      (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_mem_domain
        period hPeriod covector matterMass)

@[simp]
theorem programPGlobalGaugeFixedSpectralFiniteCore_value_apply
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (coefficients : ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι)
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode ι) :
    ((programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass coefficients :
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).domain) :
      ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) mode =
      coefficients mode := by
  exact
    programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_apply
      coefficients mode

theorem programPGlobalGaugeFixedSpectralFiniteCore_injective
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    Function.Injective
      (programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass) := by
  intro first second hEqual
  apply programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_injective
    (ι := ι)
  exact congrArg Subtype.val hEqual

/-- The concrete finite core is dense after forgetting domain membership. -/
theorem programPGlobalGaugeFixedSpectralFiniteCore_denseRange
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    DenseRange (fun coefficients =>
      ((programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass coefficients :
            (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
              period hPeriod covector matterMass).domain) :
        ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) := by
  rw [DenseRange]
  apply
    (programPGlobalGaugeFixedSpectralFiniteHilbertEmbedding_range_dense
      (ι := ι)).mono
  rintro state ⟨coefficients, rfl⟩
  exact ⟨coefficients, rfl⟩

/-- The maximal spectral operator acts by the declared diagonal weight on
the finite core. -/
@[simp]
theorem programPGlobalGaugeFixedSpectralHessianRealOperator_on_finiteCore
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (coefficients : ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι)
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode ι) :
    programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass
        (programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass coefficients) mode =
      (programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass mode : Complex) *
        coefficients mode := by
  rw [complexDiagonalRealOperator_apply,
    programPGlobalGaugeFixedSpectralFiniteCore_value_apply]

/-- Exact finite-sum pairing of the maximal operator on its concrete core. -/
theorem programPGlobalGaugeFixedSpectralFiniteCore_pairing
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (first second : ProgramPGlobalGaugeFixedSpectralFiniteCoefficients ι) :
    inner Real
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
          period hPeriod covector matterMass
          (programPGlobalGaugeFixedSpectralFiniteCore
            period hPeriod covector matterMass first))
        (programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass second :
            ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) =
      ∑ mode ∈ first.support,
        (inner Complex
          ((programPGlobalGaugeFixedSpectralHessianWeight
              period hPeriod covector matterMass mode : Complex) *
            first mode)
          (second mode)).re := by
  change
    (inner Complex
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass
        (programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass first))
      (programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass second :
          ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)).re = _
  rw [lp.inner_eq_tsum]
  simp_rw [programPGlobalGaugeFixedSpectralHessianRealOperator_on_finiteCore,
    programPGlobalGaugeFixedSpectralFiniteCore_value_apply]
  rw [tsum_eq_sum (s := first.support) (by
    intro mode hMode
    rw [Finsupp.notMem_support_iff.mp hMode]
    simp)]
  change RCLike.reCLM
      (∑ mode ∈ first.support,
        inner Complex
          ((programPGlobalGaugeFixedSpectralHessianWeight
              period hPeriod covector matterMass mode : Complex) *
            first mode)
          (second mode)) = _
  rw [map_sum]
  rfl

end
end P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
end JanusFormal
