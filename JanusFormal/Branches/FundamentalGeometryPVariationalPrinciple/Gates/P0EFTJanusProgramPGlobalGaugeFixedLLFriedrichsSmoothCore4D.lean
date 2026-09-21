import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D

/-!
# Finite-spectral times smooth-LL core

This is the concrete dense product core of the global spectral--Friedrichs
operator, together with its exact action and quadratic pairing.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Smooth LL directions as a real-linear subspace of the Friedrichs domain. -/
def canonicalLLFriedrichsSmoothDomainLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) →ₗ[Real]
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain where
  toFun := canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis
  map_add' first second := by
    apply Subtype.ext
    change
      ((canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis (first + second) :
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) =
      ((canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis first :
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) +
      ((canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis second :
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis)
    rw [canonicalLLFriedrichsSmoothDomainElement_value,
      canonicalLLFriedrichsSmoothDomainElement_value,
      canonicalLLFriedrichsSmoothDomainElement_value]
    exact (llH1SmoothToFluxL2LinearMap period hPeriod
      (analysis.llH1Data period hPeriod)).map_add first second
  map_smul' scalar direction := by
    apply Subtype.ext
    change
      ((canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis (scalar • direction) :
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) =
      scalar •
        ((canonicalLLFriedrichsSmoothDomainElement
            period hPeriod analysis direction :
              (canonicalLLFriedrichsJacobi
                period hPeriod analysis).domain) :
          CanonicalLLL2 period hPeriod analysis)
    rw [canonicalLLFriedrichsSmoothDomainElement_value,
      canonicalLLFriedrichsSmoothDomainElement_value]
    exact (llH1SmoothToFluxL2LinearMap period hPeriod
      (analysis.llH1Data period hPeriod)).map_smul scalar direction

theorem canonicalLLFriedrichsSmoothDomainLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (canonicalLLFriedrichsSmoothDomainLinearMap period hPeriod analysis) := by
  intro first second hEqual
  have hValue := congrArg Subtype.val hEqual
  change
    ((canonicalLLFriedrichsSmoothDomainElement
        period hPeriod analysis first :
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).domain) :
      CanonicalLLL2 period hPeriod analysis) =
    ((canonicalLLFriedrichsSmoothDomainElement
        period hPeriod analysis second :
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).domain) :
      CanonicalLLL2 period hPeriod analysis) at hValue
  rw [canonicalLLFriedrichsSmoothDomainElement_value,
    canonicalLLFriedrichsSmoothDomainElement_value] at hValue
  apply llH1SmoothEmbedding_injective period hPeriod
    (analysis.llH1Data period hPeriod)
  apply canonicalLLH1ToFluxL2_injective period hPeriod analysis
  rw [canonicalLLH1ToFluxL2_agrees_on_smooth,
    canonicalLLH1ToFluxL2_agrees_on_smooth]
  exact hValue

theorem canonicalLLFriedrichsSmoothDomainLinearMap_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange (fun direction =>
      ((canonicalLLFriedrichsSmoothDomainLinearMap
          period hPeriod analysis direction :
            (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis)) := by
  have hComp : DenseRange (fun direction =>
      canonicalLLH1ToFluxL2 period hPeriod analysis
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) direction)) :=
    (canonicalLLH1ToFluxL2_denseRange period hPeriod analysis).comp
      (llH1SmoothEmbedding_denseRange period hPeriod
        (analysis.llH1Data period hPeriod))
      (canonicalLLH1ToFluxL2 period hPeriod analysis).continuous
  change DenseRange (fun direction =>
    ((canonicalLLFriedrichsSmoothDomainElement
        period hPeriod analysis direction :
          (canonicalLLFriedrichsJacobi
            period hPeriod analysis).domain) :
      CanonicalLLL2 period hPeriod analysis))
  simpa only [canonicalLLH1ToFluxL2_agrees_on_smooth,
    canonicalLLFriedrichsSmoothDomainElement_value] using hComp

/-- Finite spectral coefficients paired with a smooth reduced LL direction. -/
abbrev ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (iota : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  ProgramPGlobalGaugeFixedSpectralFiniteCoefficients iota ×
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)

private def programPGlobalGaugeFixedLLFriedrichsSmoothCoreAmbientMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
        period hPeriod iota analysis →ₗ[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (WithLp.linearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota ×
      CanonicalLLL2 period hPeriod analysis)).symm.toLinearMap.comp
    (LinearMap.prodMap
      ((programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
          period hPeriod covector matterMass).domain.subtype.comp
        (programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass))
      ((canonicalLLFriedrichsJacobi period hPeriod analysis).domain.subtype.comp
        (canonicalLLFriedrichsSmoothDomainLinearMap
          period hPeriod analysis)))

private theorem programPGlobalGaugeFixedLLFriedrichsSmoothCoreAmbientMap_mem_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
      period hPeriod iota analysis) :
    programPGlobalGaugeFixedLLFriedrichsSmoothCoreAmbientMap
        period hPeriod covector matterMass analysis core ∈
      (programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis).domain := by
  change
    (((programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass core.1 :
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).domain) :
        ProgramPGlobalGaugeFixedSpectralHessianHilbert iota) ∈
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain) ∧
    (((canonicalLLFriedrichsSmoothDomainLinearMap
        period hPeriod analysis core.2 :
          (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) ∈
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain)
  exact ⟨(programPGlobalGaugeFixedSpectralFiniteCore
    period hPeriod covector matterMass core.1).property,
    (canonicalLLFriedrichsSmoothDomainLinearMap
      period hPeriod analysis core.2).property⟩

/-- The concrete product core inside the maximal spectral--Friedrichs domain. -/
def programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
        period hPeriod iota analysis →ₗ[Real]
      (programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis).domain :=
  (programPGlobalGaugeFixedLLFriedrichsSmoothCoreAmbientMap
    period hPeriod covector matterMass analysis).codRestrict _
      (programPGlobalGaugeFixedLLFriedrichsSmoothCoreAmbientMap_mem_domain
        period hPeriod covector matterMass analysis)

theorem programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
        period hPeriod covector matterMass analysis) := by
  intro first second hEqual
  have hPair := congrArg WithLp.ofLp (congrArg Subtype.val hEqual)
  change
    (((programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass first.1 :
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).domain) :
        ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
      ((canonicalLLFriedrichsSmoothDomainLinearMap
          period hPeriod analysis first.2 :
            (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis)) =
    (((programPGlobalGaugeFixedSpectralFiniteCore
        period hPeriod covector matterMass second.1 :
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).domain) :
        ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
      ((canonicalLLFriedrichsSmoothDomainLinearMap
          period hPeriod analysis second.2 :
            (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis)) at hPair
  apply Prod.ext
  · apply programPGlobalGaugeFixedSpectralFiniteCore_injective
      period hPeriod covector matterMass
    apply Subtype.ext
    exact congrArg Prod.fst hPair
  · apply canonicalLLFriedrichsSmoothDomainLinearMap_injective
      period hPeriod analysis
    apply Subtype.ext
    exact congrArg Prod.snd hPair

/-- The product core is dense after forgetting operator-domain membership. -/
theorem programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange (fun core =>
      ((programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
          period hPeriod covector matterMass analysis core :
            (programPGlobalGaugeFixedLLFriedrichsHessianOperator
              period hPeriod covector matterMass analysis).domain) :
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis)) := by
  have hProduct :=
    (programPGlobalGaugeFixedSpectralFiniteCore_denseRange
      period hPeriod covector matterMass).prodMap
      (canonicalLLFriedrichsSmoothDomainLinearMap_denseRange
        period hPeriod analysis)
  exact
    (WithLp.homeomorphProd 2
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
      (CanonicalLLL2 period hPeriod analysis)).symm.surjective.denseRange.comp
        hProduct
        (WithLp.homeomorphProd 2
          (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
          (CanonicalLLL2 period hPeriod analysis)).symm.continuous

@[simp]
theorem programPGlobalGaugeFixedLLFriedrichsHessianOperator_on_smoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
      period hPeriod iota analysis) :
    programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
          period hPeriod covector matterMass analysis core) =
      (WithLp.toLp 2
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass
            (programPGlobalGaugeFixedSpectralFiniteCore
              period hPeriod covector matterMass core.1),
          llStrongJacobiToL2 period hPeriod
            (analysis.llH1Data period hPeriod).fields core.2.toTest) :
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis) := by
  change linearPMapProd
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass)
      (canonicalLLFriedrichsJacobi period hPeriod analysis)
      (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
        period hPeriod covector matterMass analysis core) = _
  rw [linearPMapProd_apply]
  congr 1
  apply Prod.ext
  · rfl
  · exact canonicalLLFriedrichsJacobi_on_smooth
      period hPeriod analysis core.2

/-- Exact sum of the finite spectral and smooth LL Hessian pairings. -/
theorem programPGlobalGaugeFixedLLFriedrichsSmoothCore_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : ProgramPGlobalGaugeFixedLLFriedrichsSmoothCore
      period hPeriod iota analysis) :
    inner Real
        (programPGlobalGaugeFixedLLFriedrichsHessianOperator
          period hPeriod covector matterMass analysis
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
            period hPeriod covector matterMass analysis first))
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
          period hPeriod covector matterMass analysis second :
            ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
              period hPeriod iota analysis) =
      (∑ mode ∈ first.1.support,
        (inner Complex
          ((programPGlobalGaugeFixedSpectralHessianWeight
              period hPeriod covector matterMass mode : Complex) *
            first.1 mode)
          (second.1 mode)).re) +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (analysis.llH1Data period hPeriod).frame
          (analysis.llH1Data period hPeriod).fields
          first.2.toTest second.2.toTest
          (analysis.llH1Data period hPeriod).mu := by
  rw [programPGlobalGaugeFixedLLFriedrichsHessianOperator_on_smoothCore]
  change
    inner Real
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
          period hPeriod covector matterMass
          (programPGlobalGaugeFixedSpectralFiniteCore
            period hPeriod covector matterMass first.1))
        (programPGlobalGaugeFixedSpectralFiniteCore
          period hPeriod covector matterMass second.1 :
            ProgramPGlobalGaugeFixedSpectralHessianHilbert iota) +
      inner Real
        (llStrongJacobiToL2 period hPeriod
          (analysis.llH1Data period hPeriod).fields first.2.toTest)
        (canonicalLLFriedrichsSmoothDomainElement
          period hPeriod analysis second.2 :
            CanonicalLLL2 period hPeriod analysis) = _
  rw [programPGlobalGaugeFixedSpectralFiniteCore_pairing]
  congr 1
  have hLL := canonicalLLFriedrichsJacobi_smooth_pairing
    period hPeriod analysis first.2 second.2
  rw [canonicalLLFriedrichsJacobi_on_smooth] at hLL
  exact hLL

end
end P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
end JanusFormal
