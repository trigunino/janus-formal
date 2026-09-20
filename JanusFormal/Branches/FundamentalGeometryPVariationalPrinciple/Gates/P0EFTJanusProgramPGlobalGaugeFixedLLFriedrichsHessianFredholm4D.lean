import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearPMapProdIdentityFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

/-!
# Global spectral Hessian with the reduced LL Friedrichs block

This gate replaces the historical bounded identity on the LL energy space by
the canonical self-adjoint Friedrichs operator on the genuine LL `L²` space.
The direct product is densely defined, self-adjoint, closed and Fredholm.  Its
LL inverse is compact.

This analytic assembly does not yet identify a dense global Candidate-A
quotient core with the product domain.  In particular, it does not reuse the
bounded five-sector Riesz representative or assert its natural-family
agreement.  That exact core pairing is a separate downstream obligation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped LinearPMap
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Ambient real Hilbert product of the corrected D10-free spectral target
and the genuine reduced LL `L²` carrier. -/
abbrev ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι ×
      CanonicalLLL2 period hPeriod analysis)

local instance globalGaugeFixedLLFriedrichsLinearPMapStar
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Star
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis →ₗ.[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis) :=
  LinearPMap.instStar

/-- Direct sum of the maximal gauge/ghost--matter spectral operator and the
canonical reduced LL Friedrichs realization. -/
abbrev programPGlobalGaugeFixedLLFriedrichsHessianOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod ι analysis →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod ι analysis :=
  linearPMapProd
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass)
    (canonicalLLFriedrichsJacobi period hPeriod analysis)

theorem programPGlobalGaugeFixedLLFriedrichsHessian_domain_dense
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Dense
      ((programPGlobalGaugeFixedLLFriedrichsHessianOperator
          period hPeriod covector matterMass analysis).domain :
        Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis)) :=
  linearPMapProd_domain_dense _ _
    (programPGlobalGaugeFixedSpectralHessianRealDomain_dense
      period hPeriod covector matterMass)
    (canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis)

theorem programPGlobalGaugeFixedLLFriedrichsHessian_selfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsSelfAdjoint
      (programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis) :=
  by
    have hSpectral :=
      programPGlobalGaugeFixedSpectralHessianRealOperator_selfAdjoint
        period hPeriod covector matterMass
    unfold
      programPGlobalGaugeFixedSpectralHessianHilbertRealLinearPMapStar at hSpectral
    exact linearPMapProd_selfAdjoint _ _ hSpectral
      (canonicalLLFriedrichsJacobi_isSelfAdjoint period hPeriod analysis)

theorem programPGlobalGaugeFixedLLFriedrichsHessian_closed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (programPGlobalGaugeFixedLLFriedrichsHessianOperator
      period hPeriod covector matterMass analysis).IsClosed :=
  (programPGlobalGaugeFixedLLFriedrichsHessian_selfAdjoint
    period hPeriod covector matterMass analysis).isClosed

theorem programPGlobalGaugeFixedLLFriedrichsHessian_fredholm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsClosed
        (LinearMap.range
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator
            period hPeriod covector matterMass analysis).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator
            period hPeriod covector matterMass analysis).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis ⧸
          LinearMap.range
            (programPGlobalGaugeFixedLLFriedrichsHessianOperator
              period hPeriod covector matterMass analysis).toFun) :=
  linearPMapProd_fredholm _ _
    (programPGlobalGaugeFixedSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity matterMass)
    (canonicalLLFriedrichsJacobi_fredholm period hPeriod analysis)

/-- Auditable analytic certificate for the global direct product.  Compactness
is asserted only for the LL inverse, not for the unresolved spectral-product
resolvent. -/
structure ProgramPGlobalGaugeFixedLLFriedrichsHessianFredholmCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  domainDense :
    Dense
      ((programPGlobalGaugeFixedLLFriedrichsHessianOperator
          period hPeriod covector matterMass analysis).domain :
        Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis))
  selfAdjoint :
    IsSelfAdjoint
      (programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis)
  closed :
    (programPGlobalGaugeFixedLLFriedrichsHessianOperator
      period hPeriod covector matterMass analysis).IsClosed
  fredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator
            period hPeriod covector matterMass analysis).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator
            period hPeriod covector matterMass analysis).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis ⧸
          LinearMap.range
            (programPGlobalGaugeFixedLLFriedrichsHessianOperator
              period hPeriod covector matterMass analysis).toFun)
  llCompactInverse :
    IsCompactOperator
      (canonicalLLWeakL2Inverse period hPeriod analysis)
  llExtendsClosedJacobi :
    canonicalLLClosedJacobi period hPeriod analysis ≤
      canonicalLLFriedrichsJacobi period hPeriod analysis

def programPGlobalGaugeFixedLLFriedrichsHessianFredholmCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianFredholmCertificate4D
      period hPeriod d9Ellipticity matterMass analysis where
  domainDense :=
    programPGlobalGaugeFixedLLFriedrichsHessian_domain_dense
      period hPeriod covector matterMass analysis
  selfAdjoint :=
    programPGlobalGaugeFixedLLFriedrichsHessian_selfAdjoint
      period hPeriod covector matterMass analysis
  closed :=
    programPGlobalGaugeFixedLLFriedrichsHessian_closed
      period hPeriod covector matterMass analysis
  fredholm :=
    programPGlobalGaugeFixedLLFriedrichsHessian_fredholm
      period hPeriod d9Ellipticity matterMass analysis
  llCompactInverse :=
    canonicalLLFriedrichsJacobi_compactInverse period hPeriod analysis
  llExtendsClosedJacobi :=
    canonicalLLClosedJacobi_le_friedrichsJacobi period hPeriod analysis

end
end P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
end JanusFormal
