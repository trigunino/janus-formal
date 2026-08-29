import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D

/-!
# Smooth primitive SpinC sections in the maximal signed Hessian domain

The weighted Fourier datum has a geometric formulation.  A smooth primitive
section belongs to the maximal domain of `2D + m²`; after applying the maximal
geometric operator, one obtains the completion of the genuine smooth
differential expression.  Unitary conjugacy then forces the weighted
coefficient vector and its diagonal multiplier relation.

This gate isolates precisely those two geometric assertions.  It does not
assume an independently chosen weighted sequence.  The two-sector weighted
map is assembled canonically from the one-sector maximal operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped ENNReal lp LinearPMap InnerProductSpace
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SignedMode := PrimitiveSpinCGeometricSignedMode
private abbrev OneSectorSmooth :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev MatterSmooth :=
  ProgramPPrimitiveSpinCMatterSmoothField period hPeriod
private abbrev MatterCoefficients :=
  ProgramPPrimitiveSpinCMatterHilbert

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real MatterCoefficients :=
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

/-- Exact global analytic assertion for the smooth differential expression:
every smooth section is in the maximal geometric domain and the maximal
operator agrees with the completed smooth `2D + m²` expression. -/
structure ProgramPPrimitiveSpinCSmoothMaximalDomainData4D
    (massSquared : Real) : Prop where
  mem_domain : ∀ field : OneSectorSmooth period hPeriod,
    d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter field ∈
      primitiveSpinCGeometricSignedActionHessianGeometricDomain period hPeriod
        massSquared
  operator_agreement : ∀ field : OneSectorSmooth period hPeriod,
    primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
        massSquared
        ⟨d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
            field,
          mem_domain field⟩ =
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field)

/-- Linear lift of the whole smooth core to the maximal geometric domain. -/
def primitiveSpinCSmoothMaximalDomainLift
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :
    OneSectorSmooth period hPeriod →ₗ[Complex]
      primitiveSpinCGeometricSignedActionHessianGeometricDomain period hPeriod
        massSquared where
  toFun field :=
    ⟨d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter field,
      domain.mem_domain field⟩
  map_add' first second := by
    apply Subtype.ext
    exact map_add
      (d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter)
      first second
  map_smul' scalar field := by
    apply Subtype.ext
    exact map_smul
      (d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter)
      scalar field

/-- Canonical weighted Fourier coefficients of one sector, obtained by applying
the maximal geometric Hessian and returning through the signed unitary. -/
def primitiveSpinCOneSectorCanonicalWeightedCoefficients
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :
    OneSectorSmooth period hPeriod →ₗ[Complex]
      ComplexDiagonalHilbert SignedMode :=
  (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm.toLinearMap.comp
    ((primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
      massSquared).toFun.comp
      (primitiveSpinCSmoothMaximalDomainLift period hPeriod massSquared domain))

/-- The preceding coefficients are pointwise exactly the signed Hessian
multiplier applied to the canonical unweighted Fourier coefficients. -/
theorem primitiveSpinCOneSectorCanonicalWeightedCoefficients_apply
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (field : OneSectorSmooth period hPeriod) (mode : SignedMode) :
    primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
        massSquared domain field mode =
      ((primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod mode +
        massSquared : Real) : Complex) *
        primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod field
          mode := by
  let lifted := primitiveSpinCSmoothMaximalDomainLift period hPeriod
    massSquared domain field
  have hConjugacy :=
    primitiveSpinCGeometricSignedActionHessianGeometricOperator_conjugacy
      period hPeriod massSquared lifted
  have hDomainRelation :=
    complexDiagonalOperator_apply SignedMode
      (fun signedMode =>
        primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod
          signedMode + massSquared)
      (primitiveSpinCGeometricSignedActionHessianGeometricDomainEquiv period
        hPeriod massSquared lifted) mode
  change
    (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
        (primitiveSpinCGeometricSignedActionHessianGeometricOperator period
          hPeriod massSquared lifted) mode = _
  rw [hConjugacy, hDomainRelation]
  rfl

def primitiveSpinCMatterCanonicalSigmaWeightedCoefficients
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :
    MatterSmooth period hPeriod →ₗ[Complex] MatterCoefficients where
  toFun := fun field => ⟨fun mode =>
        primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
          massSquared domain (field mode.1) mode.2, by
        change Memℓp (fun mode : Sector × SignedMode =>
          primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
            massSquared domain (field mode.1) mode.2) 2
        rw [memℓp_gen_iff (by norm_num)]
        apply (summable_prod_of_nonneg (fun _ => by positivity)).2
        constructor
        · intro sector
          exact (memℓp_gen_iff (by norm_num)).1
            (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
              massSquared domain (field sector)).2
        · exact summable_of_hasFiniteSupport (Set.toFinite _)⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    funext mode
    exact congrArg (fun coefficients => coefficients mode.2) (map_add
      (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
        massSquared domain) (first mode.1) (second mode.1))
  map_smul' := by
    intro scalar field
    apply Subtype.ext
    funext mode
    exact congrArg (fun coefficients => coefficients mode.2) (map_smul
      (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
        massSquared domain) scalar (field mode.1))

/-- Assemble the weighted coefficients of both physical sectors. -/
def programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :
    MatterSmooth period hPeriod →ₗ[Complex] MatterCoefficients :=
  primitiveSpinCMatterCanonicalSigmaWeightedCoefficients period hPeriod
    massSquared domain

@[simp] private theorem
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain_raw_apply
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (field : MatterSmooth period hPeriod)
    (sector : Sector) (mode : SignedMode) :
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
        period hPeriod massSquared domain field (sector, mode) =
      primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
        massSquared domain (field sector) mode := by
  rfl

@[simp]
theorem
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain_apply
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (field : MatterSmooth period hPeriod)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
        period hPeriod massSquared domain field mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) *
        programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
          field mode := by
  rcases mode with ⟨sector, mode⟩
  rw [programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain_raw_apply,
    primitiveSpinCOneSectorCanonicalWeightedCoefficients_apply,
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients_apply]
  rfl

/-- The remaining scalar identity converting the independently integrated
smooth action into the canonical completion pairing.  Unlike the coefficient
map, this is a genuine same-action theorem and remains explicit. -/
structure ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) : Prop where
  action_pairing : ∀ field : MatterSmooth period hPeriod,
    programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared field =
      (1 / 2 : Real) *
        inner Real
          (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period
            hPeriod field)
          (programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
            period hPeriod massSquared domain field)

/-- Maximal-domain membership and the same-action pairing construct the minimal
weighted-decay interface. -/
def programPPrimitiveSpinCMatterCanonicalWeightedDecayData_of_maximalDomain
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (sameAction : ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D
      period hPeriod massSquared domain) :
    ProgramPPrimitiveSpinCMatterCanonicalWeightedDecayData4D period hPeriod
      massSquared where
  weightedCoefficients :=
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
      period hPeriod massSquared domain
  weighted_relation :=
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain_apply
      period hPeriod massSquared domain
  smoothAction_eq_pairing := sameAction.action_pairing

/-- Final smooth graph realization through the maximal geometric domain. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (sameAction : ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D
      period hPeriod massSquared domain) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_weightedDecay period
    hPeriod massSquared
      (programPPrimitiveSpinCMatterCanonicalWeightedDecayData_of_maximalDomain
        period hPeriod massSquared domain sameAction)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D
end JanusFormal
