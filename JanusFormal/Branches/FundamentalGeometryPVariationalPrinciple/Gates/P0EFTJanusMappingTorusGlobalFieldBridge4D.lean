import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusPTInvolution
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalFieldConfiguration4D

/-!
# Effective mapping-torus bases for the global field configuration

This bridge replaces the abstract spacetime and throat involutions in the
global-field gate by the actual D8 orbit quotients.  The fixed-throat quotient
inclusion is proved compatible with the same PT action used on fields.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalFieldBridge4D

set_option autoImplicit false

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusGlobalFieldConfiguration4D

abbrev EffectiveJanusSpacetime (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (reflectedSphereData period hPeriod)

abbrev EffectiveJanusThroat (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The abstract spacetime PT slot instantiated by the actual quotient map. -/
def effectiveSpacetimePT (period : Real) (hPeriod : period ≠ 0) :
    AlgebraicInvolution (EffectiveJanusSpacetime period hPeriod) where
  act := reflectedSpherePT period hPeriod
  act_involutive := reflectedSpherePT_involutive period hPeriod

/-- The abstract throat PT slot instantiated on the same effective quotient
used by the throat inclusion and normal line. -/
def effectiveThroatPT (period : Real) (hPeriod : period ≠ 0) :
    AlgebraicInvolution (EffectiveJanusThroat period hPeriod) where
  act := fixedThroatPT period hPeriod
  act_involutive := fixedThroatPT_involutive period hPeriod

/-- The actual quotient inclusion is equivariant for the two instantiated
algebraic involutions. -/
theorem effectiveThroatEmbedding_pt_equivariant
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusThroat period hPeriod) :
    fixedThroatQuotientInclusion period hPeriod
        ((effectiveThroatPT period hPeriod).act point) =
      (effectiveSpacetimePT period hPeriod).act
        (fixedThroatQuotientInclusion period hPeriod point) :=
  fixedThroatQuotientInclusion_pt_equivariant period hPeriod point

/-- Under the pullback convention of `independentPTExchange`, the equivariant
throat embedding is fixed after acting on both source and target. -/
theorem effectiveThroatEmbedding_transform_fixed
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusThroat period hPeriod) :
    (effectiveSpacetimePT period hPeriod).act
        (fixedThroatQuotientInclusion period hPeriod
          ((effectiveThroatPT period hPeriod).act point)) =
      fixedThroatQuotientInclusion period hPeriod point := by
  rw [effectiveThroatEmbedding_pt_equivariant]
  exact (effectiveSpacetimePT period hPeriod).act_act _

/-- Full independent-field PT data with effective D8 bases and explicit fibre
involutions.  Only the base slots are fixed here; matter content remains a
separate physical choice. -/
def effectiveIndependentPTData
    (period : Real) (hPeriod : period ≠ 0)
    (Matter Gauge Ghost Auxiliary LLIndependent : Type*)
    (matterPT : AlgebraicInvolution Matter)
    (gaugePT : AlgebraicInvolution Gauge)
    (ghostPT : AlgebraicInvolution Ghost)
    (auxiliaryPT : AlgebraicInvolution Auxiliary)
    (llPT : AlgebraicInvolution LLIndependent) :
    IndependentPTData
      (EffectiveJanusSpacetime period hPeriod)
      (EffectiveJanusThroat period hPeriod)
      Matter Gauge Ghost Auxiliary LLIndependent where
  spacetime := effectiveSpacetimePT period hPeriod
  throat := effectiveThroatPT period hPeriod
  metric := AlgebraicInvolution.identity LorentzMetricPoint4
  matter := matterPT
  gauge := gaugePT
  ghost := ghostPT
  auxiliary := auxiliaryPT
  llIndependent := llPT

/-- Exchanging any field configuration whose embedding is the effective throat
inclusion preserves that same embedding exactly. -/
theorem independentPTExchange_preserves_effective_throat
    (period : Real) (hPeriod : period ≠ 0)
    {Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (matterPT : AlgebraicInvolution Matter)
    (gaugePT : AlgebraicInvolution Gauge)
    (ghostPT : AlgebraicInvolution Ghost)
    (auxiliaryPT : AlgebraicInvolution Auxiliary)
    (llPT : AlgebraicInvolution LLIndependent)
    (fields : IndependentFields
      (EffectiveJanusSpacetime period hPeriod)
      (EffectiveJanusThroat period hPeriod)
      Matter Gauge Ghost Auxiliary LLIndependent)
    (hEmbedding : fields.throatEmbedding =
      fixedThroatQuotientInclusion period hPeriod) :
    (independentPTExchange
      (effectiveIndependentPTData period hPeriod Matter Gauge Ghost Auxiliary
        LLIndependent matterPT gaugePT ghostPT auxiliaryPT llPT) fields).throatEmbedding =
      fixedThroatQuotientInclusion period hPeriod := by
  funext point
  simp only [independentPTExchange]
  rw [hEmbedding]
  exact effectiveThroatEmbedding_transform_fixed period hPeriod point

/-- Concrete same-object bridge: quotient bases, PT actions and throat map all
belong to one effective D8 geometry. -/
theorem effective_mapping_torus_field_base_closure
    (period : Real) (hPeriod : period ≠ 0) :
    Function.Involutive (reflectedSpherePT period hPeriod) ∧
      Function.Involutive (fixedThroatPT period hPeriod) ∧
      (∀ point : EffectiveJanusThroat period hPeriod,
        fixedThroatQuotientInclusion period hPeriod
            (fixedThroatPT period hPeriod point) =
          reflectedSpherePT period hPeriod
            (fixedThroatQuotientInclusion period hPeriod point)) := by
  exact ⟨reflectedSpherePT_involutive period hPeriod,
    fixedThroatPT_involutive period hPeriod,
    fixedThroatQuotientInclusion_pt_equivariant period hPeriod⟩

end P0EFTJanusMappingTorusGlobalFieldBridge4D
end JanusFormal
