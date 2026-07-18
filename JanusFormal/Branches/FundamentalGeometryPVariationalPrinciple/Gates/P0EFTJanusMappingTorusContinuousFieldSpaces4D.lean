import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFlatFieldBranch4D

/-!
# Continuous field spaces on the effective D8 mapping torus

This gate replaces the previously parametric regularity slots by explicit
continuity conditions on the actual effective spacetime and throat quotients.
It constructs a nonempty PT-matched continuous configuration on those same
bases.  The result is topological: no Sobolev, smooth-manifold, boundary-trace,
or global non-diagonal root claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusContinuousFieldSpaces4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusLLBraneAuxiliaryActionVariation
open P0EFTJanusGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusGlobalFieldBridge4D
open P0EFTJanusMappingTorusFlatFieldBranch4D

/-- Continuity of every unconstrained coordinate of an LL point field. -/
def ContinuousLLPointField {Base : Type*} [TopologicalSpace Base]
    (field : Base → LLBraneAuxiliaryPointData) : Prop :=
  Continuous (fun point => (field point).gammaInv) ∧
  Continuous (fun point => (field point).inducedMetric) ∧
  Continuous (fun point => (field point).Phi) ∧
  Continuous (fun point => (field point).gaugeFlux) ∧
  Continuous (fun point => (field point).gaugeCoupling) ∧
  Continuous (fun point => (field point).measureConstant)

/-- Concrete continuity predicate for all independent fields.  Lorentz metric
proofs are propositions, so continuity is imposed on their matrix values. -/
def IndependentFieldsContinuous
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    [TopologicalSpace Spacetime] [TopologicalSpace Throat]
    [TopologicalSpace Matter] [TopologicalSpace Gauge]
    [TopologicalSpace Ghost] [TopologicalSpace Auxiliary]
    [TopologicalSpace LLIndependent]
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) : Prop :=
  Continuous (fun point => (fields.plusMetric point).metric) ∧
  Continuous (fun point => (fields.minusMetric point).metric) ∧
  Continuous fields.plusMatter ∧
  Continuous fields.minusMatter ∧
  Continuous fields.plusGauge ∧
  Continuous fields.minusGauge ∧
  Continuous fields.plusGhost ∧
  Continuous fields.minusGhost ∧
  Continuous fields.plusAuxiliary ∧
  Continuous fields.minusAuxiliary ∧
  Continuous fields.throatEmbedding ∧
  Continuous fields.llIndependent

/-- Concrete continuity predicate for the fields induced from an independent
configuration. -/
def InducedFieldsContinuous
    {Spacetime Throat ThroatGeometry : Type*}
    [TopologicalSpace Spacetime] [TopologicalSpace Throat]
    [TopologicalSpace ThroatGeometry]
    (fields : InducedFields Spacetime Throat ThroatGeometry) : Prop :=
  Continuous fields.plusInverseMetric ∧
  Continuous fields.minusInverseMetric ∧
  Continuous fields.plusVolumeDensity ∧
  Continuous fields.minusVolumeDensity ∧
  Continuous fields.relativeRoot ∧
  Continuous fields.throatGeometry ∧
  ContinuousLLPointField fields.llPointData

theorem flatDiagonalIndependentFields_continuous
    (period : Real) (hPeriod : period ≠ 0) :
    IndependentFieldsContinuous
      (flatDiagonalIndependentFields period hPeriod) := by
  refine ⟨continuous_const, continuous_const, continuous_const,
    continuous_const, continuous_const, continuous_const, continuous_const,
    continuous_const, continuous_const, continuous_const, ?_, continuous_const⟩
  exact continuous_fixedThroatQuotientInclusion period hPeriod

theorem flatDiagonalInducedFields_continuous
    (period : Real) (hPeriod : period ≠ 0) :
    InducedFieldsContinuous (flatDiagonalInducedFields period hPeriod) := by
  refine ⟨continuous_const, continuous_const, continuous_const,
    continuous_const, continuous_const, continuous_const, ?_⟩
  exact ⟨continuous_const, continuous_const, continuous_const,
    continuous_const, continuous_const, continuous_const⟩

/-- A concrete continuous, PT-matched configuration on the effective D8
quotients.  The root equation refers to the same independent and induced
fields, rather than to a separate finite proxy. -/
structure ContinuousEffectiveConfiguration
    (period : Real) (hPeriod : period ≠ 0) where
  independent : IndependentFields
    (EffectiveJanusSpacetime period hPeriod)
    (EffectiveJanusThroat period hPeriod) Real Unit Unit Unit Unit
  induced : InducedFields
    (EffectiveJanusSpacetime period hPeriod)
    (EffectiveJanusThroat period hPeriod) Unit
  independent_continuous : IndependentFieldsContinuous independent
  induced_continuous : InducedFieldsContinuous induced
  throat_exact : independent.throatEmbedding =
    fixedThroatQuotientInclusion period hPeriod
  pt_fixed : independentPTExchange (flatIndependentPTData period hPeriod)
    independent = independent
  relative_root_square : ∀ point,
    induced.relativeRoot point * induced.relativeRoot point =
      induced.plusInverseMetric point * (independent.minusMetric point).metric

/-- The continuous effective configuration space is genuinely inhabited. -/
def flatContinuousEffectiveConfiguration
    (period : Real) (hPeriod : period ≠ 0) :
    ContinuousEffectiveConfiguration period hPeriod where
  independent := flatDiagonalIndependentFields period hPeriod
  induced := flatDiagonalInducedFields period hPeriod
  independent_continuous :=
    flatDiagonalIndependentFields_continuous period hPeriod
  induced_continuous := flatDiagonalInducedFields_continuous period hPeriod
  throat_exact := rfl
  pt_fixed := flatDiagonalIndependentFields_pt_fixed period hPeriod
  relative_root_square := flatDiagonal_relativeRoot_square period hPeriod

theorem continuous_effective_configuration_nonempty
    (period : Real) (hPeriod : period ≠ 0) :
    Nonempty (ContinuousEffectiveConfiguration period hPeriod) :=
  ⟨flatContinuousEffectiveConfiguration period hPeriod⟩

end

end P0EFTJanusMappingTorusContinuousFieldSpaces4D
end JanusFormal
