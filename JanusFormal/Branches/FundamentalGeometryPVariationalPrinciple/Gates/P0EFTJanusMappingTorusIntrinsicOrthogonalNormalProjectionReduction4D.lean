import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeometricNormalJunction4D

/-!
# Local projection reduction for the intrinsic normal metric

The differential-normal topology was transported through the previously
chosen pointwise equivalence `differentialNormalFiberEquiv`.  That choice has
no geometric regularity theorem.  Consequently the exact remaining statement
is local in the transported bundle charts: the metric-orthogonal projection
must preserve quotient classes and have a continuous squared length there.

This gate proves that this one local projection lemma glues to the global
`ContinuousOrthogonalDifferentialNormalLift`, and hence closes the complete
causal stratification.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicOrthogonalNormalProjectionReduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusGeometricNormalJunction4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusNormalCausalStratificationReduction4D
open P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev ThroatTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev AmbientTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev ThroatDifferentialRange
    (point : ThroatBase period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

private abbrev OrthogonalProjectionFamily :=
  ∀ point : ThroatBase period hPeriod,
    AmbientTangent period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point

/-- Squared intrinsic length after projecting the existing algebraic normal
representative to the metric-normal direction. -/
def projectedNormalMetricSquare
    (projection : OrthogonalProjectionFamily period hPeriod)
    (normal : DifferentialNormalTotalSpace period hPeriod) : Real :=
  let representative :=
    algebraicNormalRepresentative period hPeriod normal.1 normal.2
  let projected := projection normal.1 representative
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
    (fixedThroatQuotientInclusion period hPeriod normal.1)
    projected projected

/-- The same squared length in one transported differential-normal chart. -/
def localProjectedNormalMetricSquare
    (projection : OrthogonalProjectionFamily period hPeriod)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    ThroatBase period hPeriod × Real → Real :=
  projectedNormalMetricSquare period hPeriod projection ∘
    (differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm

/-- The unique remaining local projection lemma.  It is stated directly in
the transported charts, so it exposes the precise compatibility missing from
the arbitrary pointwise `differentialNormalFiberEquiv` choice. -/
def IntrinsicOrthogonalNormalProjectionLocalLemma : Prop :=
  ∃ projection : OrthogonalProjectionFamily period hPeriod,
    (∀ (point : ThroatBase period hPeriod)
        (vector : AmbientTangent period hPeriod point),
      (ThroatDifferentialRange period hPeriod point).mkQ
          (projection point vector) =
        (ThroatDifferentialRange period hPeriod point).mkQ vector) ∧
    (∀ (point : ThroatBase period hPeriod)
        (vector : AmbientTangent period hPeriod point)
        (tangent : ThroatTangent period hPeriod point),
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod point)
          (projection point vector)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0) ∧
    ∀ anchor : MappingTorusCover (fixedEquatorData period hPeriod),
      ContinuousOn
        (localProjectedNormalMetricSquare period hPeriod projection anchor)
        (differentialNormalLocalTriv period hPeriod anchor).target

/-- Local continuity in every transported chart glues to continuity on the
whole differential-normal total space. -/
theorem projectedNormalMetricSquare_continuous_of_local
    (projection : OrthogonalProjectionFamily period hPeriod)
    (hLocal : ∀ anchor : MappingTorusCover
        (fixedEquatorData period hPeriod),
      ContinuousOn
        (localProjectedNormalMetricSquare period hPeriod projection anchor)
        (differentialNormalLocalTriv period hPeriod anchor).target) :
    Continuous (projectedNormalMetricSquare period hPeriod projection) := by
  rw [continuous_iff_continuousAt]
  intro normal
  let anchor := normalBundleIndexAt period hPeriod normal.1
  let trivialization := differentialNormalLocalTriv period hPeriod anchor
  have hSource : normal ∈ trivialization.source := by
    change normal.1 ∈ normalBundleBaseSet period hPeriod anchor
    exact mem_normalBundleBaseSet_indexAt period hPeriod normal.1
  have hTarget : trivialization normal ∈ trivialization.target :=
    trivialization.toOpenPartialHomeomorph.map_source hSource
  have hLocalAt : ContinuousAt
      (localProjectedNormalMetricSquare period hPeriod projection anchor)
      (trivialization normal) :=
    (hLocal anchor (trivialization normal) hTarget).continuousAt
      (trivialization.toOpenPartialHomeomorph.open_target.mem_nhds hTarget)
  have hComposition := hLocalAt.comp
    (trivialization.toOpenPartialHomeomorph.continuousAt hSource)
  apply hComposition.congr_of_eventuallyEq
  filter_upwards
    [trivialization.toOpenPartialHomeomorph.open_source.mem_nhds hSource]
      with other hOther
  simp only [Function.comp_apply, localProjectedNormalMetricSquare]
  have hInverse :
      (differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm
          (trivialization other) = other := by
    change trivialization.toOpenPartialHomeomorph.symm (trivialization other) = other
    exact trivialization.toOpenPartialHomeomorph.left_inv hOther
  rw [hInverse]

/-- The pointwise lift obtained by first using the existing algebraic
splitting and then applying the intrinsic orthogonal projection. -/
def projectedDifferentialNormalLift
    (projection : OrthogonalProjectionFamily period hPeriod)
    (point : ThroatBase period hPeriod) :
    DifferentialNormalFiber period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point :=
  (projection point).comp
    (algebraicNormalRepresentative period hPeriod point)

/-- The single local projection lemma produces the exact global bridge used
by the causal-stratification gate. -/
def continuousOrthogonalDifferentialNormalLift_of_localProjection
    (hProjection :
      IntrinsicOrthogonalNormalProjectionLocalLemma period hPeriod) :
    ContinuousOrthogonalDifferentialNormalLift period hPeriod := by
  let projection := hProjection.choose
  have hClass := hProjection.choose_spec.1
  have hOrthogonal := hProjection.choose_spec.2.1
  have hLocal := hProjection.choose_spec.2.2
  refine
    { lift := projectedDifferentialNormalLift period hPeriod projection
      represents := ?_
      orthogonal := ?_
      continuous_metric_square := ?_ }
  · intro point normal
    exact (hClass point
      (algebraicNormalRepresentative period hPeriod point normal)).trans
        (algebraicNormalRepresentative_rightInverse period hPeriod point normal)
  · intro point normal tangent
    exact hOrthogonal point
      (algebraicNormalRepresentative period hPeriod point normal) tangent
  · change Continuous
      (projectedNormalMetricSquare period hPeriod projection)
    exact projectedNormalMetricSquare_continuous_of_local period hPeriod
      projection hLocal

/-- Conditional only on the single chart-local projection lemma, the actual
intrinsic metric now yields the complete normal causal stratification. -/
theorem intrinsicDifferentialNormalCausalStratification_of_localProjection
    (hProjection :
      IntrinsicOrthogonalNormalProjectionLocalLemma period hPeriod) :
    let bridge :=
      continuousOrthogonalDifferentialNormalLift_of_localProjection
        period hPeriod hProjection
    let form := intrinsicDifferentialNormalQuadraticForm period hPeriod bridge
    IsOpen (normalSpacelikeStratum period hPeriod form) ∧
      IsOpen (normalTimelikeStratum period hPeriod form) ∧
      IsClosed (normalNullStratum period hPeriod form) ∧
      IsOpen (normalNonNullStratum period hPeriod form) ∧
      IsClosed (normalJointStratum period hPeriod form) ∧
      normalJointStratum period hPeriod form ⊆
        normalNullStratum period hPeriod form ∧
      normalSpacelikeStratum period hPeriod form ∪
          normalTimelikeStratum period hPeriod form ∪
          normalNullStratum period hPeriod form = univ := by
  exact intrinsicDifferentialNormalCausalStratification period hPeriod
    (continuousOrthogonalDifferentialNormalLift_of_localProjection
      period hPeriod hProjection)

end

end P0EFTJanusMappingTorusIntrinsicOrthogonalNormalProjectionReduction4D
end JanusFormal
