import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D

/-!
# Geometric metric antifields as algebraic dual functionals

The existing canonical integrated metric-tensor pairing is bilinear.  This
gate packages it as the missing linear morphism from genuine smooth
two-metric antifields to the algebraic dual used by the coadjoint BRST layer.
Injectivity and equivariance are retained as explicit stronger obligations;
no nondegeneracy of the integrated pairing is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev MetricPair :=
  SmoothGeneralMetricTensorPair period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One geometric two-metric antifield evaluated against a smooth metric
variation through the canonical integrated pairing. -/
def generalMetricGeometricAntifieldFunctional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (antifield : MetricPair period hPeriod) :
    AlgebraicAntifield (MetricPair period hPeriod) where
  toFun := fun field =>
    canonicalGeneralMetricTensorPairPairing
      period hPeriod metrics antifield field
  map_add' := by
    intro first second
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        antifield
        (smoothGeneralMetricTensorPairAdd period hPeriod first second) =
      _
    exact canonicalGeneralMetricTensorPairPairing_add_right
      period hPeriod metrics antifield first second
  map_smul' := by
    intro coefficient field
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        antifield
        (smoothGeneralMetricTensorPairSMul period hPeriod coefficient field) =
      _
    simpa [smul_eq_mul] using
      canonicalGeneralMetricTensorPairPairing_smul_right
        period hPeriod metrics coefficient antifield field

/-- Linear realization of every genuine smooth metric antifield as an
algebraic functional. -/
def generalMetricGeometricAntifieldToAlgebraicDual
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    MetricPair period hPeriod →ₗ[Real]
      AlgebraicAntifield (MetricPair period hPeriod) where
  toFun :=
    generalMetricGeometricAntifieldFunctional
      period hPeriod metrics
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro field
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairAdd period hPeriod first second) field =
      _
    exact canonicalGeneralMetricTensorPairPairing_add_left
      period hPeriod metrics first second field
  map_smul' := by
    intro coefficient antifield
    apply LinearMap.ext
    intro field
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairSMul
          period hPeriod coefficient antifield) field =
      coefficient * canonicalGeneralMetricTensorPairPairing
        period hPeriod metrics antifield field
    exact canonicalGeneralMetricTensorPairPairing_smul_left
      period hPeriod metrics coefficient antifield field

@[simp]
theorem generalMetricGeometricAntifieldToAlgebraicDual_apply
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (antifield field : MetricPair period hPeriod) :
    generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics antifield field =
      canonicalGeneralMetricTensorPairPairing
        period hPeriod metrics antifield field :=
  rfl

/-- Coadjoint equivariance of the geometric realization is exactly the
integrated skew-adjointness identity for the tensorial Lie action. -/
theorem generalMetricGeometricAntifield_coadjointIntertwining_iff
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (MetricPair period hPeriod))
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield : MetricPair period hPeriod) :
    generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics
        (representation.action ghost antifield) =
      coadjointGhostAction period hPeriod representation ghost
        (generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics antifield) ↔
    ∀ field,
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          (representation.action ghost antifield) field +
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          antifield (representation.action ghost field) = 0 := by
  constructor
  · intro hIntertwining field
    have hApply := LinearMap.congr_fun hIntertwining field
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (representation.action ghost antifield) field =
      -canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        antifield (representation.action ghost field) at hApply
    linarith
  · intro hSkew
    apply LinearMap.ext
    intro field
    change canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (representation.action ghost antifield) field =
      -canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        antifield (representation.action ghost field)
    linarith [hSkew field]

/-- Specialized criterion for the supplied two-metric tensorial action. -/
theorem generalMetricPair_coadjointIntertwining_iff
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (actions : TensorialInfinitesimalLieActionData period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield : MetricPair period hPeriod) :
    generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics
        ((smoothGhostLieRepresentationProd period hPeriod
          actions.metric actions.metric).action ghost antifield) =
      coadjointGhostAction period hPeriod
        (smoothGhostLieRepresentationProd period hPeriod
          actions.metric actions.metric)
        ghost
        (generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics antifield) ↔
    ∀ field,
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          ((smoothGhostLieRepresentationProd period hPeriod
            actions.metric actions.metric).action ghost antifield) field +
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          antifield
          ((smoothGhostLieRepresentationProd period hPeriod
            actions.metric actions.metric).action ghost field) = 0 :=
  generalMetricGeometricAntifield_coadjointIntertwining_iff
    period hPeriod metrics
    (smoothGhostLieRepresentationProd period hPeriod
      actions.metric actions.metric)
    ghost antifield

/-- Exact remaining bridge from the geometric pairing realization to the
coadjoint tensorial antifield representation. -/
structure GeneralMetricGeometricCoadjointBridgeData
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (MetricPair period hPeriod)) : Prop where
  pairingNondegenerate :
    Function.Injective
      (generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics)
  coadjointIntertwining :
    ∀ ghost antifield,
      generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics
          (representation.action ghost antifield) =
        coadjointGhostAction period hPeriod
          representation
          ghost
          (generalMetricGeometricAntifieldToAlgebraicDual
            period hPeriod metrics antifield)

/-- Auditable certificate for the constructed, assumption-free part of the
geometric-to-algebraic dual bridge. -/
structure GeneralMetricGeometricAntifieldDualCertificate4D : Prop where
  realized :
    ∀ metrics antifield field,
      generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics antifield field =
        canonicalGeneralMetricTensorPairPairing
          period hPeriod metrics antifield field
  equivarianceCriterion :
    ∀ metrics representation ghost antifield,
      generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics
          (representation.action ghost antifield) =
        coadjointGhostAction period hPeriod representation ghost
          (generalMetricGeometricAntifieldToAlgebraicDual
            period hPeriod metrics antifield) ↔
      ∀ field,
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            (representation.action ghost antifield) field +
          canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            antifield (representation.action ghost field) = 0

def generalMetricGeometricAntifieldDualCertificate4D :
    GeneralMetricGeometricAntifieldDualCertificate4D
      period hPeriod where
  realized :=
    generalMetricGeometricAntifieldToAlgebraicDual_apply
      period hPeriod
  equivarianceCriterion :=
    generalMetricGeometricAntifield_coadjointIntertwining_iff
      period hPeriod

end
end P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
end JanusFormal
