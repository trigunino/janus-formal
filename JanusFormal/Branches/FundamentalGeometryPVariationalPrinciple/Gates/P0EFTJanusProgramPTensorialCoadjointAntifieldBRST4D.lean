import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoadjointAntifieldBRST4D

/-!
# Tensorial coadjoint antifield BRST specialization

Any supplied Maxwell/metric infinitesimal Lie-action data already contains
the bracket identity.  This gate forms the two-metric product representation
and canonically derives the algebraic Maxwell and metric-pair antifield
representations, including square-zero and pairing invariance.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Direct product of two representations of the same smooth ghost algebra. -/
def smoothGhostLieRepresentationProd
    {First Second : Type*}
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second]
    (first : SmoothGhostLieRepresentation period hPeriod First)
    (second : SmoothGhostLieRepresentation period hPeriod Second) :
    SmoothGhostLieRepresentation period hPeriod (First × Second) where
  action :=
    { toFun := fun ghost =>
        { toFun := fun field =>
            (first.action ghost field.1, second.action ghost field.2)
          map_add' := by
            intro left right
            simp
          map_smul' := by
            intro coefficient field
            simp }
      map_add' := by
        intro left right
        apply LinearMap.ext
        intro field
        simp
      map_smul' := by
        intro coefficient ghost
        apply LinearMap.ext
        intro field
        simp }
  bracket_action := by
    intro left right field
    apply Prod.ext
    · exact first.bracket_action left right field.1
    · exact second.bracket_action left right field.2

/-- Algebraic field/antifield representations induced simultaneously on the
Maxwell potential and on the two-metric tangent pair. -/
structure TensorialFieldAntifieldLieRepresentationData where
  gauge :
    FieldAntifieldLieRepresentation period hPeriod
      (SmoothAbelianGaugePotential period hPeriod)
  metricPair :
    FieldAntifieldLieRepresentation period hPeriod
      (SmoothSymmetricCovariantTwoTensor period hPeriod ×
        SmoothSymmetricCovariantTwoTensor period hPeriod)

def tensorialFieldAntifieldLieRepresentationData
    (actions : TensorialInfinitesimalLieActionData period hPeriod) :
    TensorialFieldAntifieldLieRepresentationData period hPeriod where
  gauge :=
    canonicalFieldAntifieldLieRepresentation
      period hPeriod actions.gauge
  metricPair :=
    canonicalFieldAntifieldLieRepresentation period hPeriod
      (smoothGhostLieRepresentationProd period hPeriod
        actions.metric actions.metric)

/-- Nonlinear BRST square-zero on algebraic Maxwell antifields. -/
theorem gaugeAntifield_nonlinear_brst_pair_square_zero
    (actions : TensorialInfinitesimalLieActionData period hPeriod)
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield :
      AlgebraicAntifield (SmoothAbelianGaugePotential period hPeriod)) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (tensorialFieldAntifieldLieRepresentationData
        period hPeriod actions).gauge.antifield
      first second antifield = 0 :=
  coadjoint_antifield_nonlinear_brst_pair_square_zero
    period hPeriod actions.gauge first second antifield

/-- Nonlinear BRST square-zero on algebraic two-metric antifields. -/
theorem metricPairAntifield_nonlinear_brst_pair_square_zero
    (actions : TensorialInfinitesimalLieActionData period hPeriod)
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield : AlgebraicAntifield
      (SmoothSymmetricCovariantTwoTensor period hPeriod ×
        SmoothSymmetricCovariantTwoTensor period hPeriod)) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (tensorialFieldAntifieldLieRepresentationData
        period hPeriod actions).metricPair.antifield
      first second antifield = 0 :=
  coadjoint_antifield_nonlinear_brst_pair_square_zero period hPeriod
    (smoothGhostLieRepresentationProd period hPeriod
      actions.metric actions.metric)
    first second antifield

/-- Canonical Maxwell field-antifield pairing is invariant. -/
theorem gaugeFieldAntifieldPairing_brst_invariant
    (actions : TensorialInfinitesimalLieActionData period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield :
      AlgebraicAntifield (SmoothAbelianGaugePotential period hPeriod))
    (field : SmoothAbelianGaugePotential period hPeriod) :
    fieldAntifieldPairing
        (coadjointGhostAction period hPeriod actions.gauge ghost antifield)
        field +
      fieldAntifieldPairing antifield
        (actions.gauge.action ghost field) = 0 :=
  fieldAntifieldPairing_brst_invariant
    period hPeriod actions.gauge ghost antifield field

/-- Canonical two-metric field-antifield pairing is invariant. -/
theorem metricPairFieldAntifieldPairing_brst_invariant
    (actions : TensorialInfinitesimalLieActionData period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield : AlgebraicAntifield
      (SmoothSymmetricCovariantTwoTensor period hPeriod ×
        SmoothSymmetricCovariantTwoTensor period hPeriod))
    (field : SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fieldAntifieldPairing
        (coadjointGhostAction period hPeriod
          (smoothGhostLieRepresentationProd period hPeriod
            actions.metric actions.metric) ghost antifield) field +
      fieldAntifieldPairing antifield
        ((smoothGhostLieRepresentationProd period hPeriod
          actions.metric actions.metric).action ghost field) = 0 :=
  fieldAntifieldPairing_brst_invariant period hPeriod
    (smoothGhostLieRepresentationProd period hPeriod
      actions.metric actions.metric)
    ghost antifield field

/-- Exact tensorial antifield closure from Maxwell/metric infinitesimal
Lie-action data; the canonical geometric data are supplied downstream. -/
structure TensorialCoadjointAntifieldBRSTCertificate4D
    (actions : TensorialInfinitesimalLieActionData period hPeriod) : Prop where
  gaugeSquareZero :
    ∀ first second antifield,
      lieRepresentationBRSTPairObstruction period hPeriod
        (tensorialFieldAntifieldLieRepresentationData
          period hPeriod actions).gauge.antifield
        first second antifield = 0
  metricPairSquareZero :
    ∀ first second antifield,
      lieRepresentationBRSTPairObstruction period hPeriod
        (tensorialFieldAntifieldLieRepresentationData
          period hPeriod actions).metricPair.antifield
        first second antifield = 0

def tensorialCoadjointAntifieldBRSTCertificate4D
    (actions : TensorialInfinitesimalLieActionData period hPeriod) :
    TensorialCoadjointAntifieldBRSTCertificate4D
      period hPeriod actions where
  gaugeSquareZero :=
    gaugeAntifield_nonlinear_brst_pair_square_zero
      period hPeriod actions
  metricPairSquareZero :=
    metricPairAntifield_nonlinear_brst_pair_square_zero
      period hPeriod actions

end
end P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
end JanusFormal
