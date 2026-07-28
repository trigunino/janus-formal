import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatFiniteRankFunctionalMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoadjointAntifieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricTensorModule4D

/-!
# Geometric throat-metric antifields as algebraic duals

The canonical integrated throat pairing is packaged as a linear morphism
from genuine smooth throat tensors to the algebraic antifields used by BRST.
Its injectivity remains an explicit nondegeneracy obligation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatFiniteRankFunctionalMaster4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D
open P0EFTJanusProgramPThroatMetricTensorModule4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatPair :=
  SmoothThroatGeneralMetricTensorPair period hPeriod

/-- Evaluation of a genuine throat-metric antifield through the canonical
integrated pairing. -/
def throatMetricGeometricAntifieldFunctional
    (antifield : ThroatPair period hPeriod) :
    AlgebraicAntifield (ThroatPair period hPeriod) where
  toFun := fun field =>
    canonicalIntrinsicThroatTensorPairPairing
      period hPeriod antifield field
  map_add' := by
    intro first second
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        antifield
        (smoothThroatGeneralMetricTensorPairAdd
          period hPeriod first second) = _
    exact canonicalIntrinsicThroatTensorPairPairing_add_right
      period hPeriod antifield first second
  map_smul' := by
    intro coefficient field
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        antifield
        (smoothThroatGeneralMetricTensorPairSMul
          period hPeriod coefficient field) = _
    simpa [smul_eq_mul] using
      canonicalIntrinsicThroatTensorPairPairing_smul_right
        period hPeriod coefficient antifield field

/-- Linear realization of smooth throat-metric antifields in the algebraic
dual used by the coadjoint BRST construction. -/
def throatMetricGeometricAntifieldToAlgebraicDual :
    ThroatPair period hPeriod →ₗ[Real]
      AlgebraicAntifield (ThroatPair period hPeriod) where
  toFun := throatMetricGeometricAntifieldFunctional period hPeriod
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro field
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (smoothThroatGeneralMetricTensorPairAdd
          period hPeriod first second) field = _
    exact canonicalIntrinsicThroatTensorPairPairing_add_left
      period hPeriod first second field
  map_smul' := by
    intro coefficient antifield
    apply LinearMap.ext
    intro field
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (smoothThroatGeneralMetricTensorPairSMul
          period hPeriod coefficient antifield) field =
      coefficient *
        canonicalIntrinsicThroatTensorPairPairing
          period hPeriod antifield field
    exact canonicalIntrinsicThroatTensorPairPairing_smul_left
      period hPeriod coefficient antifield field

@[simp]
theorem throatMetricGeometricAntifieldToAlgebraicDual_apply
    (antifield field : ThroatPair period hPeriod) :
    throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod antifield field =
      canonicalIntrinsicThroatTensorPairPairing
        period hPeriod antifield field :=
  rfl

/-- Injectivity is exactly separation of smooth throat tensors by the
integrated pairing. -/
theorem throatMetricGeometricAntifieldToAlgebraicDual_injective_iff
    :
    Function.Injective
        (throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod) ↔
      ∀ antifield : ThroatPair period hPeriod,
        (∀ field,
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield field = 0) →
        antifield = 0 := by
  constructor
  · intro hInjective antifield hZero
    apply hInjective
    apply LinearMap.ext
    intro field
    change canonicalIntrinsicThroatTensorPairPairing
        period hPeriod antifield field =
      canonicalIntrinsicThroatTensorPairPairing
        period hPeriod 0 field
    rw [hZero field]
    change 0 =
      throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod 0 field
    simp
  · intro hSeparates first second hEqual
    have hDifference :
        throatMetricGeometricAntifieldToAlgebraicDual
            period hPeriod (first - second) = 0 := by
      rw [map_sub, hEqual, sub_self]
    have hZero :
        ∀ field,
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod (first - second) field = 0 := by
      intro field
      have hApply := LinearMap.congr_fun hDifference field
      exact hApply
    exact sub_eq_zero.mp (hSeparates (first - second) hZero)

/-- Diagonal definiteness is a sufficient, auditable route to injectivity. -/
theorem throatMetricGeometricAntifieldToAlgebraicDual_injective_of_diagonal
    (hDiagonal :
      ∀ antifield : ThroatPair period hPeriod,
        canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield antifield = 0 →
          antifield = 0) :
    Function.Injective
      (throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod) := by
  rw [throatMetricGeometricAntifieldToAlgebraicDual_injective_iff]
  intro antifield hZero
  exact hDiagonal antifield (hZero antifield)

/-- Coadjoint equivariance of the throat realization is exactly integrated
skew-adjointness for any supplied ghost Lie representation. -/
theorem throatMetricGeometricAntifield_coadjointIntertwining_iff
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (ThroatPair period hPeriod))
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield : ThroatPair period hPeriod) :
    throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod
        (representation.action ghost antifield) =
      coadjointGhostAction period hPeriod representation ghost
        (throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod antifield) ↔
    ∀ field,
      canonicalIntrinsicThroatTensorPairPairing period hPeriod
          (representation.action ghost antifield) field +
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
          antifield (representation.action ghost field) = 0 := by
  constructor
  · intro hIntertwining field
    have hApply := LinearMap.congr_fun hIntertwining field
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (representation.action ghost antifield) field =
      -canonicalIntrinsicThroatTensorPairPairing period hPeriod
        antifield (representation.action ghost field) at hApply
    linarith
  · intro hSkew
    apply LinearMap.ext
    intro field
    change canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (representation.action ghost antifield) field =
      -canonicalIntrinsicThroatTensorPairPairing period hPeriod
        antifield (representation.action ghost field)
    linarith [hSkew field]

/-- Faithful coadjoint realization of the genuine throat tensors for one
supplied geometric ghost representation. -/
structure ThroatMetricGeometricCoadjointBridgeData
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (ThroatPair period hPeriod)) : Prop where
  pairingNondegenerate :
    Function.Injective
      (throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod)
  coadjointIntertwining :
    ∀ ghost antifield,
      throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod
          (representation.action ghost antifield) =
        coadjointGhostAction period hPeriod representation ghost
          (throatMetricGeometricAntifieldToAlgebraicDual
            period hPeriod antifield)

/-- Bilinear separation and integrated skew-adjointness are the exact inputs
for the faithful coadjoint bridge. -/
def throatMetricGeometricCoadjointBridgeData_of_separation_skew
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (ThroatPair period hPeriod))
    (hSeparates :
      ∀ antifield : ThroatPair period hPeriod,
        (∀ field,
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield field = 0) →
        antifield = 0)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation where
  pairingNondegenerate :=
    (throatMetricGeometricAntifieldToAlgebraicDual_injective_iff
      period hPeriod).2 hSeparates
  coadjointIntertwining := by
    intro ghost antifield
    exact
      (throatMetricGeometricAntifield_coadjointIntertwining_iff
        period hPeriod representation ghost antifield).2
        (hSkew ghost antifield)

/-- Diagonal definiteness and integrated skew-adjointness construct the full
faithful coadjoint bridge, with no further algebraic obligation. -/
def throatMetricGeometricCoadjointBridgeData_of_diagonal_skew
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (ThroatPair period hPeriod))
    (hDiagonal :
      ∀ antifield : ThroatPair period hPeriod,
        canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield antifield = 0 →
          antifield = 0)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation where
  pairingNondegenerate :=
    throatMetricGeometricAntifieldToAlgebraicDual_injective_of_diagonal
      period hPeriod hDiagonal
  coadjointIntertwining := by
    intro ghost antifield
    exact
      (throatMetricGeometricAntifield_coadjointIntertwining_iff
        period hPeriod representation ghost antifield).2
        (hSkew ghost antifield)

/-- Exact remaining condition for faithful geometric realization. -/
structure ThroatMetricGeometricDualNondegeneracy : Prop where
  pairingNondegenerate :
    Function.Injective
      (throatMetricGeometricAntifieldToAlgebraicDual
        period hPeriod)

/-- Auditable certificate for the unconditional realization. -/
structure ThroatMetricGeometricAntifieldDualCertificate4D : Prop where
  realized :
    ∀ antifield field,
      throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod antifield field =
        canonicalIntrinsicThroatTensorPairPairing
          period hPeriod antifield field
  injectivityCriterion :
    Function.Injective
        (throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod) ↔
      ∀ antifield,
        (∀ field,
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield field = 0) →
        antifield = 0
  equivarianceCriterion :
    ∀ representation ghost antifield,
      throatMetricGeometricAntifieldToAlgebraicDual
          period hPeriod
          (representation.action ghost antifield) =
        coadjointGhostAction period hPeriod representation ghost
          (throatMetricGeometricAntifieldToAlgebraicDual
            period hPeriod antifield) ↔
      ∀ field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0

def throatMetricGeometricAntifieldDualCertificate4D :
    ThroatMetricGeometricAntifieldDualCertificate4D
      period hPeriod where
  realized :=
    throatMetricGeometricAntifieldToAlgebraicDual_apply
      period hPeriod
  injectivityCriterion :=
    throatMetricGeometricAntifieldToAlgebraicDual_injective_iff
      period hPeriod
  equivarianceCriterion :=
    throatMetricGeometricAntifield_coadjointIntertwining_iff
      period hPeriod

end
end P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
end JanusFormal
