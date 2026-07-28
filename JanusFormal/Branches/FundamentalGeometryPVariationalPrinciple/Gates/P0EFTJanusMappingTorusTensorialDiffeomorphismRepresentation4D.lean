import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D

/-!
# Tensorial diffeomorphism representations on the D8 quotient

The scalar pullback action was already functorial.  This gate proves the same
finite composition law for the genuine intrinsic gauge one-forms and
covariant two-tensors.  These are the finite geometric representation laws
whose infinitesimal bracket identity is required by nonlinear BRST.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

@[simp]
theorem pullbackGaugePotential_zero
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism 0 = 0 := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  rfl

theorem pullbackGaugePotential_smul
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism
        (coefficient • potential) =
      coefficient •
        pullbackGaugePotential period hPeriod diffeomorphism potential := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  rfl

/-- Pullback of intrinsic one-forms is a contravariant group action. -/
theorem pullbackGaugePotential_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod first
        (pullbackGaugePotential period hPeriod second potential) =
      pullbackGaugePotential period hPeriod (first.trans second) potential := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change
    potential.toFun component (second (first point))
        (mfderiv coverModelWithCorners coverModelWithCorners second
          (first point)
          (mfderiv coverModelWithCorners coverModelWithCorners first
            point tangent)) =
      potential.toFun component ((first.trans second) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (first.trans second) point tangent)
  rw [show (first.trans second : EffectiveQuotient period hPeriod →
      EffectiveQuotient period hPeriod) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (x := first point) (by simp))
    (first.contMDiff.mdifferentiableAt (x := point) (by simp))]
  rfl

/-- Pointwise pullback of a covariant two-tensor is functorial. -/
theorem pullbackTensorValue_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    pullbackTensorValue period hPeriod first
        (fun current =>
          pullbackTensorValue period hPeriod second tensor current) point =
      pullbackTensorValue period hPeriod (first.trans second) tensor point := by
  apply ContinuousLinearMap.ext
  intro firstVector
  apply ContinuousLinearMap.ext
  intro secondVector
  simp only [pullbackTensorValue_apply]
  rw [show (first.trans second : EffectiveQuotient period hPeriod →
      EffectiveQuotient period hPeriod) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (x := first point) (by simp))
    (first.contMDiff.mdifferentiableAt (x := point) (by simp))]
  rfl

/-- The two concrete tensorial pullbacks satisfy the finite representation
laws needed before differentiating to Lie derivatives. -/
structure TensorialDiffeomorphismRepresentationCertificate4D : Prop where
  gaugeTrans :
    ∀ first second potential,
      pullbackGaugePotential period hPeriod first
          (pullbackGaugePotential period hPeriod second potential) =
        pullbackGaugePotential period hPeriod (first.trans second) potential
  tensorTrans :
    ∀ first second tensor point,
      pullbackTensorValue period hPeriod first
          (fun current =>
            pullbackTensorValue period hPeriod second tensor current) point =
        pullbackTensorValue period hPeriod (first.trans second) tensor point

def tensorialDiffeomorphismRepresentationCertificate4D :
    TensorialDiffeomorphismRepresentationCertificate4D period hPeriod where
  gaugeTrans := pullbackGaugePotential_trans period hPeriod
  tensorTrans := pullbackTensorValue_trans period hPeriod

/-! ## Infinitesimal representation contract -/

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

/-- A genuine linear Lie action of smooth D8 ghosts on a geometric field
module. -/
structure SmoothGhostLieRepresentation
    (Field : Type*) [AddCommGroup Field] [Module Real Field] where
  action : Ghost period hPeriod →ₗ[Real] Field →ₗ[Real] Field
  bracket_action :
    ∀ first second field,
      action (smoothGhostLieBracket period hPeriod first second) field =
        action first (action second field) -
          action second (action first field)

/-- The precise pairwise obstruction occurring in the nonlinear BRST
square for any geometric representation. -/
def lieRepresentationBRSTPairObstruction
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (field : Field) : Field :=
  representation.action first (representation.action second field) -
    representation.action second (representation.action first field) -
      representation.action
        (smoothGhostLieBracket period hPeriod first second) field

@[simp]
theorem lieRepresentationBRSTPairObstruction_zero
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (field : Field) :
    lieRepresentationBRSTPairObstruction period hPeriod
      representation first second field = 0 := by
  rw [lieRepresentationBRSTPairObstruction,
    representation.bracket_action]
  abel

/-- The already proved scalar Lie derivative is the first unconditional
geometric instance of the common representation interface. -/
def smoothScalarGhostLieRepresentation :
    SmoothGhostLieRepresentation period hPeriod
      (CInfinityScalarField period hPeriod) where
  action :=
    { toFun := fun ghost =>
        { toFun := cInfinityScalarLieDerivative period hPeriod ghost
          map_add' :=
            cInfinityScalarLieDerivative_addScalar period hPeriod ghost
          map_smul' := fun coefficient scalar =>
            cInfinityScalarLieDerivative_smulScalar
              period hPeriod ghost coefficient scalar }
      map_add' := fun first second => by
        apply LinearMap.ext
        intro scalar
        exact cInfinityScalarLieDerivative_addGhost
          period hPeriod first second scalar
      map_smul' := fun coefficient ghost => by
        apply LinearMap.ext
        intro scalar
        exact cInfinityScalarLieDerivative_smulGhost
          period hPeriod coefficient ghost scalar }
  bracket_action :=
    cInfinityScalarLieDerivative_bracket period hPeriod

/-- Remaining geometric input: actual infinitesimal actions on the intrinsic
Maxwell one-form and symmetric metric tensor. -/
structure TensorialInfinitesimalLieActionData where
  gauge :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothAbelianGaugePotential period hPeriod)
  metric :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothSymmetricCovariantTwoTensor period hPeriod)

theorem scalar_geometric_nonlinear_brst_pair_square_zero
    (first second : Ghost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (smoothScalarGhostLieRepresentation period hPeriod)
      first second scalar = 0 :=
  lieRepresentationBRSTPairObstruction_zero period hPeriod
    (smoothScalarGhostLieRepresentation period hPeriod)
    first second scalar

end
end P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
end JanusFormal
