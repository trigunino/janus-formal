import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderStructuredBackground

namespace JanusFormal
namespace P0EFTJanusAdaptedOrthogonalSplitting

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open Module

universe u v

variable {Tangent : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Tangent]
variable [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

/-- Tangent image of a linear isometric immersion derivative. -/
def tangentRange (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Submodule ℝ Ambient :=
  LinearMap.range derivative.toLinearMap

/-- The intrinsic normal model associated with the immersion derivative. -/
abbrev NormalSpace (derivative : Tangent →ₗᵢ[ℝ] Ambient) :=
  (tangentRange derivative)ᗮ

/-- The derivative identifies the abstract tangent space isometrically with its
image subspace in the ambient space. -/
def tangentEquivRange (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Tangent ≃ₗᵢ[ℝ] tangentRange derivative :=
  derivative.equivRange

/-- Ambient adapted orthogonal coordinates: tangent image plus its orthogonal
complement, with the `L²` product norm. -/
def adaptedAmbientCoordinates
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Ambient ≃ₗᵢ[ℝ]
      WithLp 2 (tangentRange derivative × NormalSpace derivative) :=
  (tangentRange derivative).orthogonalDecomposition

/-- Canonical point of the tangent-image subspace corresponding to a source
vector. -/
def tangentRangePoint
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) : tangentRange derivative :=
  tangentEquivRange derivative x

@[simp]
theorem tangentRangePoint_coe
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    ((tangentRangePoint derivative x : tangentRange derivative) : Ambient) =
      derivative x := by
  rfl

/-- The immersion derivative lands in its tangent image. -/
theorem derivative_mem_tangentRange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    derivative x ∈ tangentRange derivative := by
  exact ⟨x, rfl⟩

/-- In adapted ambient coordinates, the tangent component of the derivative is
exactly the range point induced by the original source vector. -/
theorem adapted_derivative_fst
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    (adaptedAmbientCoordinates derivative (derivative x)).fst =
      tangentRangePoint derivative x := by
  rw [Submodule.fst_orthogonalDecomposition_apply]
  apply Subtype.ext
  change (tangentRange derivative).starProjection (derivative x) =
    derivative x
  exact (tangentRange derivative).starProjection_eq_self_iff.mpr
    (derivative_mem_tangentRange derivative x)

/-- In adapted ambient coordinates, the normal component of the derivative
vanishes. -/
theorem adapted_derivative_snd
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    (adaptedAmbientCoordinates derivative (derivative x)).snd = 0 := by
  rw [Submodule.snd_orthogonalDecomposition_apply]
  apply Subtype.ext
  change ((tangentRange derivative)ᗮ).starProjection (derivative x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact Submodule.le_orthogonal_orthogonal (derivative_mem_tangentRange derivative x)

/-- First-order adapted-frame theorem: after the canonical orthogonal splitting,
the immersion derivative is the standard inclusion into the tangent-image factor. -/
theorem adapted_derivative_is_standard_inclusion
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    adaptedAmbientCoordinates derivative (derivative x) =
      WithLp.toLp 2 (tangentRangePoint derivative x, 0) := by
  apply Prod.ext
  · exact adapted_derivative_fst derivative x
  · exact adapted_derivative_snd derivative x

/-- The tangent range is isometrically equivalent to the original tangent space. -/
theorem tangent_range_finrank
    [FiniteDimensional ℝ Tangent]
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    finrank ℝ (tangentRange derivative) = finrank ℝ Tangent := by
  exact LinearEquiv.finrank_eq (tangentEquivRange derivative).toLinearEquiv

/-- The adapted splitting yields the expected codimension identity. -/
theorem tangent_plus_normal_finrank
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    finrank ℝ (tangentRange derivative) +
        finrank ℝ (NormalSpace derivative) =
      finrank ℝ Ambient := by
  exact Submodule.finrank_add_finrank_orthogonal (tangentRange derivative)

/-- Concrete orthogonal groups acting on the two factors after first-order
normalization. -/
abbrev TangentOrthogonalGroup
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :=
  tangentRange derivative ≃ₗᵢ[ℝ] tangentRange derivative

abbrev NormalOrthogonalGroup
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :=
  NormalSpace derivative ≃ₗᵢ[ℝ] NormalSpace derivative

/-- The exact progress boundary: first-order orthogonal normalization is now a
Lean theorem for a linear isometric derivative, while the manifold-level adapted
frame field and geometric second fundamental form remain separate tasks. -/
structure AdaptedOrthogonalSplittingStatus where
  derivativeModeledAsLinearIsometry : Prop
  tangentRangeConstructed : Prop
  orthogonalNormalSpaceConstructed : Prop
  ambientOrthogonalDecompositionConstructed : Prop
  derivativeStandardInclusionProved : Prop
  codimensionIdentityProved : Prop
  residualOrthogonalGroupsIdentified : Prop
  smoothLocalAdaptedFrameFieldConstructed : Prop
  secondDerivativeTransportedThroughFrameJets : Prop
  normalQuadraticTensorIdentifiedWithSecondFundamentalForm : Prop
  spinCFrameLiftConstructed : Prop

/-- Closure of the geometric adapted-frame stage. -/
def adaptedOrthogonalSplittingClosed
    (s : AdaptedOrthogonalSplittingStatus) : Prop :=
  s.derivativeModeledAsLinearIsometry /\
  s.tangentRangeConstructed /\
  s.orthogonalNormalSpaceConstructed /\
  s.ambientOrthogonalDecompositionConstructed /\
  s.derivativeStandardInclusionProved /\
  s.codimensionIdentityProved /\
  s.residualOrthogonalGroupsIdentified /\
  s.smoothLocalAdaptedFrameFieldConstructed /\
  s.secondDerivativeTransportedThroughFrameJets /\
  s.normalQuadraticTensorIdentifiedWithSecondFundamentalForm /\
  s.spinCFrameLiftConstructed

/-- Pointwise orthogonal splitting does not by itself construct a smooth adapted
frame field near the base point. -/
theorem missing_smooth_frame_field_blocks_geometric_stage
    (s : AdaptedOrthogonalSplittingStatus)
    (hMissing : Not s.smoothLocalAdaptedFrameFieldConstructed) :
    Not (adaptedOrthogonalSplittingClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusAdaptedOrthogonalSplitting
end JanusFormal
