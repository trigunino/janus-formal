import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMovingAdaptedFrameSecondJet

namespace JanusFormal
namespace P0EFTJanusMovingNormalTransport

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusSecondFundamentalFormJet
open P0EFTJanusMovingAdaptedFrameSecondJet

universe u v

variable {Tangent : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Tangent]
variable [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

/-- An orthogonal ambient frame sends the old normal subspace to the normal
subspace of the transformed immersion derivative. -/
theorem map_normalSpace_eq
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    (NormalSpace derivative).map frame.value.toLinearEquiv.toLinearMap =
      NormalSpace (transformedDerivative frame derivative) := by
  ext vector
  constructor
  · rintro ⟨normal, hNormal, rfl⟩
    intro tangentVector hTangent
    rcases hTangent with ⟨x, rfl⟩
    simpa [transformedDerivative_apply] using
      hNormal (derivative x) (derivative_mem_tangentRange derivative x)
  · intro hNormal
    refine ⟨frame.value.symm vector, ?_, by simp⟩
    intro tangentVector hTangent
    rcases hTangent with ⟨x, rfl⟩
    have hTransformed := hNormal
      (transformedDerivative frame derivative x)
      (derivative_mem_tangentRange
        (transformedDerivative frame derivative) x)
    calc
      inner ℝ (derivative x) (frame.value.symm vector) =
          inner ℝ (frame.value (derivative x))
            (frame.value (frame.value.symm vector)) :=
        (frame.value.inner_map_map _ _).symm
      _ = inner ℝ (transformedDerivative frame derivative x) vector := by
        simp
      _ = 0 := hTransformed

/-- Canonical isometric transport from the old normal space to the transformed
normal space. -/
def normalTransport
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    NormalSpace derivative ≃ₗᵢ[ℝ]
      NormalSpace (transformedDerivative frame derivative) :=
  (LinearIsometryEquiv.submoduleMap (NormalSpace derivative) frame.value).trans
    (LinearIsometryEquiv.ofEq _ _ (map_normalSpace_eq frame derivative))

@[simp]
theorem normalTransport_coe
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (normal : NormalSpace derivative) :
    ((normalTransport frame derivative normal :
        NormalSpace (transformedDerivative frame derivative)) : Ambient) =
      frame.value normal := by
  rfl

/-- Orthogonal projection commutes with the canonical normal transport induced
by an ambient orthogonal frame. -/
theorem normalProjection_movingFrame
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (vector : Ambient) :
    normalTransport frame derivative (normalProjection derivative vector) =
      normalProjection (transformedDerivative frame derivative)
        (frame.value vector) := by
  apply Subtype.ext
  change frame.value ((NormalSpace derivative).starProjection vector) =
    (NormalSpace (transformedDerivative frame derivative)).starProjection
      (frame.value vector)
  have hProjection := frame.value.toLinearIsometry.map_starProjection
    (NormalSpace derivative) vector
  rw [map_normalSpace_eq frame derivative] at hProjection
  exact hProjection

/-- The pointwise second fundamental form is equivariant under a moving ambient
orthogonal frame once its derivative terms are compensated by the ambient
connection transformation. -/
theorem secondFundamentalForm_movingAmbientFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    (fun x y => normalTransport frame derivative
      (secondFundamentalForm derivative jet x y)) =
      secondFundamentalForm (transformedDerivative frame derivative)
        (movingAmbientFrameChange frame derivative jet) := by
  funext x y
  rw [secondFundamentalForm, secondFundamentalForm,
    normalProjection_movingFrame]
  have hCovariant := congrFun
    (congrFun
      (covariantSecondDerivative_movingAmbientFrameChange
        frame derivative jet) x) y
  exact congrArg
    (normalProjection (transformedDerivative frame derivative))
    hCovariant.symm

/-- Source-coordinate corrections disappear before the normal transport, so the
same equivariance theorem holds for the complete moving adapted-frame change. -/
theorem secondFundamentalForm_movingAdaptedFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (sourceChange : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    (fun x y => normalTransport frame derivative
      (secondFundamentalForm derivative jet x y)) =
      secondFundamentalForm (transformedDerivative frame derivative)
        (movingAdaptedFrameChange frame derivative sourceChange jet) := by
  rw [movingAdaptedFrameChange,
    ← secondFundamentalForm_sourceCoordinateChange derivative sourceChange jet]
  exact secondFundamentalForm_movingAmbientFrameChange frame derivative
    (sourceCoordinateChange derivative sourceChange jet)

/-- S5.3 normal-transport closure status. -/
structure MovingNormalTransportStatus where
  normalSubspaceMapIdentified : Prop
  normalTransportConstructed : Prop
  normalProjectionNaturalityProved : Prop
  secondFundamentalFormMovingFrameEquivarianceProved : Prop
  combinedSourceAmbientEquivarianceProved : Prop
  frameJetExtractedFromSmoothFrame : Prop
  smoothNormalBundleTransportConstructed : Prop
  manifoldOverlapCocycleProved : Prop
  orientedReductionConstructed : Prop
  spinCNormalTransportLifted : Prop

/-- Closure of the manifold-level moving-normal stage. -/
def movingNormalTransportClosed
    (s : MovingNormalTransportStatus) : Prop :=
  s.normalSubspaceMapIdentified /\
  s.normalTransportConstructed /\
  s.normalProjectionNaturalityProved /\
  s.secondFundamentalFormMovingFrameEquivarianceProved /\
  s.combinedSourceAmbientEquivarianceProved /\
  s.frameJetExtractedFromSmoothFrame /\
  s.smoothNormalBundleTransportConstructed /\
  s.manifoldOverlapCocycleProved /\
  s.orientedReductionConstructed /\
  s.spinCNormalTransportLifted

/-- Pointwise normal transport still needs to be packaged as a smooth bundle map
on overlapping manifold charts. -/
theorem missing_overlap_cocycle_blocks_full_moving_normal_stage
    (s : MovingNormalTransportStatus)
    (hMissing : Not s.manifoldOverlapCocycleProved) :
    Not (movingNormalTransportClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusMovingNormalTransport
end JanusFormal
