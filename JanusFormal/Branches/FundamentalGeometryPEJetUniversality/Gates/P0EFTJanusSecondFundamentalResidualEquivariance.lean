import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet

namespace JanusFormal
namespace P0EFTJanusSecondFundamentalResidualEquivariance

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

universe u v

open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusSecondFundamentalFormJet

variable {Tangent : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Tangent]
variable [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

/-- Orthogonal source-frame group at the point. -/
abbrev SourceOrthogonalGroup :=
  Tangent ≃ₗᵢ[ℝ] Tangent

/-- Residual product of tangent and normal orthogonal frame groups. -/
abbrev ResidualOrthogonalGroup
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :=
  SourceOrthogonalGroup (Tangent := Tangent) ×
    (NormalSpace derivative ≃ₗᵢ[ℝ] NormalSpace derivative)

/-- Standard residual action on a normal-valued two-covariant tensor,

`((a,b) · B)(x,y) = b(B(a⁻¹x,a⁻¹y))`.
-/
def actOnSecondFundamentalTensor
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (frame : ResidualOrthogonalGroup derivative)
    (form : Tangent → Tangent → NormalSpace derivative) :
    Tangent → Tangent → NormalSpace derivative :=
  fun x y =>
    frame.2 (form (frame.1.symm x) (frame.1.symm y))

@[simp]
theorem actOnSecondFundamentalTensor_one
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (form : Tangent → Tangent → NormalSpace derivative) :
    actOnSecondFundamentalTensor derivative
        (1 : ResidualOrthogonalGroup derivative) form = form := by
  funext x y
  simp [actOnSecondFundamentalTensor]

@[simp]
theorem actOnSecondFundamentalTensor_mul
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (first second : ResidualOrthogonalGroup derivative)
    (form : Tangent → Tangent → NormalSpace derivative) :
    actOnSecondFundamentalTensor derivative (first * second) form =
      actOnSecondFundamentalTensor derivative first
        (actOnSecondFundamentalTensor derivative second form) := by
  funext x y
  simp [actOnSecondFundamentalTensor, LinearIsometryEquiv.mul_def]

/-- The residual orthogonal action preserves symmetry of the second fundamental
form. -/
theorem actOnSecondFundamentalTensor_preserves_symmetry
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (frame : ResidualOrthogonalGroup derivative)
    (form : Tangent → Tangent → NormalSpace derivative)
    (hSymmetric : IsSymmetricTensor form) :
    IsSymmetricTensor
      (actOnSecondFundamentalTensor derivative frame form) := by
  intro x y
  simp only [actOnSecondFundamentalTensor]
  exact congrArg frame.2
    (hSymmetric (frame.1.symm x) (frame.1.symm y))

/-- Residual orthogonal action on a split adapted immersion two-jet. -/
def actOnAdaptedSplitJet
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (frame : ResidualOrthogonalGroup derivative)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    SplitImmersionSecondJet Tangent (NormalSpace derivative) where
  tangentialQuadratic x y :=
    frame.1
      (jet.tangentialQuadratic (frame.1.symm x) (frame.1.symm y))
  normalQuadratic :=
    actOnSecondFundamentalTensor derivative frame jet.normalQuadratic

@[simp]
theorem actOnAdaptedSplitJet_normalQuadratic
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (frame : ResidualOrthogonalGroup derivative)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    (actOnAdaptedSplitJet derivative frame jet).normalQuadratic =
      actOnSecondFundamentalTensor derivative frame
        jet.normalQuadratic := by
  rfl

@[simp]
theorem actOnAdaptedSplitJet_one
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    actOnAdaptedSplitJet derivative
        (1 : ResidualOrthogonalGroup derivative) jet = jet := by
  apply P0EFTJanusSecondJetNormalForm.SecondJetData.ext
  · funext x y
    simp [actOnAdaptedSplitJet]
  · exact actOnSecondFundamentalTensor_one derivative jet.normalQuadratic

@[simp]
theorem actOnAdaptedSplitJet_mul
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (first second : ResidualOrthogonalGroup derivative)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    actOnAdaptedSplitJet derivative (first * second) jet =
      actOnAdaptedSplitJet derivative first
        (actOnAdaptedSplitJet derivative second jet) := by
  apply P0EFTJanusSecondJetNormalForm.SecondJetData.ext
  · funext x y
    simp [actOnAdaptedSplitJet, LinearIsometryEquiv.mul_def]
  · exact actOnSecondFundamentalTensor_mul derivative first second
      jet.normalQuadratic

/-- The flat identification of the reduced tensor with the second fundamental
form is equivariant under the residual orthogonal group. -/
theorem flat_secondFundamentalForm_residual_equivariant
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (frame : ResidualOrthogonalGroup derivative)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    secondFundamentalForm derivative
        (flatConnectionSecondJet derivative
          (actOnAdaptedSplitJet derivative frame jet)) =
      actOnSecondFundamentalTensor derivative frame
        (secondFundamentalForm derivative
          (flatConnectionSecondJet derivative jet)) := by
  rw [flat_secondFundamentalForm_eq_normalQuadratic,
    flat_secondFundamentalForm_eq_normalQuadratic]
  rfl

/-- Residual-equivariance stage boundary. -/
structure ResidualSecondFundamentalStatus where
  tangentOrthogonalGroupConstructed : Prop
  normalOrthogonalGroupConstructed : Prop
  tensorActionDefined : Prop
  actionLawsProved : Prop
  symmetryPreserved : Prop
  flatIdentificationEquivariant : Prop
  smoothFrameChangeGermsConstructed : Prop
  orientedReductionConstructed : Prop
  spinCResidualLiftConstructed : Prop

/-- Closure of the full residual-frame stage. -/
def residualSecondFundamentalClosed
    (s : ResidualSecondFundamentalStatus) : Prop :=
  s.tangentOrthogonalGroupConstructed /\
  s.normalOrthogonalGroupConstructed /\
  s.tensorActionDefined /\
  s.actionLawsProved /\
  s.symmetryPreserved /\
  s.flatIdentificationEquivariant /\
  s.smoothFrameChangeGermsConstructed /\
  s.orientedReductionConstructed /\
  s.spinCResidualLiftConstructed

/-- The pointwise orthogonal representation does not itself provide a SpinC
lift of the residual frame group. -/
theorem missing_spinC_lift_blocks_full_residual_stage
    (s : ResidualSecondFundamentalStatus)
    (hMissing : Not s.spinCResidualLiftConstructed) :
    Not (residualSecondFundamentalClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2

end

end P0EFTJanusSecondFundamentalResidualEquivariance
end JanusFormal
