import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedOrthogonalSplitting

namespace JanusFormal
namespace P0EFTJanusSecondFundamentalFormJet

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

universe u v

open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusAdaptedOrthogonalSplitting

variable {Tangent : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Tangent]
variable [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

/-- Pointwise second-order geometric data in local coordinates. The ambient and
source connection terms encode the Christoffel contributions at the base point.
No manifold-level connection is assumed in this algebraic jet model. -/
@[ext]
structure ConnectionCorrectedSecondJet
    (Tangent : Type u) (Ambient : Type v) where
  rawSecond : Tangent → Tangent → Ambient
  ambientConnection : Tangent → Tangent → Ambient
  sourceConnection : Tangent → Tangent → Tangent

/-- Covariant second derivative of the immersion at the chosen point,

`D²i + Γᴹ(di,di) - di(ΓΣ)`.
-/
def covariantSecondDerivative
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    Tangent → Tangent → Ambient :=
  fun x y =>
    jet.rawSecond x y + jet.ambientConnection x y -
      derivative (jet.sourceConnection x y)

/-- Orthogonal projection to the normal space determined by the immersion
first derivative. -/
def normalProjection
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Ambient →L[ℝ] NormalSpace derivative :=
  (NormalSpace derivative).orthogonalProjectionOnto

/-- Pointwise second fundamental form: the normal projection of the covariant
second derivative. -/
def secondFundamentalForm
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    Tangent → Tangent → NormalSpace derivative :=
  fun x y => normalProjection derivative
    (covariantSecondDerivative derivative jet x y)

/-- Tangential vectors have zero normal projection. -/
@[simp]
theorem normalProjection_derivative_eq_zero
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    normalProjection derivative (derivative x) = 0 := by
  apply Subtype.ext
  change (NormalSpace derivative).starProjection (derivative x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact Submodule.le_orthogonal_orthogonal (tangentRange derivative)
    (derivative_mem_tangentRange derivative x)

/-- The source Levi-Civita/Christoffel correction is tangent-valued and therefore
drops out after normal projection. -/
theorem secondFundamentalForm_eq_projected_raw_plus_ambient
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (x y : Tangent) :
    secondFundamentalForm derivative jet x y =
      normalProjection derivative
        (jet.rawSecond x y + jet.ambientConnection x y) := by
  simp only [secondFundamentalForm, covariantSecondDerivative]
  rw [map_sub, normalProjection_derivative_eq_zero, sub_zero]

/-- Source-coordinate two-jet change. The raw second derivative and the source
connection coefficient acquire the same tangent-valued correction, so the
covariant second derivative is unchanged. -/
def sourceCoordinateChange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (change : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond x y := jet.rawSecond x y + derivative (change x y)
  ambientConnection := jet.ambientConnection
  sourceConnection x y := jet.sourceConnection x y + change x y

/-- The covariant second derivative is invariant under the paired source
coordinate transformation. -/
theorem covariantSecondDerivative_sourceCoordinateChange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (change : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    covariantSecondDerivative derivative
        (sourceCoordinateChange derivative change jet) =
      covariantSecondDerivative derivative jet := by
  funext x y
  simp only [covariantSecondDerivative, sourceCoordinateChange,
    LinearIsometry.map_add]
  abel

/-- Consequently, the pointwise second fundamental form is independent of the
source coordinate two-jet. -/
theorem secondFundamentalForm_sourceCoordinateChange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (change : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    secondFundamentalForm derivative
        (sourceCoordinateChange derivative change jet) =
      secondFundamentalForm derivative jet := by
  funext x y
  simp only [secondFundamentalForm,
    covariantSecondDerivative_sourceCoordinateChange]

/-- Ambient-coordinate two-jet change. The quadratic coordinate term enters the
raw second derivative and the ambient Christoffel correction with opposite
signs. -/
def ambientCoordinateChange
    (change : Tangent → Tangent → Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond x y := jet.rawSecond x y + change x y
  ambientConnection x y := jet.ambientConnection x y - change x y
  sourceConnection := jet.sourceConnection

/-- The connection-corrected second derivative is also invariant under the
paired ambient coordinate transformation. -/
theorem covariantSecondDerivative_ambientCoordinateChange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (change : Tangent → Tangent → Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    covariantSecondDerivative derivative
        (ambientCoordinateChange change jet) =
      covariantSecondDerivative derivative jet := by
  funext x y
  simp only [covariantSecondDerivative, ambientCoordinateChange]
  abel

/-- Therefore the second fundamental form is independent of the ambient
coordinate two-jet as well. -/
theorem secondFundamentalForm_ambientCoordinateChange
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (change : Tangent → Tangent → Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    secondFundamentalForm derivative
        (ambientCoordinateChange change jet) =
      secondFundamentalForm derivative jet := by
  funext x y
  simp only [secondFundamentalForm,
    covariantSecondDerivative_ambientCoordinateChange]

/-- Symmetry predicate for a two-covariant tensor. -/
def IsSymmetricTensor
    {Target : Type*}
    (tensor : Tangent → Tangent → Target) : Prop :=
  ∀ x y, tensor x y = tensor y x

/-- If the raw Hessian and both torsion-free connection coefficients are
symmetric, then the covariant second derivative is symmetric. -/
theorem covariantSecondDerivative_isSymmetric
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (hRaw : IsSymmetricTensor jet.rawSecond)
    (hAmbient : IsSymmetricTensor jet.ambientConnection)
    (hSource : IsSymmetricTensor jet.sourceConnection) :
    IsSymmetricTensor (covariantSecondDerivative derivative jet) := by
  intro x y
  simp only [covariantSecondDerivative]
  rw [hRaw x y, hAmbient x y, hSource x y]

/-- Under the same torsion-free hypotheses, the second fundamental form is
symmetric. -/
theorem secondFundamentalForm_isSymmetric
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (hRaw : IsSymmetricTensor jet.rawSecond)
    (hAmbient : IsSymmetricTensor jet.ambientConnection)
    (hSource : IsSymmetricTensor jet.sourceConnection) :
    IsSymmetricTensor (secondFundamentalForm derivative jet) := by
  intro x y
  exact congrArg (normalProjection derivative)
    (covariantSecondDerivative_isSymmetric derivative jet
      hRaw hAmbient hSource x y)

/-- The normal projection is exactly the second coordinate in the canonical
orthogonal splitting. -/
theorem adapted_snd_eq_normalProjection
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (vector : Ambient) :
    (adaptedAmbientCoordinates derivative vector).snd =
      normalProjection derivative vector := by
  change
    (((tangentRange derivative).orthogonalDecomposition vector).snd =
      (NormalSpace derivative).orthogonalProjectionOnto vector)
  exact Submodule.snd_orthogonalDecomposition_apply
    (tangentRange derivative) vector

/-- Hence the second fundamental form is the normal component of the covariant
second derivative in adapted orthogonal coordinates. -/
theorem adapted_snd_covariantSecondDerivative_eq_secondFundamentalForm
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (x y : Tangent) :
    (adaptedAmbientCoordinates derivative
      (covariantSecondDerivative derivative jet x y)).snd =
        secondFundamentalForm derivative jet x y := by
  exact adapted_snd_eq_normalProjection derivative _

/-- Reconstruct an ambient raw second derivative from a split tangent/normal
quadratic tensor in adapted coordinates. -/
def ambientSecondFromSplit
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    Tangent → Tangent → Ambient :=
  fun x y =>
    (adaptedAmbientCoordinates derivative).symm
      (WithLp.toLp 2
        (tangentEquivRange derivative (jet.tangentialQuadratic x y),
          jet.normalQuadratic x y))

/-- Flat connection model attached to a split second jet. -/
def flatConnectionSecondJet
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond := ambientSecondFromSplit derivative jet
  ambientConnection := 0
  sourceConnection := 0

/-- In the flat adapted model, the reduced normal quadratic tensor is exactly
the pointwise second fundamental form. This is the precise bridge from the
previous `(B,F)` quotient tensor `B` to geometric extrinsic curvature at the
base point. -/
theorem flat_secondFundamentalForm_eq_normalQuadratic
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SplitImmersionSecondJet Tangent (NormalSpace derivative)) :
    secondFundamentalForm derivative
        (flatConnectionSecondJet derivative jet) =
      jet.normalQuadratic := by
  funext x y
  rw [← adapted_snd_covariantSecondDerivative_eq_secondFundamentalForm]
  simp [covariantSecondDerivative, flatConnectionSecondJet,
    ambientSecondFromSplit]

/-- Exact status boundary for the S4 bridge. -/
structure SecondFundamentalJetStatus where
  pointwiseConnectionCorrectedJetDefined : Prop
  normalProjectionDefined : Prop
  sourceCoordinateInvarianceProved : Prop
  ambientCoordinateInvarianceProved : Prop
  torsionFreeSymmetryProved : Prop
  adaptedNormalComponentFormulaProved : Prop
  flatReducedTensorIdentifiedWithSecondFundamentalForm : Prop
  manifoldLeviCivitaConnectionsConstructed : Prop
  smoothAdaptedFrameGermConstructed : Prop
  frameJetTransformationLawProved : Prop
  spinCFrameLiftConstructed : Prop

/-- Closure of the full manifold-level S4 stage. -/
def secondFundamentalJetClosed
    (s : SecondFundamentalJetStatus) : Prop :=
  s.pointwiseConnectionCorrectedJetDefined /\
  s.normalProjectionDefined /\
  s.sourceCoordinateInvarianceProved /\
  s.ambientCoordinateInvarianceProved /\
  s.torsionFreeSymmetryProved /\
  s.adaptedNormalComponentFormulaProved /\
  s.flatReducedTensorIdentifiedWithSecondFundamentalForm /\
  s.manifoldLeviCivitaConnectionsConstructed /\
  s.smoothAdaptedFrameGermConstructed /\
  s.frameJetTransformationLawProved /\
  s.spinCFrameLiftConstructed

/-- The pointwise jet theorem does not by itself construct the manifold
Levi-Civita connections used to instantiate the coefficients geometrically. -/
theorem missing_manifold_connections_blocks_full_S4
    (s : SecondFundamentalJetStatus)
    (hMissing : Not s.manifoldLeviCivitaConnectionsConstructed) :
    Not (secondFundamentalJetClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusSecondFundamentalFormJet
end JanusFormal
