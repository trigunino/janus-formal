import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMovingNormalTransport

namespace JanusFormal
namespace P0EFTJanusAdaptedFrameOverlapCocycle

set_option autoImplicit false

noncomputable section

universe u v w

variable {TangentModel : Type u}
variable {NormalModel : Type v}
variable [NormedAddCommGroup TangentModel]
variable [InnerProductSpace ℝ TangentModel]
variable [NormedAddCommGroup NormalModel]
variable [InnerProductSpace ℝ NormalModel]

/-- A local adapted orthogonal frame choice after tangent/normal splitting. The
fields record the tangent and normal orthogonal gauges relative to fixed local
models. The geometric construction of these gauges from manifold bundle
trivializations is kept as a separate obligation. -/
@[ext]
structure AdaptedFrameChoice
    (TangentModel : Type u) (NormalModel : Type v)
    [NormedAddCommGroup TangentModel]
    [InnerProductSpace ℝ TangentModel]
    [NormedAddCommGroup NormalModel]
    [InnerProductSpace ℝ NormalModel] where
  tangentGauge : TangentModel ≃ₗᵢ[ℝ] TangentModel
  normalGauge : NormalModel ≃ₗᵢ[ℝ] NormalModel

/-- Residual tangent/normal transition between two local adapted frame choices. -/
def adaptedTransition
    (first second : AdaptedFrameChoice TangentModel NormalModel) :
    (TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
      (NormalModel ≃ₗᵢ[ℝ] NormalModel) :=
  (first.tangentGauge.symm.trans second.tangentGauge,
    first.normalGauge.symm.trans second.normalGauge)

/-- A frame has the identity transition to itself. -/
@[simp]
theorem adaptedTransition_self
    (frame : AdaptedFrameChoice TangentModel NormalModel) :
    adaptedTransition frame frame = 1 := by
  apply Prod.ext <;>
    simp [adaptedTransition, LinearIsometryEquiv.one_def]

/-- Reversing an overlap inverts both tangent and normal transitions. -/
@[simp]
theorem adaptedTransition_reverse
    (first second : AdaptedFrameChoice TangentModel NormalModel) :
    adaptedTransition second first =
      ((adaptedTransition first second).1.symm,
        (adaptedTransition first second).2.symm) := by
  apply Prod.ext <;>
    simp [adaptedTransition]

/-- Čech cocycle law for three adapted frame choices. The transition from the
first frame to the third is the composition through the second frame. -/
theorem adaptedTransition_cocycle
    (first second third : AdaptedFrameChoice TangentModel NormalModel) :
    ((adaptedTransition first second).1.trans
        (adaptedTransition second third).1,
      (adaptedTransition first second).2.trans
        (adaptedTransition second third).2) =
      adaptedTransition first third := by
  apply Prod.ext
  · simp only [adaptedTransition]
    calc
      (first.tangentGauge.symm.trans second.tangentGauge).trans
          (second.tangentGauge.symm.trans third.tangentGauge) =
        first.tangentGauge.symm.trans
          (second.tangentGauge.trans
            (second.tangentGauge.symm.trans third.tangentGauge)) :=
        (LinearIsometryEquiv.trans_assoc _ _ _).symm
      _ = first.tangentGauge.symm.trans third.tangentGauge := by
        simp [LinearIsometryEquiv.trans_assoc]
  · simp only [adaptedTransition]
    calc
      (first.normalGauge.symm.trans second.normalGauge).trans
          (second.normalGauge.symm.trans third.normalGauge) =
        first.normalGauge.symm.trans
          (second.normalGauge.trans
            (second.normalGauge.symm.trans third.normalGauge)) :=
        (LinearIsometryEquiv.trans_assoc _ _ _).symm
      _ = first.normalGauge.symm.trans third.normalGauge := by
        simp [LinearIsometryEquiv.trans_assoc]

/-- The cocycle law in the product-group multiplication convention used by Lean.
Because multiplication of linear isometry equivalences is function composition,
`g₂₃ * g₁₂` is the transition `g₁₃`. -/
theorem adaptedTransition_mul
    (first second third : AdaptedFrameChoice TangentModel NormalModel) :
    adaptedTransition second third * adaptedTransition first second =
      adaptedTransition first third := by
  apply Prod.ext
  · rw [Prod.fst_mul, LinearIsometryEquiv.mul_def]
    exact congrArg Prod.fst
      (adaptedTransition_cocycle first second third)
  · rw [Prod.snd_mul, LinearIsometryEquiv.mul_def]
    exact congrArg Prod.snd
      (adaptedTransition_cocycle first second third)

section OrientationCharacters

variable {Sign : Type w}
variable [Group Sign]

/-- Abstract orientation characters of the tangent and normal orthogonal groups.
The intended finite-dimensional real instantiation is determinant sign. Keeping
this as a character interface separates the cocycle theorem from the later
choice of determinant/orientation API. -/
structure ResidualOrientationCharacters where
  tangentCharacter :
    (TangentModel ≃ₗᵢ[ℝ] TangentModel) →* Sign
  normalCharacter :
    (NormalModel ≃ₗᵢ[ℝ] NormalModel) →* Sign

/-- A residual transition preserves both chosen orientations. -/
def IsOrientationPreserving
    (characters : ResidualOrientationCharacters
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      (Sign := Sign))
    (transition :
      (TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
        (NormalModel ≃ₗᵢ[ℝ] NormalModel)) : Prop :=
  characters.tangentCharacter transition.1 = 1 ∧
    characters.normalCharacter transition.2 = 1

/-- Identity overlap transitions preserve orientation. -/
theorem orientationPreserving_self
    (characters : ResidualOrientationCharacters
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      (Sign := Sign))
    (frame : AdaptedFrameChoice TangentModel NormalModel) :
    IsOrientationPreserving characters (adaptedTransition frame frame) := by
  rw [adaptedTransition_self]
  exact ⟨characters.tangentCharacter.map_one,
    characters.normalCharacter.map_one⟩

/-- Orientation-preserving overlap transitions are closed under the Čech cocycle
composition. -/
theorem orientationPreserving_cocycle
    (characters : ResidualOrientationCharacters
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      (Sign := Sign))
    (first second third : AdaptedFrameChoice TangentModel NormalModel)
    (hFirstSecond : IsOrientationPreserving characters
      (adaptedTransition first second))
    (hSecondThird : IsOrientationPreserving characters
      (adaptedTransition second third)) :
    IsOrientationPreserving characters
      (adaptedTransition first third) := by
  rw [← adaptedTransition_mul first second third]
  constructor
  · rw [map_mul, hSecondThird.1, hFirstSecond.1, mul_one]
  · rw [map_mul, hSecondThird.2, hFirstSecond.2, mul_one]

/-- Reversing an orientation-preserving transition remains
orientation-preserving. -/
theorem orientationPreserving_reverse
    (characters : ResidualOrientationCharacters
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      (Sign := Sign))
    (first second : AdaptedFrameChoice TangentModel NormalModel)
    (hTransition : IsOrientationPreserving characters
      (adaptedTransition first second)) :
    IsOrientationPreserving characters
      (adaptedTransition second first) := by
  rw [adaptedTransition_reverse]
  constructor
  · rw [map_inv, hTransition.1, inv_one]
  · rw [map_inv, hTransition.2, inv_one]

end OrientationCharacters

/-- Exact boundary after the overlap-cocycle theorem. -/
structure AdaptedFrameOverlapStatus where
  localAdaptedFrameChoicesConstructed : Prop
  residualTransitionsDefined : Prop
  identityLawProved : Prop
  inverseLawProved : Prop
  cechCocycleLawProved : Prop
  orientationCharactersSpecified : Prop
  orientationPreservingSubcocycleProved : Prop
  transitionsExtractedFromSmoothBundleFrames : Prop
  overlapSmoothnessProved : Prop
  determinantCharactersInstantiated : Prop
  orientedFrameBundleReductionConstructed : Prop
  spinCTransitionLiftsConstructed : Prop

/-- Closure of the oriented/SpinC overlap stage. -/
def adaptedFrameOverlapClosed
    (s : AdaptedFrameOverlapStatus) : Prop :=
  s.localAdaptedFrameChoicesConstructed /\
  s.residualTransitionsDefined /\
  s.identityLawProved /\
  s.inverseLawProved /\
  s.cechCocycleLawProved /\
  s.orientationCharactersSpecified /\
  s.orientationPreservingSubcocycleProved /\
  s.transitionsExtractedFromSmoothBundleFrames /\
  s.overlapSmoothnessProved /\
  s.determinantCharactersInstantiated /\
  s.orientedFrameBundleReductionConstructed /\
  s.spinCTransitionLiftsConstructed

/-- The algebraic cocycle does not itself instantiate determinant signs or build
an oriented frame bundle. -/
theorem missing_determinant_character_blocks_oriented_reduction
    (s : AdaptedFrameOverlapStatus)
    (hMissing : Not s.determinantCharactersInstantiated) :
    Not (adaptedFrameOverlapClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusAdaptedFrameOverlapCocycle
end JanusFormal
