import Mathlib.LinearAlgebra.SpecialLinearGroup
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedFrameOverlapCocycle

namespace JanusFormal
namespace P0EFTJanusDeterminantOrientedReduction

set_option autoImplicit false

noncomputable section

open P0EFTJanusAdaptedFrameOverlapCocycle

universe u v

variable {V : Type u}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Determinant character of the orthogonal group of a finite-dimensional real
inner-product space. The codomain is `ℝˣ`, so invertibility is recorded in the
type and multiplicativity is exact. -/
def orthogonalDeterminant : (V ≃ₗᵢ[ℝ] V) →* ℝˣ where
  toFun frame := frame.toLinearEquiv.det
  map_one' := by
    simp [LinearIsometryEquiv.one_def]
  map_mul' first second := by
    simp [LinearIsometryEquiv.mul_def]

@[simp]
theorem orthogonalDeterminant_apply
    (frame : V ≃ₗᵢ[ℝ] V) :
    orthogonalDeterminant frame = frame.toLinearEquiv.det := by
  rfl

/-- The scalar determinant of an orthogonal transformation is nonzero. This is
already encoded more strongly by the unit-valued determinant character. -/
theorem coe_orthogonalDeterminant_ne_zero
    (frame : V ≃ₗᵢ[ℝ] V) :
    (((orthogonalDeterminant frame : ℝˣ) : ℝ)) ≠ 0 := by
  exact Units.ne_zero _

/-- Concrete orientation-preserving orthogonal subgroup, i.e. the kernel of the
determinant character. -/
def specialOrthogonalSubgroup : Subgroup (V ≃ₗᵢ[ℝ] V) :=
  (orthogonalDeterminant (V := V)).ker

@[simp]
theorem mem_specialOrthogonalSubgroup_iff
    (frame : V ≃ₗᵢ[ℝ] V) :
    frame ∈ specialOrthogonalSubgroup (V := V) ↔
      frame.toLinearEquiv.det = 1 := by
  rfl

/-- Bundled orientation-preserving orthogonal group. -/
abbrev SpecialOrthogonalGroup :=
  specialOrthogonalSubgroup (V := V)

section TangentNormal

variable {TangentModel : Type u}
variable {NormalModel : Type v}
variable [NormedAddCommGroup TangentModel]
variable [InnerProductSpace ℝ TangentModel]
variable [FiniteDimensional ℝ TangentModel]
variable [NormedAddCommGroup NormalModel]
variable [InnerProductSpace ℝ NormalModel]
variable [FiniteDimensional ℝ NormalModel]

/-- Tangent and normal orientation characters instantiated by determinant. -/
def determinantOrientationCharacters :
    ResidualOrientationCharacters
      (TangentModel := TangentModel)
      (NormalModel := NormalModel)
      (Sign := ℝˣ) where
  tangentCharacter := orthogonalDeterminant
  normalCharacter := orthogonalDeterminant

/-- Concrete `SO(T) × SO(N)` subgroup inside the residual
`O(T) × O(N)` symmetry group. -/
def orientedResidualSubgroup : Subgroup
    ((TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
      (NormalModel ≃ₗᵢ[ℝ] NormalModel)) where
  carrier transition :=
    transition.1 ∈ specialOrthogonalSubgroup (V := TangentModel) ∧
      transition.2 ∈ specialOrthogonalSubgroup (V := NormalModel)
  one_mem' := by
    constructor <;> simp [specialOrthogonalSubgroup]
  mul_mem' := by
    intro first second hFirst hSecond
    exact ⟨Subgroup.mul_mem _ hFirst.1 hSecond.1,
      Subgroup.mul_mem _ hFirst.2 hSecond.2⟩
  inv_mem' := by
    intro transition hTransition
    exact ⟨Subgroup.inv_mem _ hTransition.1,
      Subgroup.inv_mem _ hTransition.2⟩

@[simp]
theorem mem_orientedResidualSubgroup_iff
    (transition :
      (TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
        (NormalModel ≃ₗᵢ[ℝ] NormalModel)) :
    transition ∈ orientedResidualSubgroup
      (TangentModel := TangentModel) (NormalModel := NormalModel) ↔
      transition.1.toLinearEquiv.det = 1 ∧
        transition.2.toLinearEquiv.det = 1 := by
  rfl

/-- The generic orientation predicate from the preceding gate is exactly
membership in the determinant-one residual subgroup. -/
theorem orientationPredicate_iff_mem_orientedResidualSubgroup
    (transition :
      (TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
        (NormalModel ≃ₗᵢ[ℝ] NormalModel)) :
    IsOrientationPreserving determinantOrientationCharacters transition ↔
      transition ∈ orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel) := by
  rfl

/-- Determinant-one overlap transitions are closed under the adapted-frame Čech
cocycle. -/
theorem determinantOrientedTransition_cocycle
    (first second third : AdaptedFrameChoice TangentModel NormalModel)
    (hFirstSecond : adaptedTransition first second ∈
      orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel))
    (hSecondThird : adaptedTransition second third ∈
      orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel)) :
    adaptedTransition first third ∈
      orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel) := by
  rw [← adaptedTransition_mul first second third]
  exact Subgroup.mul_mem _ hSecondThird hFirstSecond

/-- Reversing a determinant-one overlap transition remains determinant one. -/
theorem determinantOrientedTransition_reverse
    (first second : AdaptedFrameChoice TangentModel NormalModel)
    (hTransition : adaptedTransition first second ∈
      orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel)) :
    adaptedTransition second first ∈
      orientedResidualSubgroup
        (TangentModel := TangentModel) (NormalModel := NormalModel) := by
  rw [adaptedTransition_reverse]
  exact Subgroup.inv_mem _ hTransition

/-- The oriented residual group is the product of the tangent and normal
special-orthogonal groups at the level of carrier conditions. -/
theorem orientedResidualSubgroup_carrier
    (transition :
      (TangentModel ≃ₗᵢ[ℝ] TangentModel) ×
        (NormalModel ≃ₗᵢ[ℝ] NormalModel)) :
    transition ∈ orientedResidualSubgroup
      (TangentModel := TangentModel) (NormalModel := NormalModel) ↔
      transition.1 ∈ specialOrthogonalSubgroup (V := TangentModel) ∧
        transition.2 ∈ specialOrthogonalSubgroup (V := NormalModel) := by
  rfl

end TangentNormal

/-- Boundary after determinant instantiation. -/
structure DeterminantOrientedReductionStatus where
  orthogonalDeterminantCharacterConstructed : Prop
  determinantUnitTyped : Prop
  tangentSpecialOrthogonalSubgroupConstructed : Prop
  normalSpecialOrthogonalSubgroupConstructed : Prop
  residualProductSubgroupConstructed : Prop
  determinantOrientedCocycleProved : Prop
  smoothTransitionMapsInserted : Prop
  orientationCompatibilityOfGeometricFramesProved : Prop
  orientedPrincipalBundleConstructed : Prop
  spinDoubleCoverInserted : Prop
  spinCDeterminantFiberProductConstructed : Prop
  spinCCocycleLiftProved : Prop

/-- Closure of the determinant/oriented/SpinC reduction stage. -/
def determinantOrientedReductionClosed
    (s : DeterminantOrientedReductionStatus) : Prop :=
  s.orthogonalDeterminantCharacterConstructed /\
  s.determinantUnitTyped /\
  s.tangentSpecialOrthogonalSubgroupConstructed /\
  s.normalSpecialOrthogonalSubgroupConstructed /\
  s.residualProductSubgroupConstructed /\
  s.determinantOrientedCocycleProved /\
  s.smoothTransitionMapsInserted /\
  s.orientationCompatibilityOfGeometricFramesProved /\
  s.orientedPrincipalBundleConstructed /\
  s.spinDoubleCoverInserted /\
  s.spinCDeterminantFiberProductConstructed /\
  s.spinCCocycleLiftProved

/-- The determinant-one subgroup theorem does not itself construct the spin
double cover or a SpinC lift. -/
theorem missing_spin_double_cover_blocks_spinC_reduction
    (s : DeterminantOrientedReductionStatus)
    (hMissing : Not s.spinDoubleCoverInserted) :
    Not (determinantOrientedReductionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusDeterminantOrientedReduction
end JanusFormal
