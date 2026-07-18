import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinCechTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalFrameNoGo4D

/-!
# Nonorientability no-go for ambient Spin and SpinC descent

The ambient space is the mapping torus of the reflection of `S^3`.  One turn
therefore reverses the determinant line of the four-dimensional tangent
bundle.  A global orientation lifts to a continuous nowhere-zero determinant
on the cover, but that lift is anti-periodic.  The existing intermediate-value
argument proves that such a determinant cannot exist.

This gate keeps two logically different levels separate:

* the existing algebraic Spin Cech types make pointwise choices and impose no
  continuity on orthonormal frames or lifts;
* an honest global Spin or SpinC realization must additionally trivialize the
  determinant orientation line continuously.

The second level is empty.  An orientation-reversing overlap also obstructs
the first level immediately.  No Pin no-go is asserted: Pin is precisely the
appropriate structure group when orientation-reversing transitions are kept.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinCNonorientabilityNoGo4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection
open P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
open P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier
open P0EFTJanusMappingTorusAmbientSpinCechTrivialization4D
open P0EFTJanusMappingTorusLocalFrameNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- Determinant-line form of a global ambient tangent orientation.  Its lift
to the mapping-torus cover is continuous, nowhere zero and anti-periodic. -/
abbrev AmbientTangentDeterminantOrientationDescent :=
  AntiPeriodicFrameDeterminant period

/-- The real ambient tangent mapping torus is nonorientable in the exact
determinant-line descent model. -/
theorem ambientTangentDeterminantOrientationDescent_isEmpty :
    IsEmpty (AmbientTangentDeterminantOrientationDescent period) :=
  no_antiPeriodicFrameDeterminant period

/-- There is no continuous nowhere-zero orientation determinant on the
ambient quotient. -/
theorem ambientTangentDeterminantOrientationDescent_not_nonempty :
    ¬ Nonempty (AmbientTangentDeterminantOrientationDescent period) := by
  rintro ⟨orientation⟩
  exact (ambientTangentDeterminantOrientationDescent_isEmpty period).false
    orientation

/-- Concrete obstruction witness: one genuine reduced atlas overlap has
determinant different from `+1`. -/
structure AmbientOrientationReversingOverlapWitness
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  first : AmbientCover period hPeriod
  second : AmbientCover period hPeriod
  coordinate : CoverModel
  coordinate_mem :
    coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source
  determinant_ne_one :
    LinearEquiv.det
        (reduction.orthogonalTransition period hPeriod first second
          coordinate coordinate_mem).toLinearEquiv ≠ (1 : Realˣ)

/-- A reversing overlap has no pointwise Spin lift. -/
theorem AmbientOrientationReversingOverlapWitness.noOverlapLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (witness : AmbientOrientationReversingOverlapWitness
      period hPeriod reduction) :
    ¬ Nonempty (AmbientSpinOverlapLift period hPeriod reduction
      witness.first witness.second witness.coordinate witness.coordinate_mem) :=
  ambientSpinOverlapLift_not_nonempty_of_det_ne_one period hPeriod reduction
    witness.first witness.second witness.coordinate witness.coordinate_mem
      witness.determinant_ne_one

/-- A reversing overlap rules out even an atlas-wide pointwise Spin choice. -/
theorem AmbientOrientationReversingOverlapWitness.not_oriented
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (witness : AmbientOrientationReversingOverlapWitness
      period hPeriod reduction) :
    ¬ AmbientSpinAtlasOriented period hPeriod reduction := by
  intro hOriented
  exact witness.determinant_ne_one
    (hOriented witness.first witness.second witness.coordinate
      witness.coordinate_mem)

/-- A reversing overlap rules out every atlas-wide pointwise Spin lift
choice. -/
theorem AmbientOrientationReversingOverlapWitness.noAtlasLiftChoice
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (witness : AmbientOrientationReversingOverlapWitness
      period hPeriod reduction) :
    ¬ Nonempty (AmbientSpinAtlasLiftChoice period hPeriod reduction) := by
  rintro ⟨choice⟩
  apply witness.noOverlapLift period hPeriod reduction
  exact ⟨choice.overlapLift period hPeriod reduction witness.first
    witness.second witness.coordinate witness.coordinate_mem⟩

/-- Hence no algebraic Spin Cech transition lift can exist once a reversing
overlap is exhibited. -/
theorem AmbientOrientationReversingOverlapWitness.noCechTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (witness : AmbientOrientationReversingOverlapWitness
      period hPeriod reduction) :
    ¬ Nonempty (AmbientSpinCechTransitionLift period hPeriod reduction) := by
  rintro ⟨lift⟩
  apply witness.noAtlasLiftChoice period hPeriod reduction
  exact ⟨ambientSpinCechTransitionLiftToAtlasLiftChoice
    period hPeriod reduction lift⟩

/-- Kernel-valued Cech correction cannot repair an orientation obstruction. -/
theorem AmbientOrientationReversingOverlapWitness.noKernelTrivialization
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (witness : AmbientOrientationReversingOverlapWitness
      period hPeriod reduction)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction) :
    ¬ Nonempty (AmbientSpinCechKernelTrivialization
      period hPeriod reduction choice) := by
  intro hTrivialization
  apply witness.noCechTransitionLift period hPeriod reduction
  exact (ambientSpinCechKernelTrivialization_nonempty_iff
    period hPeriod reduction choice).1 hTrivialization

/-- Minimal honest global Spin realization: the already-defined algebraic
Cech lift plus the continuous determinant orientation required for descent. -/
structure AmbientContinuousOrientedSpinCechRealization
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  cechLift : AmbientSpinCechTransitionLift period hPeriod reduction
  determinantOrientation : AmbientTangentDeterminantOrientationDescent period

/-- No honest global continuous Spin realization exists on the ambient
mapping torus. -/
theorem ambientContinuousOrientedSpinCechRealization_isEmpty
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) :
    IsEmpty (AmbientContinuousOrientedSpinCechRealization
      period hPeriod reduction) := by
  constructor
  intro realization
  exact (ambientTangentDeterminantOrientationDescent_isEmpty period).false
    realization.determinantOrientation

/-- SpinC-specific continuous Cech realization.  The determinant-one
projection records that the connected SpinC structure group acts through the
orientation-preserving tangent group; the continuous orientation descent is
kept explicit because the current generic Pin/SpinC interface does not derive
it automatically. -/
structure AmbientContinuousSpinCCechRealization
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (LiftGroup : Type*) [Group LiftGroup] [TopologicalSpace LiftGroup]
    [IsTopologicalGroup LiftGroup]
    (projection : LiftGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates)) where
  cechLift : AmbientPinSpinCContinuousCechLiftContract
    period hPeriod reduction LiftGroup projection
  projection_det_one : ∀ lift,
    LinearEquiv.det (projection lift) = (1 : Realˣ)
  determinantOrientation : AmbientTangentDeterminantOrientationDescent period

/-- No continuous SpinC Cech realization exists on the nonorientable ambient
mapping torus, independently of the chosen SpinC group model. -/
theorem ambientContinuousSpinCCechRealization_isEmpty
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (LiftGroup : Type*) [Group LiftGroup] [TopologicalSpace LiftGroup]
    [IsTopologicalGroup LiftGroup]
    (projection : LiftGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates)) :
    IsEmpty (AmbientContinuousSpinCCechRealization period hPeriod reduction
      LiftGroup projection) := by
  constructor
  intro realization
  exact (ambientTangentDeterminantOrientationDescent_isEmpty period).false
    realization.determinantOrientation

/-- Algebraic Cech coherence alone is deliberately not declared empty: it
omits precisely the continuity/orientation datum obstructed above. -/
def AmbientAlgebraicSpinCechRemainsConditional
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) : Prop :=
  Nonempty (AmbientSpinCechTransitionLift period hPeriod reduction)

end

end P0EFTJanusMappingTorusAmbientSpinCNonorientabilityNoGo4D
end JanusFormal
