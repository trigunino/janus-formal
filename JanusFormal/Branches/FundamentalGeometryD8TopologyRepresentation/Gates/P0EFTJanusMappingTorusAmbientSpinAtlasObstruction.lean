import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinProjection

/-!
# Atlas-specific obstruction to an ambient Spin lift

This gate proves the strict cocycle law for the actual tangent transitions.
It then isolates the two genuinely remaining Spin inputs: existence of lifts
of the oriented orthogonal transitions, and triviality of their kernel-valued
Čech defect.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinAtlasObstruction

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- Coordinate changes built from three quotient charts compose pointwise on
their common domain. -/
theorem ambientAtlasTransition_cocycle_apply
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (_hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source) :
    ambientAtlasTransition period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate) =
      ambientAtlasTransition period hPeriod first third coordinate := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hFirstSecond
  rw [OpenPartialHomeomorph.trans_source] at hFirstSecond
  change
    (ambientQuotientLocalChart period hPeriod third)
        ((ambientQuotientLocalChart period hPeriod second).symm
          ((ambientQuotientLocalChart period hPeriod second)
            ((ambientQuotientLocalChart period hPeriod first).symm coordinate))) =
      (ambientQuotientLocalChart period hPeriod third)
        ((ambientQuotientLocalChart period hPeriod first).symm coordinate)
  rw [(ambientQuotientLocalChart period hPeriod second).left_inv hFirstSecond.2]

/-- The derivatives of the actual atlas transitions satisfy the strict
triple-overlap cocycle law. -/
theorem ambientAtlasTangentTransition_cocycle
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source) :
    (ambientAtlasTangentTransition period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird).toLinearEquiv *
      (ambientAtlasTangentTransition period hPeriod first second
        coordinate hFirstSecond).toLinearEquiv =
      (ambientAtlasTangentTransition period hPeriod first third
        coordinate hFirstThird).toLinearEquiv := by
  apply LinearEquiv.ext
  intro tangent
  change
    mfderiv coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod second third)
        (ambientAtlasTransition period hPeriod first second coordinate)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (ambientAtlasTransition period hPeriod first second) coordinate tangent) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first third) coordinate tangent
  let firstSecond := ambientAtlasPartialDiffeomorph period hPeriod first second
  let secondThird := ambientAtlasPartialDiffeomorph period hPeriod second third
  have hDifferentiableFirstSecond :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second) coordinate :=
    (firstSecond.isLocalDiffeomorphAt
      (I := coverModelWithCorners) (J := coverModelWithCorners) (n := ω)
      hFirstSecond).mdifferentiableAt (by simp)
  have hDifferentiableSecondThird :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod second third)
        (ambientAtlasTransition period hPeriod first second coordinate) :=
    (secondThird.isLocalDiffeomorphAt
      (I := coverModelWithCorners) (J := coverModelWithCorners) (n := ω)
      hSecondThird).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply coordinate hDifferentiableSecondThird
    hDifferentiableFirstSecond tangent]
  have hEventually :
      (ambientAtlasTransition period hPeriod second third) ∘
          (ambientAtlasTransition period hPeriod first second) =ᶠ[𝓝 coordinate]
        ambientAtlasTransition period hPeriod first third := by
    apply Filter.eventuallyEq_of_mem
      ((ambientAtlasTransition period hPeriod first second).isOpen_inter_preimage
        (ambientAtlasTransition period hPeriod second third).open_source |>.mem_nhds
          ⟨hFirstSecond, hSecondThird⟩)
    intro point hPoint
    exact ambientAtlasTransition_cocycle_apply period hPeriod first second third point
      hPoint.1 hPoint.2
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners) (I' := coverModelWithCorners) hEventually
  exact congrArg (fun derivative => derivative tangent) hDerivative

/-- Conjugating the strict tangent cocycle by any compatible orthonormal
reduction gives a strict `O(4)` cocycle. -/
theorem ambientOrthogonalTransition_cocycle
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source) :
    (reduction.orthogonalTransition period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate)
        hSecondThird).toLinearEquiv *
      (reduction.orthogonalTransition period hPeriod first second
        coordinate hFirstSecond).toLinearEquiv =
      (reduction.orthogonalTransition period hPeriod first third
        coordinate hFirstThird).toLinearEquiv := by
  apply LinearEquiv.ext
  intro tangent
  change
    (reduction.orthonormalFrame third
      (ambientAtlasTransition period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate))).symm
        (reduction.transition second third
          (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird
          (reduction.orthonormalFrame second
            (ambientAtlasTransition period hPeriod first second coordinate)
            ((reduction.orthonormalFrame second
              (ambientAtlasTransition period hPeriod first second coordinate)).symm
              (reduction.transition first second coordinate hFirstSecond
                (reduction.orthonormalFrame first coordinate tangent))))) =
      (reduction.orthonormalFrame third
        (ambientAtlasTransition period hPeriod first third coordinate)).symm
          (reduction.transition first third coordinate hFirstThird
            (reduction.orthonormalFrame first coordinate tangent))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply]
  have hTransitionSecondThird (vector : CoverCoordinates) :
      reduction.transition second third
          (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird vector =
        (ambientAtlasTangentTransition period hPeriod second third
          (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird).toLinearEquiv
            vector :=
    congrArg (fun transition => transition vector)
      (reduction.transition_coe second third
        (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
  have hTransitionFirstSecond (vector : CoverCoordinates) :
      reduction.transition first second coordinate hFirstSecond vector =
        (ambientAtlasTangentTransition period hPeriod first second
          coordinate hFirstSecond).toLinearEquiv vector :=
    congrArg (fun transition => transition vector)
      (reduction.transition_coe first second coordinate hFirstSecond)
  have hTransitionFirstThird (vector : CoverCoordinates) :
      reduction.transition first third coordinate hFirstThird vector =
        (ambientAtlasTangentTransition period hPeriod first third
          coordinate hFirstThird).toLinearEquiv vector :=
    congrArg (fun transition => transition vector)
      (reduction.transition_coe first third coordinate hFirstThird)
  rw [hTransitionSecondThird, hTransitionFirstSecond, hTransitionFirstThird]
  have hPoint := ambientAtlasTransition_cocycle_apply period hPeriod
    first second third coordinate hFirstSecond hSecondThird
  rw [hPoint]
  apply congrArg
    (reduction.orthonormalFrame third
      (ambientAtlasTransition period hPeriod first third coordinate)).symm
  exact congrArg (fun transition =>
      transition (reduction.orthonormalFrame first coordinate tangent))
    (ambientAtlasTangentTransition_cocycle period hPeriod first second third coordinate
      hFirstSecond hSecondThird hFirstThird)

/-- A pointwise Spin lift of one actual reduced atlas transition.  Existence
of this object is precisely the still-missing surjectivity/choice step. -/
structure AmbientSpinOverlapLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) where
  lift : AmbientCoordinateSpinGroup
  projects :
    ambientSpinProjection lift =
      (reduction.orthogonalTransition period hPeriod first second
        coordinate hCoordinate).toLinearEquiv

/-- Liftable overlaps are closed under composition on triple intersections. -/
def AmbientSpinOverlapLift.comp
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (firstSecond : AmbientSpinOverlapLift period hPeriod reduction first second
      coordinate hFirstSecond)
    (secondThird : AmbientSpinOverlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird) :
    AmbientSpinOverlapLift period hPeriod reduction first third coordinate hFirstThird where
  lift := secondThird.lift * firstSecond.lift
  projects := by
    rw [map_mul, secondThird.projects, firstSecond.projects]
    exact ambientOrthogonalTransition_cocycle period hPeriod reduction
      first second third coordinate hFirstSecond hSecondThird hFirstThird

/-- The Čech defect of three chosen pointwise Spin lifts. -/
def ambientSpinCechDefect
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (firstSecond : AmbientSpinOverlapLift period hPeriod reduction first second
      coordinate hFirstSecond)
    (secondThird : AmbientSpinOverlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
    (firstThird : AmbientSpinOverlapLift period hPeriod reduction first third
      coordinate hFirstThird) : AmbientCoordinateSpinGroup :=
  secondThird.lift * firstSecond.lift * firstThird.lift⁻¹

/-- The defect always lies in the kernel of the genuine Spin projection. -/
theorem ambientSpinProjection_cechDefect
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (firstSecond : AmbientSpinOverlapLift period hPeriod reduction first second
      coordinate hFirstSecond)
    (secondThird : AmbientSpinOverlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
    (firstThird : AmbientSpinOverlapLift period hPeriod reduction first third
      coordinate hFirstThird) :
    ambientSpinProjection
        (ambientSpinCechDefect period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird) = 1 := by
  rw [ambientSpinCechDefect, map_mul, map_mul, map_inv,
    secondThird.projects, firstSecond.projects, firstThird.projects,
    ambientOrthogonalTransition_cocycle period hPeriod reduction first second third
      coordinate hFirstSecond hSecondThird hFirstThird]
  exact mul_inv_cancel _

/-- Kernel-valued form of the exact Čech obstruction. -/
def ambientSpinCechKernelDefect
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (firstSecond : AmbientSpinOverlapLift period hPeriod reduction first second
      coordinate hFirstSecond)
    (secondThird : AmbientSpinOverlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
    (firstThird : AmbientSpinOverlapLift period hPeriod reduction first third
      coordinate hFirstThird) : MonoidHom.ker ambientSpinProjection :=
  ⟨ambientSpinCechDefect period hPeriod reduction first second third coordinate
      hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird,
    ambientSpinProjection_cechDefect period hPeriod reduction first second third coordinate
      hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird⟩

/-- Exact closure criterion: the chosen lifts form a Spin cocycle if and only
if their kernel-valued defect is trivial. -/
theorem ambientSpinCechDefect_eq_one_iff
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (firstSecond : AmbientSpinOverlapLift period hPeriod reduction first second
      coordinate hFirstSecond)
    (secondThird : AmbientSpinOverlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
    (firstThird : AmbientSpinOverlapLift period hPeriod reduction first third
      coordinate hFirstThird) :
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird = 1 ↔
      secondThird.lift * firstSecond.lift = firstThird.lift := by
  exact mul_inv_eq_one

end

end P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
end JanusFormal
