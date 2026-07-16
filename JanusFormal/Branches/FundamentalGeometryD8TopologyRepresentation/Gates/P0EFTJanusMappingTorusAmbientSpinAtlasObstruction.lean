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

/-- Two Spin lifts of the same actual atlas transition differ by an element
of the kernel of the Spin projection. -/
def ambientSpinOverlapLiftDifference
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (firstLift secondLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    MonoidHom.ker ambientSpinProjection :=
  ⟨firstLift.lift * secondLift.lift⁻¹, by
    change ambientSpinProjection (firstLift.lift * secondLift.lift⁻¹) = 1
    rw [map_mul, map_inv, firstLift.projects, secondLift.projects]
    exact mul_inv_cancel _⟩

/-- The kernel-valued difference is trivial exactly when the two chosen Spin
lifts are equal as group elements. -/
theorem ambientSpinOverlapLiftDifference_eq_one_iff
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (firstLift secondLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    (ambientSpinOverlapLiftDifference period hPeriod reduction first second
      coordinate hCoordinate firstLift secondLift : AmbientCoordinateSpinGroup) = 1 ↔
      firstLift.lift = secondLift.lift := by
  exact mul_inv_eq_one

/-- The kernel of the Spin projection acts on the set of lifts of one fixed
atlas transition by left multiplication. -/
def AmbientSpinOverlapLift.kernelTranslate
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (kernel : MonoidHom.ker ambientSpinProjection)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate where
  lift := kernel.1 * overlapLift.lift
  projects := by
    rw [map_mul, kernel.2, overlapLift.projects, one_mul]

/-- The identity kernel element acts trivially on the underlying Spin lift. -/
theorem AmbientSpinOverlapLift.kernelTranslate_one
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    (overlapLift.kernelTranslate period hPeriod reduction first second coordinate
      hCoordinate 1).lift = overlapLift.lift := by
  simp [AmbientSpinOverlapLift.kernelTranslate]

/-- Successive kernel translations compose by multiplication. -/
theorem AmbientSpinOverlapLift.kernelTranslate_mul
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (firstKernel secondKernel : MonoidHom.ker ambientSpinProjection)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    ((overlapLift.kernelTranslate period hPeriod reduction first second coordinate
        hCoordinate secondKernel).kernelTranslate period hPeriod reduction
          first second coordinate hCoordinate firstKernel).lift =
      (overlapLift.kernelTranslate period hPeriod reduction first second coordinate
        hCoordinate (firstKernel * secondKernel)).lift := by
  simp [AmbientSpinOverlapLift.kernelTranslate, mul_assoc]

/-- Translating a lift by a kernel element recovers exactly that element as
the kernel-valued difference from the original lift. -/
theorem ambientSpinOverlapLiftDifference_kernelTranslate
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (kernel : MonoidHom.ker ambientSpinProjection)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    ambientSpinOverlapLiftDifference period hPeriod reduction first second
        coordinate hCoordinate
        (overlapLift.kernelTranslate period hPeriod reduction first second
          coordinate hCoordinate kernel) overlapLift = kernel := by
  apply Subtype.ext
  simp [ambientSpinOverlapLiftDifference,
    AmbientSpinOverlapLift.kernelTranslate]

/-- The kernel action is faithful at every chosen lift. -/
theorem AmbientSpinOverlapLift.kernelTranslate_injective
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    Function.Injective (fun kernel : MonoidHom.ker ambientSpinProjection =>
      (overlapLift.kernelTranslate period hPeriod reduction first second
        coordinate hCoordinate kernel).lift) := by
  intro firstKernel secondKernel hEqual
  apply Subtype.ext
  have h := congrArg (fun value => value * overlapLift.lift⁻¹) hEqual
  simpa [AmbientSpinOverlapLift.kernelTranslate, mul_assoc] using h

/-- Conjugation by any ambient Spin element preserves the projection kernel. -/
def ambientSpinKernelConjugate
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    MonoidHom.ker ambientSpinProjection :=
  ⟨spin * kernel.1 * spin⁻¹, by
    change ambientSpinProjection (spin * kernel.1 * spin⁻¹) = 1
    rw [map_mul, map_mul, map_inv, kernel.2]
    simp⟩

/-- Conjugation by a Spin element is a genuine automorphism of the projection
kernel, with inverse given by conjugation by the inverse Spin element. -/
def ambientSpinKernelConjugationEquiv
    (spin : AmbientCoordinateSpinGroup) :
    MonoidHom.ker ambientSpinProjection ≃* MonoidHom.ker ambientSpinProjection where
  toFun := ambientSpinKernelConjugate spin
  invFun := ambientSpinKernelConjugate spin⁻¹
  left_inv kernel := by
    apply Subtype.ext
    simp [ambientSpinKernelConjugate, mul_assoc]
  right_inv kernel := by
    apply Subtype.ext
    simp [ambientSpinKernelConjugate, mul_assoc]
  map_mul' firstKernel secondKernel := by
    apply Subtype.ext
    simp [ambientSpinKernelConjugate, mul_assoc]

@[simp]
theorem ambientSpinKernelConjugationEquiv_apply
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinKernelConjugationEquiv spin kernel =
      ambientSpinKernelConjugate spin kernel :=
  rfl

/-- The pointwise conjugation automorphisms assemble into the adjoint
representation of the ambient Spin group on the projection kernel. -/
def ambientSpinKernelConjugationRepresentation :
    AmbientCoordinateSpinGroup →*
      MulAut (MonoidHom.ker ambientSpinProjection) where
  toFun := ambientSpinKernelConjugationEquiv
  map_one' := by
    ext kernel
    simp [ambientSpinKernelConjugationEquiv, ambientSpinKernelConjugate]
  map_mul' firstSpin secondSpin := by
    ext kernel
    simp [ambientSpinKernelConjugationEquiv, ambientSpinKernelConjugate,
      mul_assoc]

@[simp]
theorem ambientSpinKernelConjugationRepresentation_apply
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinKernelConjugationRepresentation spin kernel =
      ambientSpinKernelConjugate spin kernel :=
  rfl

/-- Pointwise fixedness under conjugation is exactly commutation with the
chosen ambient Spin element. -/
theorem ambientSpinKernelConjugate_eq_iff_commute
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinKernelConjugate spin kernel = kernel ↔
      Commute spin kernel.1 := by
  constructor
  · intro hFixed
    have hValue := congrArg Subtype.val hFixed
    apply mul_right_cancel (b := spin⁻¹)
    simpa [ambientSpinKernelConjugate, mul_assoc] using hValue
  · intro hCommute
    apply Subtype.ext
    change spin * kernel.1 * spin⁻¹ = kernel.1
    rw [hCommute.eq]
    simp [mul_assoc]

/-- Exact centrality criterion: the conjugation automorphism associated with
`spin` is trivial precisely when `spin` commutes with every kernel element. -/
theorem ambientSpinKernelConjugationEquiv_eq_one_iff
    (spin : AmbientCoordinateSpinGroup) :
    ambientSpinKernelConjugationEquiv spin = 1 ↔
      ∀ kernel : MonoidHom.ker ambientSpinProjection,
        Commute spin kernel.1 := by
  constructor
  · intro hTrivial kernel
    apply (ambientSpinKernelConjugate_eq_iff_commute spin kernel).1
    change ambientSpinKernelConjugationEquiv spin kernel = kernel
    rw [hTrivial]
    rfl
  · intro hCentral
    ext kernel
    simpa [ambientSpinKernelConjugationEquiv] using congrArg Subtype.val
      ((ambientSpinKernelConjugate_eq_iff_commute spin kernel).2 (hCentral kernel))

/-- The full conjugation representation is trivial exactly when every ambient
Spin element commutes with every element of the projection kernel. -/
theorem ambientSpinKernelConjugationRepresentation_eq_one_iff :
    ambientSpinKernelConjugationRepresentation = 1 ↔
      ∀ (spin : AmbientCoordinateSpinGroup)
        (kernel : MonoidHom.ker ambientSpinProjection),
        Commute spin kernel.1 := by
  constructor
  · intro hTrivial spin
    apply (ambientSpinKernelConjugationEquiv_eq_one_iff spin).1
    change ambientSpinKernelConjugationRepresentation spin = 1
    rw [hTrivial]
    rfl
  · intro hCentral
    ext spin kernel
    simpa [ambientSpinKernelConjugationRepresentation,
      ambientSpinKernelConjugationEquiv] using congrArg Subtype.val
      ((ambientSpinKernelConjugate_eq_iff_commute spin kernel).2
        (hCentral spin kernel))

/-- A common change of local Spin lift conjugates, rather than changes
arbitrarily, the kernel-valued difference of two lifts. -/
theorem ambientSpinOverlapLiftDifference_common_kernelTranslate
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (kernel : MonoidHom.ker ambientSpinProjection)
    (firstLift secondLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    ambientSpinOverlapLiftDifference period hPeriod reduction first second
        coordinate hCoordinate
        (firstLift.kernelTranslate period hPeriod reduction first second
          coordinate hCoordinate kernel)
        (secondLift.kernelTranslate period hPeriod reduction first second
          coordinate hCoordinate kernel) =
      ambientSpinKernelConjugate kernel.1
        (ambientSpinOverlapLiftDifference period hPeriod reduction first second
          coordinate hCoordinate firstLift secondLift) := by
  apply Subtype.ext
  simp [ambientSpinOverlapLiftDifference,
    AmbientSpinOverlapLift.kernelTranslate, ambientSpinKernelConjugate,
    mul_assoc]

/-- Conversely, the difference of two lifts translates the second lift back
to the first one.  Thus the local lift ambiguity is a torsor under the kernel. -/
theorem ambientSpinOverlapLiftDifference_transitive
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (firstLift secondLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    (secondLift.kernelTranslate period hPeriod reduction first second coordinate
      hCoordinate (ambientSpinOverlapLiftDifference period hPeriod reduction
        first second coordinate hCoordinate firstLift secondLift)).lift =
      firstLift.lift := by
  simp [ambientSpinOverlapLiftDifference,
    AmbientSpinOverlapLift.kernelTranslate]

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

/-- Changing the chosen lift on the composite overlap by a kernel translation
changes the Cech defect by the inverse kernel element on the right.  This is
the exact local coboundary law for the third edge of a triple overlap. -/
theorem ambientSpinCechDefect_third_kernelTranslate
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
      coordinate hFirstThird)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird firstSecond secondThird
        (firstThird.kernelTranslate period hPeriod reduction first third
          coordinate hFirstThird kernel) =
      ambientSpinCechDefect period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird *
        kernel.1⁻¹ := by
  simp [ambientSpinCechDefect, AmbientSpinOverlapLift.kernelTranslate,
    mul_assoc]

/-- Translating the chosen composite-overlap lift by its own kernel-valued
Cech defect canonically kills that defect on the fixed triple overlap. -/
theorem ambientSpinCechDefect_canonicalThirdCorrection_eq_one
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
        hFirstSecond hSecondThird hFirstThird firstSecond secondThird
        (firstThird.kernelTranslate period hPeriod reduction first third
          coordinate hFirstThird
          (ambientSpinCechKernelDefect period hPeriod reduction first second third
            coordinate hFirstSecond hSecondThird hFirstThird firstSecond
            secondThird firstThird)) = 1 := by
  rw [ambientSpinCechDefect_third_kernelTranslate]
  simp [ambientSpinCechKernelDefect]

/-- A kernel translation of the chosen composite-overlap lift kills the Cech
defect exactly when it is the canonical kernel-valued defect. -/
theorem ambientSpinCechDefect_third_kernelTranslate_eq_one_iff
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
      coordinate hFirstThird)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird firstSecond secondThird
        (firstThird.kernelTranslate period hPeriod reduction first third
          coordinate hFirstThird kernel) = 1 ↔
      kernel = ambientSpinCechKernelDefect period hPeriod reduction first second
        third coordinate hFirstSecond hSecondThird hFirstThird firstSecond
        secondThird firstThird := by
  rw [ambientSpinCechDefect_third_kernelTranslate]
  constructor
  · intro hDefect
    apply Subtype.ext
    exact (mul_inv_eq_one.mp hDefect).symm
  · intro hKernel
    subst kernel
    simp [ambientSpinCechKernelDefect]

/-- Correcting the chosen composite-overlap lift by its canonical Cech defect
recovers exactly the lift obtained by composing the other two overlaps. -/
theorem ambientSpinCechCanonicalThirdCorrection_eq_comp
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
    firstThird.kernelTranslate period hPeriod reduction first third coordinate
        hFirstThird
        (ambientSpinCechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird firstSecond
          secondThird firstThird) =
      firstSecond.comp period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird secondThird := by
  cases firstSecond
  cases secondThird
  cases firstThird
  simp [ambientSpinCechKernelDefect, ambientSpinCechDefect,
    AmbientSpinOverlapLift.kernelTranslate, AmbientSpinOverlapLift.comp,
    mul_assoc]

/-- The canonical correction on the composite overlap is independent of the
initial choice of lift on that overlap. -/
theorem ambientSpinCechCanonicalThirdCorrection_independent
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
    (firstThird alternativeThird :
      AmbientSpinOverlapLift period hPeriod reduction first third coordinate
        hFirstThird) :
    firstThird.kernelTranslate period hPeriod reduction first third coordinate
        hFirstThird
        (ambientSpinCechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird firstSecond
          secondThird firstThird) =
      alternativeThird.kernelTranslate period hPeriod reduction first third
        coordinate hFirstThird
        (ambientSpinCechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird firstSecond
          secondThird alternativeThird) := by
  rw [ambientSpinCechCanonicalThirdCorrection_eq_comp]
  rw [ambientSpinCechCanonicalThirdCorrection_eq_comp]

/-- Translating the second-to-third lift multiplies the Cech defect on the
left by the same kernel element. -/
theorem ambientSpinCechDefect_secondThird_kernelTranslate
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
      coordinate hFirstThird)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird firstSecond
        (secondThird.kernelTranslate period hPeriod reduction second third
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird kernel) firstThird =
      kernel.1 *
        ambientSpinCechDefect period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird := by
  simp [ambientSpinCechDefect, AmbientSpinOverlapLift.kernelTranslate,
    mul_assoc]

/-- Translating the first-to-second lift inserts the conjugated kernel element
on the left of the Cech defect.  No centrality assumption is used. -/
theorem ambientSpinCechDefect_firstSecond_kernelTranslate
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
      coordinate hFirstThird)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird
        (firstSecond.kernelTranslate period hPeriod reduction first second
          coordinate hFirstSecond kernel) secondThird firstThird =
      (ambientSpinKernelConjugate secondThird.lift kernel).1 *
        ambientSpinCechDefect period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird firstSecond secondThird firstThird := by
  simp [ambientSpinCechDefect, AmbientSpinOverlapLift.kernelTranslate,
    ambientSpinKernelConjugate, mul_assoc]

/-- On every actual triple overlap for which two Spin lifts are supplied, the
third lift obtained by composition has exactly trivial Cech defect.  This is a
local coherence theorem; it does not assert a global choice of overlap lifts. -/
theorem ambientSpinCechDefect_comp_eq_one
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
    ambientSpinCechDefect period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird firstSecond secondThird
        (firstSecond.comp period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird secondThird) = 1 := by
  apply (ambientSpinCechDefect_eq_one_iff period hPeriod reduction
    first second third coordinate hFirstSecond hSecondThird hFirstThird
    firstSecond secondThird
    (firstSecond.comp period hPeriod reduction first second third coordinate
      hFirstSecond hSecondThird hFirstThird secondThird)).2
  rfl

end

end P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
end JanusFormal
