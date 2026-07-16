import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinOrientation

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
open P0EFTJanusMappingTorusAmbientSpinOrientation

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

/-- Every actual transition admitting a Spin lift is necessarily orientation
preserving.  This records the first obstruction before any Cech coherence is
considered. -/
theorem AmbientSpinOverlapLift.orthogonalTransition_det
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (overlapLift : AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) :
    LinearEquiv.det
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv = (1 : Realˣ) := by
  rw [← overlapLift.projects]
  exact ambientSpinProjection_det overlapLift.lift

/-- An orientation-reversing reduced transition has no pointwise lift through
the genuine ambient Spin projection. -/
theorem ambientSpinOverlapLift_not_nonempty_of_det_ne_one
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hDet : LinearEquiv.det
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv ≠ (1 : Realˣ)) :
    ¬ Nonempty (AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) := by
  rintro ⟨overlapLift⟩
  exact hDet (overlapLift.orthogonalTransition_det period hPeriod reduction
    first second coordinate hCoordinate)

/-- A simultaneous pointwise choice of Spin lift on every atlas overlap.
This is strictly weaker than a Spin Cech lift: no normalization, continuity,
or cocycle law is included. -/
structure AmbientSpinAtlasLiftChoice
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  transitionLift :
    AmbientCover period hPeriod → AmbientCover period hPeriod →
      CoverModel → AmbientCoordinateSpinGroup
  projects :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      ambientSpinProjection (transitionLift first second coordinate) =
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv

/-- The pointwise overlap lift selected by an atlas-wide choice. -/
def AmbientSpinAtlasLiftChoice.overlapLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate where
  lift := choice.transitionLift first second coordinate
  projects := choice.projects first second coordinate hCoordinate

/-- Forgetting normalization and the cocycle of a full Cech transition lift
leaves an atlas-wide pointwise lift choice. -/
def ambientSpinCechTransitionLiftToAtlasLiftChoice
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (lift : AmbientSpinCechTransitionLift period hPeriod reduction) :
    AmbientSpinAtlasLiftChoice period hPeriod reduction where
  transitionLift := lift.transitionLift
  projects := lift.projects_to_transition

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

/-- An element in the projection kernel commutes with every element of the
ambient Clifford algebra.  The kernel condition gives commutation with every
Clifford generator, and the Clifford induction principle extends it to the
whole algebra. -/
theorem ambientSpinKernel_commutes_clifford
    (kernel : MonoidHom.ker ambientSpinProjection)
    (value : AmbientCliffordAlgebra) :
    Commute (kernel.1 : AmbientCliffordAlgebra) value := by
  induction value using CliffordAlgebra.induction with
  | algebraMap scalar =>
      exact (Algebra.commutes scalar
        (kernel.1 : AmbientCliffordAlgebra)).symm
  | ι vector =>
      have hAction : ambientSpinVectorAction kernel.1 vector = vector := by
        rw [← ambientSpinProjection_apply, kernel.property]
        rfl
      have hConjugation :
          (kernel.1 : AmbientCliffordAlgebra) *
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector *
              (↑(kernel.1⁻¹) : AmbientCliffordAlgebra) =
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector := by
        have hSpec := (ambientSpinVectorAction_spec kernel.1 vector).symm
        rw [hAction] at hSpec
        exact hSpec
      have hInvMul :
          (↑(kernel.1⁻¹) : AmbientCliffordAlgebra) *
              (kernel.1 : AmbientCliffordAlgebra) = 1 :=
        spinGroup.coe_star_mul_self kernel.1
      show (kernel.1 : AmbientCliffordAlgebra) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector =
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector *
          (kernel.1 : AmbientCliffordAlgebra)
      calc
        (kernel.1 : AmbientCliffordAlgebra) *
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector =
            ((kernel.1 : AmbientCliffordAlgebra) *
                CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector) *
              ((↑(kernel.1⁻¹) : AmbientCliffordAlgebra) *
                (kernel.1 : AmbientCliffordAlgebra)) := by rw [hInvMul, mul_one]
        _ = ((kernel.1 : AmbientCliffordAlgebra) *
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector *
              (↑(kernel.1⁻¹) : AmbientCliffordAlgebra)) *
            (kernel.1 : AmbientCliffordAlgebra) := by simp only [mul_assoc]
        _ = CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector *
            (kernel.1 : AmbientCliffordAlgebra) := by rw [hConjugation]
  | mul first second hFirst hSecond => exact hFirst.mul_right hSecond
  | add first second hFirst hSecond => exact hFirst.add_right hSecond

/-- The projection kernel is central in the ambient Spin group. -/
theorem ambientSpinKernel_commutes
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    Commute spin kernel.1 := by
  change spin * kernel.1 = kernel.1 * spin
  apply Subtype.ext
  exact (ambientSpinKernel_commutes_clifford kernel
    (spin : AmbientCliffordAlgebra)).symm.eq

/-- In particular, multiplication in the projection kernel is commutative. -/
theorem ambientSpinProjection_ker_mul_comm
    (first second : MonoidHom.ker ambientSpinProjection) :
    first * second = second * first := by
  apply Subtype.ext
  exact (ambientSpinKernel_commutes first.1 second).eq

/-- The adjoint action on the projection kernel is genuinely trivial. -/
theorem ambientSpinKernelConjugationRepresentation_trivial :
    ambientSpinKernelConjugationRepresentation = 1 :=
  ambientSpinKernelConjugationRepresentation_eq_one_iff.2
    ambientSpinKernel_commutes

@[simp]
theorem ambientSpinKernelConjugate_eq_self
    (spin : AmbientCoordinateSpinGroup)
    (kernel : MonoidHom.ker ambientSpinProjection) :
    ambientSpinKernelConjugate spin kernel = kernel :=
  (ambientSpinKernelConjugate_eq_iff_commute spin kernel).2
    (ambientSpinKernel_commutes spin kernel)

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

/-- Since the projection kernel is central, a common kernel translation
actually leaves the difference of two overlap lifts unchanged. -/
theorem ambientSpinOverlapLiftDifference_common_kernelTranslate_invariant
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
      ambientSpinOverlapLiftDifference period hPeriod reduction first second
        coordinate hCoordinate firstLift secondLift := by
  rw [ambientSpinOverlapLiftDifference_common_kernelTranslate,
    ambientSpinKernelConjugate_eq_self]

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

/-- Kernel-valued Cech defect attached to an atlas-wide pointwise lift
choice. -/
def AmbientSpinAtlasLiftChoice.cechKernelDefect
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source) :
    MonoidHom.ker ambientSpinProjection :=
  ambientSpinCechKernelDefect period hPeriod reduction first second third coordinate
    hFirstSecond hSecondThird hFirstThird
    (choice.overlapLift period hPeriod reduction first second coordinate hFirstSecond)
    (choice.overlapLift period hPeriod reduction second third
      (ambientAtlasTransition period hPeriod first second coordinate) hSecondThird)
    (choice.overlapLift period hPeriod reduction first third coordinate hFirstThird)

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

/-- A genuine Cech transition lift has trivial kernel defect after forgetting
down to its atlas-wide pointwise lift choice. -/
theorem AmbientSpinCechTransitionLift.toAtlasLiftChoice_cechKernelDefect_eq_one
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (lift : AmbientSpinCechTransitionLift period hPeriod reduction)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source) :
    (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod reduction lift).cechKernelDefect
        period hPeriod reduction first second third coordinate
        hFirstSecond hSecondThird hFirstThird = 1 := by
  apply Subtype.ext
  change lift.transitionLift second third
        (ambientAtlasTransition period hPeriod first second coordinate) *
        lift.transitionLift first second coordinate *
        (lift.transitionLift first third coordinate)⁻¹ = 1
  rw [lift.cocycle first second third coordinate
    hFirstSecond hSecondThird hFirstThird]
  simp

/-- Exact atlas-wide completion step: a normalized pointwise lift choice with
trivial kernel defect on every triple overlap produces the algebraic Spin
Cech transition lift.  Existence, continuity, and triviality of the supplied
defects remain separate obligations. -/
def AmbientSpinAtlasLiftChoice.toCechTransitionLiftOfDefectTrivial
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (hNormalized :
      ∀ anchor coordinate
        (_hCoordinate :
          coordinate ∈ (ambientAtlasTransition period hPeriod anchor anchor).source),
        choice.transitionLift anchor anchor coordinate = 1)
    (hDefectTrivial :
      ∀ first second third coordinate
        (hFirstSecond :
          coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
        (hSecondThird :
          ambientAtlasTransition period hPeriod first second coordinate ∈
            (ambientAtlasTransition period hPeriod second third).source)
        (hFirstThird :
          coordinate ∈ (ambientAtlasTransition period hPeriod first third).source),
        choice.cechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird = 1) :
    AmbientSpinCechTransitionLift period hPeriod reduction where
  transitionLift := choice.transitionLift
  projects_to_transition := choice.projects
  normalized := hNormalized
  cocycle := by
    intro first second third coordinate hFirstSecond hSecondThird hFirstThird
    have hValue := congrArg Subtype.val
      (hDefectTrivial first second third coordinate
        hFirstSecond hSecondThird hFirstThird)
    change choice.transitionLift second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
          choice.transitionLift first second coordinate *
          (choice.transitionLift first third coordinate)⁻¹ = 1 at hValue
    exact mul_inv_eq_one.mp hValue

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

/-- Kernel-valued coboundary law for a translation of the second-to-third
lift. -/
theorem ambientSpinCechKernelDefect_secondThird_kernelTranslate
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
    ambientSpinCechKernelDefect period hPeriod reduction first second third
        coordinate hFirstSecond hSecondThird hFirstThird firstSecond
        (secondThird.kernelTranslate period hPeriod reduction second third
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird kernel) firstThird =
      kernel * ambientSpinCechKernelDefect period hPeriod reduction first second
        third coordinate hFirstSecond hSecondThird hFirstThird firstSecond
        secondThird firstThird := by
  apply Subtype.ext
  exact ambientSpinCechDefect_secondThird_kernelTranslate period hPeriod
    reduction first second third coordinate hFirstSecond hSecondThird hFirstThird
    firstSecond secondThird firstThird kernel

/-- Kernel-valued coboundary law for a translation of the first-to-second
lift; the translating kernel is transported by the intervening lift. -/
theorem ambientSpinCechKernelDefect_firstSecond_kernelTranslate
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
    ambientSpinCechKernelDefect period hPeriod reduction first second third
        coordinate hFirstSecond hSecondThird hFirstThird
        (firstSecond.kernelTranslate period hPeriod reduction first second
          coordinate hFirstSecond kernel) secondThird firstThird =
      ambientSpinKernelConjugate secondThird.lift kernel *
        ambientSpinCechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird firstSecond
          secondThird firstThird := by
  apply Subtype.ext
  exact ambientSpinCechDefect_firstSecond_kernelTranslate period hPeriod
    reduction first second third coordinate hFirstSecond hSecondThird hFirstThird
    firstSecond secondThird firstThird kernel

/-- Exact nonabelian quadruple-overlap identity for any atlas-wide pointwise
choice of Spin lifts.  The conjugation is the usual transport of the first
triple defect across the last edge. -/
theorem AmbientSpinAtlasLiftChoice.cechKernelDefect_quadruple_conjugated
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (first second third fourth : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (hThirdFourth :
      ambientAtlasTransition period hPeriod first third coordinate ∈
        (ambientAtlasTransition period hPeriod third fourth).source)
    (hSecondFourth :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second fourth).source)
    (hFirstFourth :
      coordinate ∈ (ambientAtlasTransition period hPeriod first fourth).source) :
    let hThirdFourthNested :
        ambientAtlasTransition period hPeriod second third
            (ambientAtlasTransition period hPeriod first second coordinate) ∈
          (ambientAtlasTransition period hPeriod third fourth).source := by
      rw [ambientAtlasTransition_cocycle_apply period hPeriod first second third
        coordinate hFirstSecond hSecondThird]
      exact hThirdFourth
    ambientSpinKernelConjugate
          (choice.transitionLift third fourth
            (ambientAtlasTransition period hPeriod first third coordinate))
          (choice.cechKernelDefect period hPeriod reduction first second third
            coordinate hFirstSecond hSecondThird hFirstThird) *
        choice.cechKernelDefect period hPeriod reduction first third fourth
          coordinate hFirstThird hThirdFourth hFirstFourth =
      choice.cechKernelDefect period hPeriod reduction second third fourth
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird hThirdFourthNested hSecondFourth *
        choice.cechKernelDefect period hPeriod reduction first second fourth
          coordinate hFirstSecond hSecondFourth hFirstFourth := by
  dsimp only
  apply Subtype.ext
  simp [AmbientSpinAtlasLiftChoice.cechKernelDefect,
    ambientSpinCechKernelDefect, ambientSpinCechDefect,
    ambientSpinKernelConjugate, AmbientSpinAtlasLiftChoice.overlapLift,
    ambientAtlasTransition_cocycle_apply period hPeriod first second third
      coordinate hFirstSecond hSecondThird, mul_assoc]

/-- Because the genuine Spin projection kernel is central, the transported
quadruple identity reduces to the ordinary abelian Cech two-cocycle law. -/
theorem AmbientSpinAtlasLiftChoice.cechKernelDefect_quadruple
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (first second third fourth : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird :
      coordinate ∈ (ambientAtlasTransition period hPeriod first third).source)
    (hThirdFourth :
      ambientAtlasTransition period hPeriod first third coordinate ∈
        (ambientAtlasTransition period hPeriod third fourth).source)
    (hSecondFourth :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second fourth).source)
    (hFirstFourth :
      coordinate ∈ (ambientAtlasTransition period hPeriod first fourth).source) :
    let hThirdFourthNested :
        ambientAtlasTransition period hPeriod second third
            (ambientAtlasTransition period hPeriod first second coordinate) ∈
          (ambientAtlasTransition period hPeriod third fourth).source := by
      rw [ambientAtlasTransition_cocycle_apply period hPeriod first second third
        coordinate hFirstSecond hSecondThird]
      exact hThirdFourth
    choice.cechKernelDefect period hPeriod reduction first second third
          coordinate hFirstSecond hSecondThird hFirstThird *
        choice.cechKernelDefect period hPeriod reduction first third fourth
          coordinate hFirstThird hThirdFourth hFirstFourth =
      choice.cechKernelDefect period hPeriod reduction second third fourth
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird hThirdFourthNested hSecondFourth *
        choice.cechKernelDefect period hPeriod reduction first second fourth
          coordinate hFirstSecond hSecondFourth hFirstFourth := by
  dsimp only
  have hQuadruple :=
    choice.cechKernelDefect_quadruple_conjugated period hPeriod reduction
      first second third fourth coordinate hFirstSecond hSecondThird hFirstThird
      hThirdFourth hSecondFourth hFirstFourth
  rw [ambientSpinKernelConjugate_eq_self] at hQuadruple
  exact hQuadruple

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
