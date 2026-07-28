import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCMonopoleFiniteFrame4D

/-!
# Primitive SpinC monopole finite frame

This gate constructs the signed two-dimensional Hopf sector planes in the
doubled matter fiber and proves the exact Gram identities of the geometric
seed/tangential frame.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance d9DoubledMatterFiberComplexModule :
    Module Complex D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorLinearEquiv.toAddEquiv.module Complex

@[simp]
theorem d9DoubledMatterFiber_complex_smul_eq_action
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    scalar • matter =
      d9PrimitiveSpinCComplexActionCLM scalar matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp [Equiv.smul_def]

@[simp]
theorem d9PrimitiveSpinCComplexActionCLM_zero
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM 0 matter = 0 := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  ext <;> simp

@[simp]
theorem d9DoubledMatterSpinorHermitianPairing_zero_right
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing matter 0 = 0 := by
  have hAdd :=
    d9DoubledMatterSpinorHermitianPairing_add_right matter 0 0
  simp only [zero_add] at hAdd
  have hCancel :
      0 + d9DoubledMatterSpinorHermitianPairing matter 0 =
        d9DoubledMatterSpinorHermitianPairing matter 0 +
          d9DoubledMatterSpinorHermitianPairing matter 0 := by
    simpa using hAdd
  exact (add_right_cancel hCancel).symm

@[simp]
theorem d9DoubledMatterSpinorHermitianPairing_zero_left
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing 0 matter = 0 := by
  rw [← d9DoubledMatterSpinorHermitianPairing_conj_symm]
  simp

def d9DoubledMatterSpinorHermitianPairingRightLinearMap
    (left : D9DoubledMatterFiber) :
    D9DoubledMatterFiber →ₗ[Complex] Complex where
  toFun right :=
    d9DoubledMatterSpinorHermitianPairing left right
  map_add' :=
    d9DoubledMatterSpinorHermitianPairing_add_right left
  map_smul' scalar right := by
    rw [d9DoubledMatterFiber_complex_smul_eq_action,
      d9DoubledMatterSpinorHermitianPairing_complexAction_right]
    rfl

def geometricSectorSubmodule (sector : NormalRootChoice) :
    Submodule Complex D9DoubledMatterFiber where
  carrier := PrimitiveSpinCGeometricSectorPlane sector
  zero_mem' := primitiveSpinCGeometricSectorPlane_zero sector
  add_mem' := fun hFirst hSecond =>
    primitiveSpinCGeometricSectorPlane_add
      sector _ _ hFirst hSecond
  smul_mem' := by
    intro scalar matter hMatter
    rw [d9DoubledMatterFiber_complex_smul_eq_action]
    exact primitiveSpinCGeometricSectorPlane_complexAction
      sector scalar matter hMatter

def d9DoubledMatterFiberHalfSpinorComplexLinearEquiv :
    D9DoubledMatterFiber ≃ₗ[Complex] D9DoubledMatterSpinor :=
  d9DoubledMatterFiberHalfSpinorLinearEquiv.toAddEquiv.linearEquiv
    Complex

local instance d9DoubledMatterFiberComplexFiniteDimensional :
    FiniteDimensional Complex D9DoubledMatterFiber :=
  FiniteDimensional.of_injective
    d9DoubledMatterFiberHalfSpinorComplexLinearEquiv.toLinearMap
    d9DoubledMatterFiberHalfSpinorComplexLinearEquiv.injective

theorem d9DoubledMatterFiber_complex_finrank :
    Module.finrank Complex D9DoubledMatterFiber = 4 := by
  rw [LinearEquiv.finrank_eq
    d9DoubledMatterFiberHalfSpinorComplexLinearEquiv]
  simp [D9DoubledMatterSpinor]

def geometricSectorHalfSpinorSynthesis
    (sector : NormalRootChoice) :
    (Complex × Complex) →ₗ[Complex] D9DoubledMatterSpinor where
  toFun coefficients :=
    match sector with
    | .positiveQuarter =>
        (coefficients.1 • ambientHalfGammaPositiveEigenvector,
          coefficients.2 • ambientHalfGammaTransverseVector)
    | .negativeQuarter =>
        (coefficients.1 • ambientHalfGammaTransverseVector,
          coefficients.2 • ambientHalfGammaPositiveEigenvector)
  map_add' first second := by
    cases sector <;>
      apply Prod.ext <;>
      simp [add_smul]
  map_smul' scalar coefficients := by
    cases sector <;>
      apply Prod.ext <;>
      simp [smul_smul]

def geometricSectorSynthesis
    (sector : NormalRootChoice) :
    (Complex × Complex) →ₗ[Complex] D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorComplexLinearEquiv.symm.toLinearMap.comp
    (geometricSectorHalfSpinorSynthesis sector)

theorem geometricSectorHalfSpinorSynthesis_injective
    (sector : NormalRootChoice) :
    Function.Injective (geometricSectorHalfSpinorSynthesis sector) := by
  intro first second hEqual
  apply Prod.ext
  · have hCoordinate :=
      congrArg (fun spinor : D9DoubledMatterSpinor => spinor.1 0)
        hEqual
    cases sector <;>
      simpa [geometricSectorHalfSpinorSynthesis,
        ambientHalfGammaPositiveEigenvector,
        ambientHalfGammaTransverseVector] using hCoordinate
  · have hCoordinate :=
      congrArg (fun spinor : D9DoubledMatterSpinor => spinor.2 0)
        hEqual
    cases sector <;>
      simpa [geometricSectorHalfSpinorSynthesis,
        ambientHalfGammaPositiveEigenvector,
        ambientHalfGammaTransverseVector] using hCoordinate

theorem geometricSectorSynthesis_injective
    (sector : NormalRootChoice) :
    Function.Injective (geometricSectorSynthesis sector) :=
  (d9DoubledMatterFiberHalfSpinorComplexLinearEquiv.symm.injective
    ).comp (geometricSectorHalfSpinorSynthesis_injective sector)

theorem geometricSectorSubmodule_eq_range
    (sector : NormalRootChoice) :
    geometricSectorSubmodule sector =
      LinearMap.range (geometricSectorSynthesis sector) := by
  ext matter
  constructor
  · intro hMatter
    cases sector with
    | positiveQuarter =>
        rcases hMatter with ⟨first, second, hMatter⟩
        refine ⟨(first, second), ?_⟩
        apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
        simpa [geometricSectorSynthesis,
          d9DoubledMatterFiberHalfSpinorComplexLinearEquiv,
          geometricSectorHalfSpinorSynthesis] using hMatter.symm
    | negativeQuarter =>
        rcases hMatter with ⟨first, second, hMatter⟩
        refine ⟨(first, second), ?_⟩
        apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
        simpa [geometricSectorSynthesis,
          d9DoubledMatterFiberHalfSpinorComplexLinearEquiv,
          geometricSectorHalfSpinorSynthesis] using hMatter.symm
  · rintro ⟨coefficients, rfl⟩
    cases sector with
    | positiveQuarter =>
        exact ⟨coefficients.1, coefficients.2, by
          simp [geometricSectorSynthesis,
            d9DoubledMatterFiberHalfSpinorComplexLinearEquiv,
            geometricSectorHalfSpinorSynthesis]⟩
    | negativeQuarter =>
        exact ⟨coefficients.1, coefficients.2, by
          simp [geometricSectorSynthesis,
            d9DoubledMatterFiberHalfSpinorComplexLinearEquiv,
            geometricSectorHalfSpinorSynthesis]⟩

theorem geometricSectorSubmodule_finrank
    (sector : NormalRootChoice) :
    Module.finrank Complex (geometricSectorSubmodule sector) = 2 := by
  rw [geometricSectorSubmodule_eq_range,
    LinearMap.finrank_range_of_inj
      (geometricSectorSynthesis_injective sector)]
  simp

theorem geometricSectorSubmodules_inf_eq_bot :
    geometricSectorSubmodule .positiveQuarter ⊓
        geometricSectorSubmodule .negativeQuarter =
      ⊥ := by
  apply bot_unique
  intro matter hMatter
  have hPairing :
      d9DoubledMatterSpinorHermitianPairing matter matter = 0 :=
    d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero
      matter matter hMatter.1 hMatter.2
  have hMatterZero : matter = 0 := by
    apply
      (d9DoubledMatterSpinorHermitianPairing_self_re_eq_zero_iff
        matter).mp
    rw [hPairing]
    rfl
  simpa [hMatterZero]

theorem geometricSectorSubmodules_sup_eq_top :
    geometricSectorSubmodule .positiveQuarter ⊔
        geometricSectorSubmodule .negativeQuarter =
      ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hDimension :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (geometricSectorSubmodule .positiveQuarter)
      (geometricSectorSubmodule .negativeQuarter)
  rw [geometricSectorSubmodules_inf_eq_bot,
    geometricSectorSubmodule_finrank,
    geometricSectorSubmodule_finrank] at hDimension
  simp at hDimension
  rw [d9DoubledMatterFiber_complex_finrank]
  omega

theorem d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero_of_ne
    (firstSector secondSector : NormalRootChoice)
    (hSectors : firstSector ≠ secondSector)
    (first second : D9DoubledMatterFiber)
    (hFirst : PrimitiveSpinCGeometricSectorPlane firstSector first)
    (hSecond : PrimitiveSpinCGeometricSectorPlane secondSector second) :
    d9DoubledMatterSpinorHermitianPairing first second = 0 := by
  cases firstSector <;> cases secondSector
  · exact (hSectors rfl).elim
  · exact
      d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero
        first second hFirst hSecond
  · rw [← d9DoubledMatterSpinorHermitianPairing_conj_symm]
    rw [
      d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero
        second first hSecond hFirst]
    simp
  · exact (hSectors rfl).elim

def geometricHopfFrameSpan
    (seed : D9DoubledMatterFiber)
    (tangent : Fin 3 → D9DoubledMatterFiber) :
    Submodule Complex D9DoubledMatterFiber :=
  Submodule.span Complex
    (Set.insert seed (Set.range tangent))

def geometricPairSynthesis
    (seed tangent : D9DoubledMatterFiber) :
    (Complex × Complex) →ₗ[Complex] D9DoubledMatterFiber where
  toFun coefficients :=
    coefficients.1 • seed + coefficients.2 • tangent
  map_add' first second := by
    simp [add_smul]
    abel
  map_smul' scalar coefficients := by
    change
      (scalar * coefficients.1) • seed +
          (scalar * coefficients.2) • tangent =
        scalar •
          (coefficients.1 • seed + coefficients.2 • tangent)
    module

theorem geometricPairSynthesis_injective_of_orthogonal
    (seed tangent : D9DoubledMatterFiber)
    (hSeedSelf :
      d9DoubledMatterSpinorHermitianPairing seed seed = 8)
    (hSeedTangent :
      d9DoubledMatterSpinorHermitianPairing seed tangent = 0)
    (hTangent : tangent ≠ 0) :
    Function.Injective (geometricPairSynthesis seed tangent) := by
  have hKernel :
      ∀ coefficients : Complex × Complex,
        geometricPairSynthesis seed tangent coefficients = 0 →
          coefficients = 0 := by
    intro coefficients hZero
    change
      coefficients.1 • seed + coefficients.2 • tangent = 0
      at hZero
    have hPair :=
      congrArg
        (fun matter =>
          d9DoubledMatterSpinorHermitianPairing seed matter)
        hZero
    rw [d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterFiber_complex_smul_eq_action,
      d9DoubledMatterFiber_complex_smul_eq_action,
      d9DoubledMatterSpinorHermitianPairing_complexAction_right,
      d9DoubledMatterSpinorHermitianPairing_complexAction_right,
      hSeedSelf, hSeedTangent] at hPair
    have hPairZero :
        d9DoubledMatterSpinorHermitianPairing seed 0 = 0 := by
      have hAdd :=
        d9DoubledMatterSpinorHermitianPairing_add_right
          seed 0 0
      simp only [zero_add] at hAdd
      have hCancel :
          0 +
              d9DoubledMatterSpinorHermitianPairing seed 0 =
            d9DoubledMatterSpinorHermitianPairing seed 0 +
              d9DoubledMatterSpinorHermitianPairing seed 0 := by
        simpa using hAdd
      exact (add_right_cancel hCancel).symm
    rw [hPairZero] at hPair
    simp only [mul_zero, add_zero] at hPair
    have hFirst : coefficients.1 = 0 := by
      exact (mul_eq_zero.mp hPair).resolve_right
        (by norm_num : (8 : Complex) ≠ 0)
    have hSecondAction :
        coefficients.2 • tangent = 0 := by
      simpa [geometricPairSynthesis, hFirst] using hZero
    have hSecond : coefficients.2 = 0 :=
      (smul_eq_zero.mp hSecondAction).resolve_right hTangent
    exact Prod.ext hFirst hSecond
  intro first second hEqual
  apply sub_eq_zero.mp
  apply hKernel (first - second)
  rw [map_sub, hEqual, sub_self]

theorem geometricHopfFrameSpan_eq_sector
    (sector : NormalRootChoice)
    (seed : D9DoubledMatterFiber)
    (tangent : Fin 3 → D9DoubledMatterFiber)
    (hSeedSector :
      PrimitiveSpinCGeometricSectorPlane sector seed)
    (hTangentSector :
      ∀ coordinate,
        PrimitiveSpinCGeometricSectorPlane sector
          (tangent coordinate))
    (hSeedSelf :
      d9DoubledMatterSpinorHermitianPairing seed seed = 8)
    (hSeedTangent :
      ∀ coordinate,
        d9DoubledMatterSpinorHermitianPairing
          seed (tangent coordinate) = 0)
    (hTangentNonzero :
      ∃ coordinate, tangent coordinate ≠ 0) :
    geometricHopfFrameSpan seed tangent =
      geometricSectorSubmodule sector := by
  have hLe :
      geometricHopfFrameSpan seed tangent ≤
        geometricSectorSubmodule sector := by
    apply Submodule.span_le.mpr
    rintro matter (rfl | ⟨coordinate, rfl⟩)
    · exact hSeedSector
    · exact hTangentSector coordinate
  apply Submodule.eq_of_le_of_finrank_le hLe
  rw [geometricSectorSubmodule_finrank]
  obtain ⟨coordinate, hCoordinate⟩ := hTangentNonzero
  let pairRange :=
    LinearMap.range
      (geometricPairSynthesis seed (tangent coordinate))
  have hPairRangeLe :
      pairRange ≤ geometricHopfFrameSpan seed tangent := by
    rintro matter ⟨coefficients, rfl⟩
    apply (geometricHopfFrameSpan seed tangent).add_mem
    · exact (geometricHopfFrameSpan seed tangent).smul_mem
        coefficients.1
        (Submodule.subset_span (Set.mem_insert seed _))
    · exact (geometricHopfFrameSpan seed tangent).smul_mem
        coefficients.2
        (Submodule.subset_span
          (Set.mem_insert_of_mem seed
            ⟨coordinate, rfl⟩))
  have hPairRangeFinrank :
      Module.finrank Complex pairRange = 2 := by
    unfold pairRange
    rw [LinearMap.finrank_range_of_inj
      (geometricPairSynthesis_injective_of_orthogonal
        seed (tangent coordinate) hSeedSelf
        (hSeedTangent coordinate) hCoordinate)]
    simp
  rw [← hPairRangeFinrank]
  exact Submodule.finrank_mono hPairRangeLe

theorem tangentialMatrix_mul
    (point : MonopoleSphere) (time : Real)
    (first second : Fin 3) :
    (∑ middle : Fin 3,
      primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first middle *
        primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          middle second) =
      2 *
        primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second := by
  have hSphere :
      (monopoleSphereCoordinate point 0 : Complex) ^ 2 +
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 +
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 = 1 := by
    exact_mod_cast monopoleSphereCoordinate_sq_sum point
  have hThird :
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 =
        1 -
          (monopoleSphereCoordinate point 0 : Complex) ^ 2 -
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 := by
    linear_combination hSphere
  have hThirdCube :
      (monopoleSphereCoordinate point 2 : Complex) ^ 3 =
        (monopoleSphereCoordinate point 2 : Complex) *
          (1 -
            (monopoleSphereCoordinate point 0 : Complex) ^ 2 -
            (monopoleSphereCoordinate point 1 : Complex) ^ 2) := by
    rw [show
      (monopoleSphereCoordinate point 2 : Complex) ^ 3 =
        (monopoleSphereCoordinate point 2 : Complex) *
          (monopoleSphereCoordinate point 2 : Complex) ^ 2 by ring,
      hThird]
  have hThirdFourth :
      (monopoleSphereCoordinate point 2 : Complex) ^ 4 =
        (1 -
            (monopoleSphereCoordinate point 0 : Complex) ^ 2 -
            (monopoleSphereCoordinate point 1 : Complex) ^ 2) ^ 2 := by
    rw [show
      (monopoleSphereCoordinate point 2 : Complex) ^ 4 =
        ((monopoleSphereCoordinate point 2 : Complex) ^ 2) ^ 2 by ring,
      hThird]
  fin_cases first <;> fin_cases second <;>
    simp [Fin.sum_univ_three,
      primitiveSpinCZeroModeTangentialPairingMatrix,
      d9PrimitiveSpinCBaseUnitRadialCoordinate,
      primitiveSpinCNullPacketMovingWitnessBase_coordinate] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    simp only [hThird, hThirdCube, hThirdFourth] <;>
    ring

theorem tangentialMatrix_trace
    (point : MonopoleSphere) (time : Real) :
    (∑ coordinate : Fin 3,
      primitiveSpinCZeroModeTangentialPairingMatrix
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        coordinate coordinate) = 2 := by
  have hSphere :
      (monopoleSphereCoordinate point 0 : Complex) ^ 2 +
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 +
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 = 1 := by
    exact_mod_cast monopoleSphereCoordinate_sq_sum point
  have hThird :
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 =
        1 -
          (monopoleSphereCoordinate point 0 : Complex) ^ 2 -
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 := by
    linear_combination hSphere
  simp [Fin.sum_univ_three,
    primitiveSpinCZeroModeTangentialPairingMatrix,
    d9PrimitiveSpinCBaseUnitRadialCoordinate,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  ring_nf
  rw [hThird]
  ring

theorem tangentialFrame_operator
    (point : MonopoleSphere) (time : Real)
    (sector : NormalRootChoice) (circleMode : Int)
    (second : Fin 3) :
    (∑ first : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second)
        (show D9DoubledMatterFiber from
          primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod first sector circleMode
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time))) =
      d9PrimitiveSpinCComplexActionCLM 2
        (show D9DoubledMatterFiber from
          primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod second sector circleMode
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) := by
  let base :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  let tangent : Fin 3 → D9DoubledMatterFiber := fun coordinate =>
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector circleMode base
  let matrix : Fin 3 → Fin 3 → Complex :=
    primitiveSpinCZeroModeTangentialPairingMatrix
      period hPeriod base
  let left : D9DoubledMatterFiber :=
    ∑ first : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
        (matrix first second) (tangent first)
  let right : D9DoubledMatterFiber :=
    d9PrimitiveSpinCComplexActionCLM 2 (tangent second)
  change left = right
  have hPair (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) left =
        d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) right := by
    have hMatrix :=
      tangentialMatrix_mul
        period hPeriod point time coordinate second
    simp only [Fin.sum_univ_three] at hMatrix
    unfold left right
    simp only [Fin.sum_univ_three,
      d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterSpinorHermitianPairing_complexAction_right]
    simp only [tangent, matrix, base,
      primitiveSpinCHopfZeroMode_tangential_pairing,
      primitiveSpinCHopfZeroMode_pointwise_self_eq_eight]
    linear_combination 8 * hMatrix
  let residual := left - right
  have hResidualPair (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) residual = 0 := by
    unfold residual
    rw [show left - right = left + (-right) by abel,
      d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterSpinorHermitianPairing_neg_right,
      hPair]
    ring
  have hResidualSelf :
      d9DoubledMatterSpinorHermitianPairing residual residual = 0 := by
    change
      d9DoubledMatterSpinorHermitianPairing
        (left - right) residual = 0
    rw [show
      left - right =
        (∑ first : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
            (matrix first second) (tangent first)) +
          (-d9PrimitiveSpinCComplexActionCLM 2
            (tangent second)) by
          unfold left right
          abel,
      d9DoubledMatterSpinorHermitianPairing_add_left,
      d9DoubledMatterSpinorHermitianPairing_neg_left]
    simp only [Fin.sum_univ_three,
      d9DoubledMatterSpinorHermitianPairing_add_left,
      d9DoubledMatterSpinorHermitianPairing_complexAction_left,
      hResidualPair, mul_zero, add_zero, neg_zero]
  have hResidualZero : residual = 0 := by
    apply
      (d9DoubledMatterSpinorHermitianPairing_self_re_eq_zero_iff
        residual).mp
    rw [hResidualSelf]
    rfl
  exact sub_eq_zero.mp hResidualZero

def localHopfFrameSeed
    (point : MonopoleSphere) (chart : MonopoleChart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode)

def localHopfFrameTangent
    (point : MonopoleSphere) (chart : MonopoleChart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (coordinate : Fin 3) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector circleMode)

theorem localHopfFrameSeed_self
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    d9DoubledMatterSpinorHermitianPairing
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time)
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time) = 8 := by
  unfold localHopfFrameSeed
  rw [← d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time)]
  exact primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
    period hPeriod sector circleMode point time

theorem localHopfFrameSeed_tangent_orthogonal
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (coordinate : Fin 3) :
    d9DoubledMatterSpinorHermitianPairing
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time)
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time coordinate) =
      0 := by
  unfold localHopfFrameSeed localHopfFrameTangent
  rw [← d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time)]
  exact primitiveSpinCHopfZeroMode_tangential_pointwise_orthogonal
    period hPeriod coordinate sector circleMode
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)

theorem localHopfFrameTangent_pairing
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (first second : Fin 3) :
    d9DoubledMatterSpinorHermitianPairing
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time first)
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time second) =
      8 *
        primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second := by
  unfold localHopfFrameTangent
  rw [← d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time)]
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  rw [primitiveSpinCHopfZeroMode_tangential_pairing,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight]
  ring

theorem localHopfFrameTangent_operator
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (second : Fin 3) :
    (∑ first : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second)
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time first)) =
      d9PrimitiveSpinCComplexActionCLM 2
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time second) := by
  let tangent : Fin 3 → D9DoubledMatterFiber :=
    localHopfFrameTangent
      period hPeriod point chart sector circleMode time
  let matrix : Fin 3 → Fin 3 → Complex :=
    primitiveSpinCZeroModeTangentialPairingMatrix
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
  let left : D9DoubledMatterFiber :=
    ∑ first : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
        (matrix first second) (tangent first)
  let right : D9DoubledMatterFiber :=
    d9PrimitiveSpinCComplexActionCLM 2 (tangent second)
  change left = right
  have hPair (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) left =
        d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) right := by
    have hMatrix :=
      tangentialMatrix_mul
        period hPeriod point time coordinate second
    simp only [Fin.sum_univ_three] at hMatrix
    unfold left right
    simp only [Fin.sum_univ_three,
      d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterSpinorHermitianPairing_complexAction_right]
    simp only [tangent, matrix,
      localHopfFrameTangent_pairing
        period hPeriod point chart hChart sector circleMode time]
    linear_combination 8 * hMatrix
  let residual := left - right
  have hResidualPair (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) residual = 0 := by
    unfold residual
    rw [show left - right = left + (-right) by abel,
      d9DoubledMatterSpinorHermitianPairing_add_right,
      d9DoubledMatterSpinorHermitianPairing_neg_right,
      hPair]
    ring
  have hResidualSelf :
      d9DoubledMatterSpinorHermitianPairing residual residual = 0 := by
    change
      d9DoubledMatterSpinorHermitianPairing
        (left - right) residual = 0
    rw [show
      left - right =
        (∑ first : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
            (matrix first second) (tangent first)) +
          (-d9PrimitiveSpinCComplexActionCLM 2
            (tangent second)) by
          unfold left right
          abel,
      d9DoubledMatterSpinorHermitianPairing_add_left,
      d9DoubledMatterSpinorHermitianPairing_neg_left]
    simp only [Fin.sum_univ_three,
      d9DoubledMatterSpinorHermitianPairing_add_left,
      d9DoubledMatterSpinorHermitianPairing_complexAction_left,
      hResidualPair, mul_zero, add_zero, neg_zero]
  have hResidualZero : residual = 0 := by
    apply
      (d9DoubledMatterSpinorHermitianPairing_self_re_eq_zero_iff
        residual).mp
    rw [hResidualSelf]
    rfl
  exact sub_eq_zero.mp hResidualZero

def localHopfFrameReconstruction
    (point : MonopoleSphere) (chart : MonopoleChart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    D9DoubledMatterFiber →ₗ[Complex] D9DoubledMatterFiber :=
  (8 : Complex)⁻¹ •
      LinearMap.smulRight
        (d9DoubledMatterSpinorHermitianPairingRightLinearMap
          (localHopfFrameSeed
            period hPeriod point chart sector circleMode time))
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time) +
    ∑ coordinate : Fin 3,
      (16 : Complex)⁻¹ •
        LinearMap.smulRight
          (d9DoubledMatterSpinorHermitianPairingRightLinearMap
            (localHopfFrameTangent
              period hPeriod point chart sector circleMode time coordinate))
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time coordinate)

theorem localHopfFrameReconstruction_apply
    (point : MonopoleSphere) (chart : MonopoleChart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (matter : D9DoubledMatterFiber) :
    localHopfFrameReconstruction
        period hPeriod point chart sector circleMode time matter =
      d9PrimitiveSpinCComplexActionCLM
          ((8 : Complex)⁻¹ *
            d9DoubledMatterSpinorHermitianPairing
              (localHopfFrameSeed
                period hPeriod point chart sector circleMode time)
              matter)
          (localHopfFrameSeed
            period hPeriod point chart sector circleMode time) +
        ∑ coordinate : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
              ((16 : Complex)⁻¹ *
                d9DoubledMatterSpinorHermitianPairing
                  (localHopfFrameTangent
                    period hPeriod point chart sector circleMode time
                      coordinate)
                  matter)
            (localHopfFrameTangent
              period hPeriod point chart sector circleMode time
                coordinate) := by
  simp only [localHopfFrameReconstruction, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply,
    Fin.sum_univ_three,
    d9DoubledMatterFiber_complex_smul_eq_action,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1 <;> ring

theorem localHopfFrameTangent_exists_ne_zero
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    ∃ coordinate : Fin 3,
      localHopfFrameTangent
        period hPeriod point chart sector circleMode time coordinate ≠ 0 := by
  by_contra h
  push Not at h
  have hPairingSum :
      (∑ coordinate : Fin 3,
        d9DoubledMatterSpinorHermitianPairing
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time coordinate)
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time coordinate)) =
        0 := by
    simp [h]
  have hTrace :=
    tangentialMatrix_trace period hPeriod point time
  simp_rw [localHopfFrameTangent_pairing
    period hPeriod point chart hChart sector circleMode time]
    at hPairingSum
  rw [← Finset.mul_sum] at hPairingSum
  rw [hTrace] at hPairingSum
  norm_num at hPairingSum

theorem localHopfFrameReconstruction_seed
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    localHopfFrameReconstruction
        period hPeriod point chart sector circleMode time
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time) =
      localHopfFrameSeed
        period hPeriod point chart sector circleMode time := by
  have hReverseOrthogonal (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time coordinate)
          (localHopfFrameSeed
            period hPeriod point chart sector circleMode time) = 0 := by
    rw [← d9DoubledMatterSpinorHermitianPairing_conj_symm,
      localHopfFrameSeed_tangent_orthogonal
        period hPeriod point chart hChart sector circleMode time coordinate]
    simp
  rw [localHopfFrameReconstruction_apply,
    localHopfFrameSeed_self
      period hPeriod point chart hChart sector circleMode time]
  simp_rw [hReverseOrthogonal]
  simp [d9PrimitiveSpinCComplexAction_one]

theorem localHopfFrameReconstruction_tangent
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (second : Fin 3) :
    localHopfFrameReconstruction
        period hPeriod point chart sector circleMode time
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time second) =
      localHopfFrameTangent
        period hPeriod point chart sector circleMode time second := by
  rw [localHopfFrameReconstruction_apply,
    localHopfFrameSeed_tangent_orthogonal
      period hPeriod point chart hChart sector circleMode time second]
  simp only [mul_zero, d9PrimitiveSpinCComplexActionCLM_zero, zero_add]
  simp_rw [localHopfFrameTangent_pairing
    period hPeriod point chart hChart sector circleMode time]
  have hOperator :=
    localHopfFrameTangent_operator
      period hPeriod point chart hChart sector circleMode time second
  rw [show
      (∑ coordinate : Fin 3,
        d9PrimitiveSpinCComplexActionCLM
            ((16 : Complex)⁻¹ *
              (8 *
                primitiveSpinCZeroModeTangentialPairingMatrix
                  period hPeriod
                  (primitiveSpinCNullPacketMovingWitnessBase
                    period hPeriod point time)
                  coordinate second))
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time coordinate)) =
        d9PrimitiveSpinCComplexActionCLM (2 : Complex)⁻¹
          (∑ coordinate : Fin 3,
            d9PrimitiveSpinCComplexActionCLM
                (primitiveSpinCZeroModeTangentialPairingMatrix
                  period hPeriod
                  (primitiveSpinCNullPacketMovingWitnessBase
                    period hPeriod point time)
                  coordinate second)
              (localHopfFrameTangent
                period hPeriod point chart sector circleMode time
                  coordinate)) by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro coordinate _
        have hScalar :
            (16 : Complex)⁻¹ *
                (8 *
                  primitiveSpinCZeroModeTangentialPairingMatrix
                    period hPeriod
                    (primitiveSpinCNullPacketMovingWitnessBase
                      period hPeriod point time)
                    coordinate second) =
              (2 : Complex)⁻¹ *
                primitiveSpinCZeroModeTangentialPairingMatrix
                  period hPeriod
                  (primitiveSpinCNullPacketMovingWitnessBase
                    period hPeriod point time)
                  coordinate second := by
          apply Complex.ext <;> norm_num <;> ring
        rw [hScalar, d9PrimitiveSpinCComplexAction_mul]]
  rw [hOperator, ← d9PrimitiveSpinCComplexAction_mul]
  norm_num

theorem localHopfFrameSpan_eq_sector
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    geometricHopfFrameSpan
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time)
        (localHopfFrameTangent
          period hPeriod point chart sector circleMode time) =
      geometricSectorSubmodule sector := by
  apply geometricHopfFrameSpan_eq_sector
  · exact primitiveSpinCHopfZeroModeLocalCoordinate_sectorPlane
      period hPeriod point chart hChart sector circleMode time
  · intro coordinate
    exact
      primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_sectorPlane
        period hPeriod point chart hChart coordinate sector circleMode time
  · exact localHopfFrameSeed_self
      period hPeriod point chart hChart sector circleMode time
  · intro coordinate
    exact localHopfFrameSeed_tangent_orthogonal
      period hPeriod point chart hChart sector circleMode time coordinate
  · exact localHopfFrameTangent_exists_ne_zero
      period hPeriod point chart hChart sector circleMode time

theorem localHopfFrameReconstruction_eq_self_of_sector
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter : PrimitiveSpinCGeometricSectorPlane sector matter) :
    localHopfFrameReconstruction
        period hPeriod point chart sector circleMode time matter =
      matter := by
  have hSpan :
      matter ∈
        geometricHopfFrameSpan
          (localHopfFrameSeed
            period hPeriod point chart sector circleMode time)
          (localHopfFrameTangent
            period hPeriod point chart sector circleMode time) := by
    rw [localHopfFrameSpan_eq_sector
      period hPeriod point chart hChart sector circleMode time]
    exact hMatter
  refine Submodule.span_induction
    (p := fun matter _ =>
      localHopfFrameReconstruction
          period hPeriod point chart sector circleMode time matter =
        matter)
    ?_ ?_ ?_ ?_ hSpan
  · rintro generator (rfl | ⟨coordinate, rfl⟩)
    · exact localHopfFrameReconstruction_seed
        period hPeriod point chart hChart sector circleMode time
    · exact localHopfFrameReconstruction_tangent
        period hPeriod point chart hChart sector circleMode time coordinate
  · exact map_zero _
  · intro first second _ _ hFirst hSecond
    rw [map_add, hFirst, hSecond]
  · intro scalar matter _ hMatter
    rw [map_smul, hMatter]

theorem localHopfFrameReconstruction_eq_zero_of_other_sector
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (frameSector matterSector : NormalRootChoice)
    (hSectors : frameSector ≠ matterSector)
    (circleMode : Int) (time : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter : PrimitiveSpinCGeometricSectorPlane matterSector matter) :
    localHopfFrameReconstruction
        period hPeriod point chart frameSector circleMode time matter =
      0 := by
  have hSeedSector :
      PrimitiveSpinCGeometricSectorPlane frameSector
        (localHopfFrameSeed
          period hPeriod point chart frameSector circleMode time) :=
    primitiveSpinCHopfZeroModeLocalCoordinate_sectorPlane
      period hPeriod point chart hChart frameSector circleMode time
  have hTangentSector (coordinate : Fin 3) :
      PrimitiveSpinCGeometricSectorPlane frameSector
        (localHopfFrameTangent
          period hPeriod point chart frameSector circleMode time coordinate) :=
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_sectorPlane
      period hPeriod point chart hChart coordinate frameSector circleMode time
  have hSeedPairing :
      d9DoubledMatterSpinorHermitianPairing
          (localHopfFrameSeed
            period hPeriod point chart frameSector circleMode time)
          matter = 0 :=
    d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero_of_ne
      frameSector matterSector hSectors _ _ hSeedSector hMatter
  have hTangentPairing (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (localHopfFrameTangent
            period hPeriod point chart frameSector circleMode time coordinate)
          matter = 0 :=
    d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero_of_ne
      frameSector matterSector hSectors _ _
        (hTangentSector coordinate) hMatter
  rw [localHopfFrameReconstruction_apply, hSeedPairing]
  simp_rw [hTangentPairing]
  simp

def localSignedHopfFrameReconstruction
    (point : MonopoleSphere) (chart : MonopoleChart)
    (positiveCircleMode negativeCircleMode : Int) (time : Real) :
    D9DoubledMatterFiber →ₗ[Complex] D9DoubledMatterFiber :=
  localHopfFrameReconstruction
      period hPeriod point chart .positiveQuarter positiveCircleMode time +
    localHopfFrameReconstruction
      period hPeriod point chart .negativeQuarter negativeCircleMode time

theorem localSignedHopfFrameReconstruction_eq_id
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (positiveCircleMode negativeCircleMode : Int) (time : Real) :
    localSignedHopfFrameReconstruction
        period hPeriod point chart positiveCircleMode negativeCircleMode time =
      LinearMap.id := by
  apply LinearMap.ext
  intro matter
  have hTop :
      matter ∈
        geometricSectorSubmodule .positiveQuarter ⊔
          geometricSectorSubmodule .negativeQuarter := by
    rw [geometricSectorSubmodules_sup_eq_top]
    trivial
  obtain ⟨positive, hPositive, negative, hNegative, rfl⟩ :=
    Submodule.mem_sup.mp hTop
  simp only [localSignedHopfFrameReconstruction, LinearMap.add_apply,
    LinearMap.id_apply, map_add]
  rw [
    localHopfFrameReconstruction_eq_self_of_sector
      period hPeriod point chart hChart .positiveQuarter
        positiveCircleMode time positive hPositive,
    localHopfFrameReconstruction_eq_zero_of_other_sector
      period hPeriod point chart hChart .positiveQuarter .negativeQuarter
        (by decide) positiveCircleMode time negative hNegative,
    localHopfFrameReconstruction_eq_zero_of_other_sector
      period hPeriod point chart hChart .negativeQuarter .positiveQuarter
        (by decide) negativeCircleMode time positive hPositive,
    localHopfFrameReconstruction_eq_self_of_sector
      period hPeriod point chart hChart .negativeQuarter
        negativeCircleMode time negative hNegative]
  abel

end
end P0EFTJanusProgramPD9PrimitiveSpinCMonopoleFiniteFrame4D
end JanusFormal
