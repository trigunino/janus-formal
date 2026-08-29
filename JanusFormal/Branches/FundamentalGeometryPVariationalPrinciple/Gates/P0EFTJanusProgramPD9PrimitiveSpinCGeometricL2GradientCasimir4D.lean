import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D

/-!
# Gradient Casimir identity in the primitive SpinC geometric L² core

This file identifies the geometric pairing of the Clifford-gradient packet
with the scalar round-sphere Dirichlet pairing.  It is the remaining analytic
input needed to make the two first-order signs orthogonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped BigOperators Matrix Manifold ContDiff
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)
private abbrev SphereMeasure : Measure MonopoleSphere :=
  (volume : Measure EuclideanR3).toSphere

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) :=
  borel _

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

theorem d9DoubledMatterFiberCliffordGamma_zero_one
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 0
        (d9DoubledMatterFiberCliffordGamma 1 matter) =
      d9DoubledMatterFiberCliffordGamma 2 matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  apply Prod.ext <;> funext index <;> fin_cases index <;> simp

theorem d9DoubledMatterFiberCliffordGamma_one_two
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 1
        (d9DoubledMatterFiberCliffordGamma 2 matter) =
      d9DoubledMatterFiberCliffordGamma 0 matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  apply Prod.ext <;> funext index <;> fin_cases index <;> simp

theorem d9DoubledMatterFiberCliffordGamma_two_zero
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 2
        (d9DoubledMatterFiberCliffordGamma 0 matter) =
      d9DoubledMatterFiberCliffordGamma 1 matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  apply Prod.ext <;> funext index <;> fin_cases index <;> simp

theorem d9DoubledMatterFiberCliffordGamma_one_zero
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 1
        (d9DoubledMatterFiberCliffordGamma 0 matter) =
      -d9DoubledMatterFiberCliffordGamma 2 matter := by
  rw [d9DoubledMatterFiberCliffordGamma_anticommute 1 0 (by decide),
    d9DoubledMatterFiberCliffordGamma_zero_one]

theorem d9DoubledMatterFiberCliffordGamma_two_one
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 2
        (d9DoubledMatterFiberCliffordGamma 1 matter) =
      -d9DoubledMatterFiberCliffordGamma 0 matter := by
  rw [d9DoubledMatterFiberCliffordGamma_anticommute 2 1 (by decide),
    d9DoubledMatterFiberCliffordGamma_one_two]

theorem d9DoubledMatterFiberCliffordGamma_zero_two
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma 0
        (d9DoubledMatterFiberCliffordGamma 2 matter) =
      -d9DoubledMatterFiberCliffordGamma 1 matter := by
  rw [d9DoubledMatterFiberCliffordGamma_anticommute 0 2 (by decide),
    d9DoubledMatterFiberCliffordGamma_two_zero]

private def primitiveSpinCZeroModeGammaPairingMatrix
    (base : ThroatBase period hPeriod) : Fin 3 → Fin 3 → Complex :=
  let n : Fin 3 → Real :=
    fun coordinate =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod coordinate base
  fun first second =>
    if first = 0 then
      if second = 0 then 1
      else if second = 1 then -Complex.I * n 2
      else Complex.I * n 1
    else if first = 1 then
      if second = 0 then Complex.I * n 2
      else if second = 1 then 1
      else -Complex.I * n 0
    else
      if second = 0 then -Complex.I * n 1
      else if second = 1 then Complex.I * n 0
      else 1

def primitiveSpinCZeroModeTangentialPairingMatrix
    (base : ThroatBase period hPeriod) : Fin 3 → Fin 3 → Complex :=
  let n : Fin 3 → Real :=
    fun coordinate =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod coordinate base
  fun first second =>
    if first = 0 then
      if second = 0 then 1 - n 0 * n 0
      else if second = 1 then -n 0 * n 1 - Complex.I * n 2
      else -n 0 * n 2 + Complex.I * n 1
    else if first = 1 then
      if second = 0 then -n 1 * n 0 + Complex.I * n 2
      else if second = 1 then 1 - n 1 * n 1
      else -n 1 * n 2 - Complex.I * n 0
    else
      if second = 0 then -n 2 * n 0 - Complex.I * n 1
      else if second = 1 then -n 2 * n 1 + Complex.I * n 0
      else 1 - n 2 * n 2

/-- A Hopf zero mode is orthogonal to each of its three tangential
Clifford partners in one fiber. -/
theorem primitiveSpinCHopfZeroMode_tangential_pointwise_orthogonal
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base) =
      0 := by
  exact
    d9DoubledMatterSpinorHermitianPairing_radial_eigen_anti_eigen
      period hPeriod base _ _
      (primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base)
      (primitiveSpinCHopfFirstSphereTangential_baseUnitRadial_anti_eigen
        period hPeriod coordinate sector circleMode base)

/-- The zero-mode expectation of one Clifford generator is its radial
coordinate times `i`. -/
theorem primitiveSpinCHopfZeroMode_cliffordGamma_expectation
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base)
        (d9DoubledMatterFiberCliffordGamma coordinate
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)) =
      (d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod coordinate base : Complex) *
        Complex.I *
        d9DoubledMatterSpinorHermitianPairing
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base) := by
  let matter :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let radial :=
    d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod coordinate base
  have hOrthogonal :=
    primitiveSpinCHopfZeroMode_tangential_pointwise_orthogonal
      period hPeriod coordinate sector circleMode base
  rw [primitiveSpinCHopfFirstSphereTangentialSection_apply] at hOrthogonal
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt at hOrthogonal
  have hImaginary :
      d9PrimitiveSpinCImaginaryAction matter =
        d9PrimitiveSpinCComplexActionCLM Complex.I matter := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  change
    d9DoubledMatterSpinorHermitianPairing matter
        (d9DoubledMatterFiberCliffordGamma coordinate matter) =
      (radial : Complex) * Complex.I *
        d9DoubledMatterSpinorHermitianPairing matter matter
  change
    d9DoubledMatterSpinorHermitianPairing matter
        (d9DoubledMatterFiberCliffordGamma coordinate matter -
          radial • d9PrimitiveSpinCImaginaryAction matter) = 0
    at hOrthogonal
  rw [show
      d9DoubledMatterFiberCliffordGamma coordinate matter -
          radial • d9PrimitiveSpinCImaginaryAction matter =
        d9DoubledMatterFiberCliffordGamma coordinate matter +
          (-radial) • d9PrimitiveSpinCImaginaryAction matter by module,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right,
    hImaginary,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right]
    at hOrthogonal
  push_cast at hOrthogonal
  linear_combination hOrthogonal

/-- Pairing of two Clifford generators on a Hopf zero mode. -/
theorem primitiveSpinCHopfZeroMode_cliffordGamma_pairing
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma first
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base))
        (d9DoubledMatterFiberCliffordGamma second
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)) =
      primitiveSpinCZeroModeGammaPairingMatrix
          period hPeriod base first second *
        d9DoubledMatterSpinorHermitianPairing
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base) := by
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  change
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma first matter)
        (d9DoubledMatterFiberCliffordGamma second matter) =
      primitiveSpinCZeroModeGammaPairingMatrix
          period hPeriod base first second *
        d9DoubledMatterSpinorHermitianPairing matter matter
  have hExpectation (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing matter
          (d9DoubledMatterFiberCliffordGamma coordinate matter) =
        (d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base : Complex) *
          Complex.I *
          d9DoubledMatterSpinorHermitianPairing matter matter :=
    primitiveSpinCHopfZeroMode_cliffordGamma_expectation
      period hPeriod coordinate sector circleMode base
  have hCases (coordinate : Fin 3) :
      coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 := by
    fin_cases coordinate <;> simp
  rcases hCases first with rfl | rfl | rfl <;>
    rcases hCases second with rfl | rfl | rfl <;>
    rw [d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew] <;>
    simp [d9DoubledMatterFiberCliffordGamma_sq,
      d9DoubledMatterFiberCliffordGamma_zero_one,
      d9DoubledMatterFiberCliffordGamma_one_two,
      d9DoubledMatterFiberCliffordGamma_two_zero,
      d9DoubledMatterFiberCliffordGamma_one_zero,
      d9DoubledMatterFiberCliffordGamma_two_one,
      d9DoubledMatterFiberCliffordGamma_zero_two,
      d9DoubledMatterSpinorHermitianPairing_neg_right,
      primitiveSpinCZeroModeGammaPairingMatrix] <;>
    try rw [hExpectation] <;>
    ring

/-- The three tangential Clifford partners carry the standard chiral
tangent Hermitian form. -/
theorem primitiveSpinCHopfZeroMode_tangential_pairing
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod first sector circleMode base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod second sector circleMode base) =
      primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod base first second *
        d9DoubledMatterSpinorHermitianPairing
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base) := by
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let n : Fin 3 → Real := fun coordinate =>
    d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod coordinate base
  change
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod first sector circleMode base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod second sector circleMode base) =
      primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod base first second *
        d9DoubledMatterSpinorHermitianPairing matter matter
  have hGammaPair (first second : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing
          (d9DoubledMatterFiberCliffordGamma first matter)
          (d9DoubledMatterFiberCliffordGamma second matter) =
        primitiveSpinCZeroModeGammaPairingMatrix
            period hPeriod base first second *
          d9DoubledMatterSpinorHermitianPairing matter matter :=
    primitiveSpinCHopfZeroMode_cliffordGamma_pairing
      period hPeriod first second sector circleMode base
  have hExpectation (coordinate : Fin 3) :
      d9DoubledMatterSpinorHermitianPairing matter
          (d9DoubledMatterFiberCliffordGamma coordinate matter) =
        (d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base : Complex) *
          Complex.I *
          d9DoubledMatterSpinorHermitianPairing matter matter :=
    primitiveSpinCHopfZeroMode_cliffordGamma_expectation
      period hPeriod coordinate sector circleMode base
  have hGammaLeft := fun coordinate =>
    d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew
      (left := matter) (right := matter) coordinate
  have hImaginary :
      d9PrimitiveSpinCImaginaryAction matter =
        d9PrimitiveSpinCComplexActionCLM Complex.I matter := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  have hTangential (coordinate : Fin 3) :
      d9DoubledMatterFiberCliffordGamma coordinate matter -
          n coordinate • d9PrimitiveSpinCImaginaryAction matter =
        d9DoubledMatterFiberCliffordGamma coordinate matter +
          d9PrimitiveSpinCComplexActionCLM
            (-((n coordinate : Real) : Complex) * Complex.I) matter := by
    have hCoefficient :
        d9PrimitiveSpinCComplexActionCLM
            (-((n coordinate : Real) : Complex) * Complex.I) matter =
          (-n coordinate) • d9PrimitiveSpinCImaginaryAction matter := by
      rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
      simp
    rw [hCoefficient]
    module
  rw [primitiveSpinCHopfFirstSphereTangentialSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  change
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma first matter -
          n first • d9PrimitiveSpinCImaginaryAction matter)
        (d9DoubledMatterFiberCliffordGamma second matter -
          n second • d9PrimitiveSpinCImaginaryAction matter) =
      _
  rw [hTangential first, hTangential second]
  simp_rw [d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right]
  rw [hGammaPair first second, hGammaLeft first,
    hExpectation first, hExpectation second]
  have hCases (coordinate : Fin 3) :
      coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 := by
    fin_cases coordinate <;> simp
  have hISq : Complex.I ^ 2 = -1 := by
    rw [pow_two, Complex.I_mul_I]
  rcases hCases first with rfl | rfl | rfl <;>
    rcases hCases second with rfl | rfl | rfl <;>
    simp [primitiveSpinCZeroModeGammaPairingMatrix,
      primitiveSpinCZeroModeTangentialPairingMatrix, n] <;>
    ring_nf <;>
    rw [hISq] <;>
    ring

/-- Direct evaluation of null multiplication at the moving quotient
witness. -/
theorem primitiveSpinCNullMultiplication_apply_movingWitness
    (point : MonopoleSphere) (time : Real) (parameter : Complex)
    (state : SmoothSection period hPeriod) :
    (show D9DoubledMatterFiber from
      primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point)
        (show D9DoubledMatterFiber from
          state
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) := by
  rw [primitiveSpinCNullMultiplicationLinearMap_apply]
  change
    (∑ coordinate : Fin 3,
      (show D9DoubledMatterFiber from
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter
          (primitiveSpinCSolidNullVector parameter coordinate)
          (primitiveSpinCCoordinateMultiplicationLinearMap
            period hPeriod coordinate state)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))) = _
  simp_rw [d9PrimitiveSpinCComplexScalarSection_apply_complexAction,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  change
    (∑ coordinate : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCSolidNullVector parameter coordinate)
        (monopoleSphereCoordinate point coordinate •
          (show D9DoubledMatterFiber from
            state
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time)))) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point)
        (show D9DoubledMatterFiber from
          state
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time))
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [map_sum,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp_rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_smul]
  unfold primitiveSpinCNullSphereScalar
  simp_rw [← Complex.coe_smul, smul_smul]
  rw [← Finset.sum_smul]

/-- Pointwise factorization of every scalar null-power section. -/
theorem primitiveSpinCNullPowerSection_apply_movingWitness
    (point : MonopoleSphere) (time : Real) (parameter : Complex)
    (sector : NormalRootChoice) (circleMode : Int) (degree : Nat) :
    (show D9DoubledMatterFiber from
      primitiveSpinCNullPowerSection
          period hPeriod parameter sector circleMode degree
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point ^ degree)
        (show D9DoubledMatterFiber from
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) := by
  induction degree with
  | zero =>
      rw [primitiveSpinCNullPowerSection_zero]
      simp
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullPowerSection_succ,
        primitiveSpinCNullMultiplication_apply_movingWitness,
        inductionHypothesis, ← d9PrimitiveSpinCComplexAction_mul]
      congr 1
      simp [pow_succ, mul_comm]

/-- The null gradient of the Hopf seed is the complex linear combination
of the three installed tangential partners. -/
theorem primitiveSpinCNullGradient_zeroMode_apply
    (point : MonopoleSphere) (time : Real) (parameter : Complex)
    (sector : NormalRootChoice) (circleMode : Int) :
    (show D9DoubledMatterFiber from
      primitiveSpinCNullGradientLinearMap
          period hPeriod parameter
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      ∑ coordinate : Fin 3,
        d9PrimitiveSpinCComplexActionCLM
          (primitiveSpinCSolidNullVector parameter coordinate)
          (show D9DoubledMatterFiber from
            primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time)) := by
  rw [primitiveSpinCNullGradientLinearMap_apply]
  change
    (∑ coordinate : Fin 3,
      (show D9DoubledMatterFiber from
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter
          (primitiveSpinCSolidNullVector parameter coordinate)
          (primitiveSpinCCoordinateGradientLinearMap
            period hPeriod coordinate
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode))
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))) = _
  simp_rw [primitiveSpinCCoordinateGradient_zeroMode,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]

/-- Pointwise factorization of the auxiliary gradient-power sequence. -/
theorem primitiveSpinCNullGradientPowerSection_apply_movingWitness
    (point : MonopoleSphere) (time : Real) (parameter : Complex)
    (sector : NormalRootChoice) (circleMode : Int) (degree : Nat) :
    (show D9DoubledMatterFiber from
      primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point ^ degree)
        (∑ coordinate : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
            (primitiveSpinCSolidNullVector parameter coordinate)
            (show D9DoubledMatterFiber from
              primitiveSpinCHopfFirstSphereTangentialSection
                period hPeriod coordinate sector circleMode
                (primitiveSpinCNullPacketMovingWitnessBase
                  period hPeriod point time))) := by
  induction degree with
  | zero =>
      rw [primitiveSpinCNullGradientPowerSection_zero,
        primitiveSpinCNullGradient_zeroMode_apply]
      simp
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullGradientPowerSection_succ,
        primitiveSpinCNullMultiplication_apply_movingWitness,
        inductionHypothesis, ← d9PrimitiveSpinCComplexAction_mul]
      congr 1
      simp [pow_succ, mul_comm]

/-- Ambient coefficient of the Clifford gradient of a scalar null power. -/
def primitiveSpinCNullSpherePowerAmbientDerivative
    (degree : Nat) (parameter : Complex) (coordinate : Fin 3)
    (point : MonopoleSphere) : Complex :=
  (degree : Complex) *
    primitiveSpinCSolidNullVector parameter coordinate *
    primitiveSpinCNullSpherePower (degree - 1) parameter point

/-- Rotation derivative of one ambient-gradient coefficient along the
matching rotation generator. -/
def primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
    (degree : Nat) (parameter : Complex) (coordinate : Fin 3)
    (point : MonopoleSphere) : Complex :=
  (degree : Complex) *
    primitiveSpinCSolidNullVector parameter coordinate *
    primitiveSpinCNullSpherePowerAngularDerivative
      coordinate (degree - 1) parameter point

/-- The ambient gradient of one null power has zero rotational
divergence. -/
theorem primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_sum
    (degree : Nat) (parameter : Complex) (point : MonopoleSphere) :
    ∑ coordinate : Fin 3,
        primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
          degree parameter coordinate point =
      0 := by
  simp [primitiveSpinCNullSpherePowerAmbientDivergenceDerivative,
    primitiveSpinCNullSpherePowerAngularDerivative,
    primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullLinearFunctional_apply,
    canonicalRotationVelocity, Fin.sum_univ_three]
  ring

/-- Integration by parts for one ambient-gradient coefficient and the
matching rotation derivative. -/
theorem primitiveSpinCNullSpherePowerAmbientDerivative_angular_ipp
    (coordinate : Fin 3) (degree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star
            (primitiveSpinCNullSpherePowerAmbientDerivative
              degree firstParameter coordinate point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            coordinate degree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star
            (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
              degree firstParameter coordinate point) *
          primitiveSpinCNullSpherePower
            degree secondParameter point
        ∂SphereMeasure := by
  let coefficient : Complex :=
    (degree : Complex) *
      primitiveSpinCSolidNullVector firstParameter coordinate
  have hIPP :
      (∫ point,
          star
              (primitiveSpinCNullSpherePower
                (degree - 1) firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate degree secondParameter point
          ∂SphereMeasure) =
        -∫ point,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                coordinate (degree - 1) firstParameter point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
          ∂SphereMeasure := by
    simpa only [] using
      primitiveSpinCNullSpherePower_angular_ipp
        coordinate (degree - 1) degree firstParameter secondParameter
  change
    (∫ point,
        star
            (coefficient *
              primitiveSpinCNullSpherePower
                (degree - 1) firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            coordinate degree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star
            (coefficient *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate (degree - 1) firstParameter point) *
          primitiveSpinCNullSpherePower
            degree secondParameter point
        ∂SphereMeasure
  have hLeftFactor :
      (∫ point,
          star
              (coefficient *
                primitiveSpinCNullSpherePower
                  (degree - 1) firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate degree secondParameter point
          ∂SphereMeasure) =
        star coefficient *
          ∫ point,
            star
                (primitiveSpinCNullSpherePower
                  (degree - 1) firstParameter point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate degree secondParameter point
            ∂SphereMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with point
    simp only [Complex.star_def, map_mul]
    ring
  have hRightFactor :
      (∫ point,
          star
              (coefficient *
                primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (degree - 1) firstParameter point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
          ∂SphereMeasure) =
        star coefficient *
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (degree - 1) firstParameter point) *
              primitiveSpinCNullSpherePower
                degree secondParameter point
            ∂SphereMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with point
    simp only [Complex.star_def, map_mul]
    ring
  rw [hLeftFactor, hRightFactor, hIPP]
  ring

/-- Ambient null-power coefficients are continuous on the sphere. -/
theorem primitiveSpinCNullSpherePowerAmbientDerivative_continuous
    (degree : Nat) (parameter : Complex) (coordinate : Fin 3) :
    Continuous
      (primitiveSpinCNullSpherePowerAmbientDerivative
        degree parameter coordinate) := by
  change Continuous (fun point =>
    (degree : Complex) *
      primitiveSpinCSolidNullVector parameter coordinate *
      primitiveSpinCNullSpherePower (degree - 1) parameter point)
  exact continuous_const.mul
    (primitiveSpinCNullSpherePower_continuous
      (degree - 1) parameter)

/-- Rotational divergences of ambient null-power coefficients are
continuous on the sphere. -/
theorem primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_continuous
    (degree : Nat) (parameter : Complex) (coordinate : Fin 3) :
    Continuous
      (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
        degree parameter coordinate) := by
  change Continuous (fun point =>
    (degree : Complex) *
      primitiveSpinCSolidNullVector parameter coordinate *
      primitiveSpinCNullSpherePowerAngularDerivative
        coordinate (degree - 1) parameter point)
  exact continuous_const.mul
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      coordinate (degree - 1) parameter)

/-- The mixed ambient/angular contribution integrates to zero. -/
theorem primitiveSpinCNullSpherePowerAmbientDerivative_angular_sum_zero
    (degree : Nat) (firstParameter secondParameter : Complex) :
    (∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate degree secondParameter point
        ∂SphereMeasure) = 0 := by
  have hLeftIntegrable (coordinate : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate degree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAmbientDerivative_continuous
      degree firstParameter coordinate).star.mul
        (primitiveSpinCNullSpherePowerAngularDerivative_continuous
          coordinate degree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRightIntegrable (coordinate : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_continuous
      degree firstParameter coordinate).star.mul
        (primitiveSpinCNullSpherePower_continuous
          degree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRightPointwise :
      (fun point =>
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
              degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point) = 0 := by
    funext point
    change
      (∑ coordinate : Fin 3,
        (starRingEnd Complex)
            (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
              degree firstParameter coordinate point) *
          primitiveSpinCNullSpherePower
            degree secondParameter point) = (0 : Complex)
    rw [← Finset.sum_mul, ← map_sum,
      primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_sum]
    simp
  calc
    (∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate degree secondParameter point
        ∂SphereMeasure) =
        ∑ coordinate : Fin 3,
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAmbientDerivative
                  degree firstParameter coordinate point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate degree secondParameter point
            ∂SphereMeasure := by
      rw [integral_finsetSum]
      intro coordinate _
      exact hLeftIntegrable coordinate
    _ = ∑ coordinate : Fin 3,
        -∫ point,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
          ∂SphereMeasure := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact primitiveSpinCNullSpherePowerAmbientDerivative_angular_ipp
        coordinate degree firstParameter secondParameter
    _ = -(∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                degree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
        ∂SphereMeasure) := by
      rw [integral_finsetSum]
      · simp
      · intro coordinate _
        exact hRightIntegrable coordinate
    _ = 0 := by
      rw [hRightPointwise]
      simp

/-- One angular derivative transfers to the second factor with the
expected skew-Hermitian sign. -/
theorem primitiveSpinCNullSpherePower_angular_energy_ipp
    (axis : Fin 3) (degree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star
            (primitiveSpinCNullSpherePowerAngularDerivative
              axis degree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            axis degree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star
            (primitiveSpinCNullSpherePower
              degree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularSecondDerivative
            axis degree secondParameter point
        ∂SphereMeasure := by
  have hIPP := sphere_integral_star_mul_derivative_eq_neg axis
    (primitiveSpinCNullSpherePower degree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis degree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis degree firstParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis degree secondParameter)
    (primitiveSpinCNullSpherePower_continuous
      degree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis degree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis degree firstParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
      axis degree secondParameter)
    (fun angle point =>
      primitiveSpinCNullSpherePower_rotation_hasDerivAt
        axis degree firstParameter point angle)
    (fun angle point =>
      primitiveSpinCNullSpherePowerAngularDerivative_rotation_hasDerivAt
        axis degree secondParameter point angle)
  linear_combination hIPP

/-- The Dirichlet pairing of degree-`degree` null powers is their
positive rotation-Casimir eigenvalue times the scalar pairing. -/
theorem primitiveSpinCNullSpherePower_angular_energy_eq_casimir
    (degree : Nat) (firstParameter secondParameter : Complex) :
    (∫ point,
        ∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis degree secondParameter point
        ∂SphereMeasure) =
      ((degree : Complex) * (degree + 1 : Nat)) *
        ∫ point,
          star
              (primitiveSpinCNullSpherePower
                degree firstParameter point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
          ∂SphereMeasure := by
  have hEnergyIntegrable (axis : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis degree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis degree firstParameter).star.mul
        (primitiveSpinCNullSpherePowerAngularDerivative_continuous
          axis degree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hSecondIntegrable (axis : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePower
                degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis degree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePower_continuous
      degree firstParameter).star.mul
        (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
          axis degree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hCasimirPointwise :
      (fun point =>
        star
            (primitiveSpinCNullSpherePower
              degree firstParameter point) *
          primitiveSpinCNullSpherePowerRotationCasimir
            degree secondParameter point) =
        fun point =>
          -(∑ axis : Fin 3,
            star
                (primitiveSpinCNullSpherePower
                  degree firstParameter point) *
              primitiveSpinCNullSpherePowerAngularSecondDerivative
                axis degree secondParameter point) := by
    funext point
    simp [primitiveSpinCNullSpherePowerRotationCasimir,
      Finset.mul_sum]
  calc
    (∫ point,
        ∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis degree secondParameter point
        ∂SphereMeasure) =
        ∑ axis : Fin 3,
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAngularDerivative
                  axis degree firstParameter point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                axis degree secondParameter point
            ∂SphereMeasure := by
      rw [integral_finsetSum]
      intro axis _
      exact hEnergyIntegrable axis
    _ = ∑ axis : Fin 3,
        -∫ point,
          star
              (primitiveSpinCNullSpherePower
                degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis degree secondParameter point
          ∂SphereMeasure := by
      apply Finset.sum_congr rfl
      intro axis _
      exact primitiveSpinCNullSpherePower_angular_energy_ipp
        axis degree firstParameter secondParameter
    _ = -(∫ point,
        ∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePower
                degree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis degree secondParameter point
        ∂SphereMeasure) := by
      rw [integral_finsetSum]
      · simp
      · intro axis _
        exact hSecondIntegrable axis
    _ = ∫ point,
        star
            (primitiveSpinCNullSpherePower
              degree firstParameter point) *
          primitiveSpinCNullSpherePowerRotationCasimir
            degree secondParameter point
        ∂SphereMeasure := by
      rw [hCasimirPointwise, integral_neg]
    _ = ((degree : Complex) * (degree + 1 : Nat)) *
        ∫ point,
          star
              (primitiveSpinCNullSpherePower
                degree firstParameter point) *
            primitiveSpinCNullSpherePower
              degree secondParameter point
          ∂SphereMeasure := by
      simp_rw [primitiveSpinCNullSpherePowerRotationCasimir_eq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with point
      ring

/-- The reconstructed all-level gradient evaluates to the ambient
derivatives multiplying the three tangential Hopf partners. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    (show D9DoubledMatterFiber from
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)) =
      ∑ coordinate : Fin 3,
        d9PrimitiveSpinCComplexActionCLM
          (primitiveSpinCNullSpherePowerAmbientDerivative
            (positiveLevel + 1)
            (primitiveSpinCNullGeometricParameter
              positiveLevel multiplicity)
            coordinate point)
          (show D9DoubledMatterFiber from
            primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time)) := by
  rw [show
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.gradientSection) =
        (primitiveSpinCAllLevelNullHarmonicSquaredSeed
          period hPeriod positiveLevel multiplicity sector circleMode
          |>.gradientSection) by rfl,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed_gradientSection]
  change
    ((positiveLevel + 1 : Nat) : Real) •
        (show D9DoubledMatterFiber from
          primitiveSpinCNullGradientPowerSection
              period hPeriod
              (primitiveSpinCNullGeometricParameter
                positiveLevel multiplicity)
              sector circleMode positiveLevel
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time)) =
      _
  rw [primitiveSpinCNullGradientPowerSection_apply_movingWitness]
  let scalar :=
    primitiveSpinCNullSphereScalar
      (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
      point
  have hRealAction (matter : D9DoubledMatterFiber) :
      ((positiveLevel + 1 : Nat) : Real) • matter =
        d9PrimitiveSpinCComplexActionCLM
          (((positiveLevel + 1 : Nat) : Real) : Complex) matter := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  rw [hRealAction, ← d9PrimitiveSpinCComplexAction_mul, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [← d9PrimitiveSpinCComplexAction_mul]
  congr 1
  simp [primitiveSpinCNullSpherePowerAmbientDerivative,
    primitiveSpinCNullSpherePower]
  ring

/-- Pairing of two arbitrary complex tangential combinations. -/
theorem primitiveSpinCHopfTangentialCombination_pairing
    (firstCoefficient secondCoefficient : Fin 3 → Complex)
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (∑ coordinate : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
            (firstCoefficient coordinate)
            (show D9DoubledMatterFiber from
              primitiveSpinCHopfFirstSphereTangentialSection
                period hPeriod coordinate sector circleMode base))
        (∑ coordinate : Fin 3,
          d9PrimitiveSpinCComplexActionCLM
            (secondCoefficient coordinate)
            (show D9DoubledMatterFiber from
              primitiveSpinCHopfFirstSphereTangentialSection
                period hPeriod coordinate sector circleMode base)) =
      (∑ first : Fin 3, ∑ second : Fin 3,
        star (firstCoefficient first) *
          secondCoefficient second *
          primitiveSpinCZeroModeTangentialPairingMatrix
            period hPeriod base first second) *
        d9DoubledMatterSpinorHermitianPairing
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base) := by
  simp only [Fin.sum_univ_three,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroMode_tangential_pairing,
    starRingEnd_apply]
  ring

/-- The chiral tangent matrix splits into the ordinary spherical
Dirichlet contraction and one Hamiltonian divergence term. -/
theorem primitiveSpinCNullSpherePower_tangentialMatrix_contraction
    (degree : Nat) (firstParameter secondParameter : Complex)
    (point : MonopoleSphere) (time : Real) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAmbientDerivative
            degree firstParameter first point) *
        primitiveSpinCNullSpherePowerAmbientDerivative
            degree secondParameter second point *
        primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second) =
      (∑ axis : Fin 3,
        star
            (primitiveSpinCNullSpherePowerAngularDerivative
              axis degree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            axis degree secondParameter point) +
        Complex.I *
          (∑ coordinate : Fin 3,
            star
                (primitiveSpinCNullSpherePowerAmbientDerivative
                  degree firstParameter coordinate point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate degree secondParameter point) := by
  simp [Fin.sum_univ_three,
    primitiveSpinCZeroModeTangentialPairingMatrix,
    d9PrimitiveSpinCBaseUnitRadialCoordinate,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate,
    primitiveSpinCNullSpherePowerAmbientDerivative,
    primitiveSpinCNullSpherePower,
    primitiveSpinCNullSpherePowerAngularDerivative,
    primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullLinearFunctional_apply,
    canonicalRotationVelocity, monopoleSphereCoordinate]
  have hSphere :
      (monopoleSphereCoordinate point 0 : Complex) ^ 2 +
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 +
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 = 1 := by
    exact_mod_cast monopoleSphereCoordinate_sq_sum point
  simp [monopoleSphereCoordinate] at hSphere
  linear_combination
    (-((degree : Complex) ^ 2 *
        (starRingEnd Complex)
            (primitiveSpinCNullSphereScalar firstParameter point) ^
          (degree - 1) *
        primitiveSpinCNullSphereScalar secondParameter point ^
          (degree - 1) *
        ((starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 0) *
            primitiveSpinCSolidNullVector secondParameter 0 +
          (starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 1) *
            primitiveSpinCSolidNullVector secondParameter 1 +
          (starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 2) *
            primitiveSpinCSolidNullVector secondParameter 2))) * hSphere

/-- The chiral tangential contraction is valid between arbitrary null
degrees. -/
theorem primitiveSpinCNullSpherePower_tangentialMatrix_contraction_cross
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex)
    (point : MonopoleSphere) (time : Real) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAmbientDerivative
            firstDegree firstParameter first point) *
        primitiveSpinCNullSpherePowerAmbientDerivative
            secondDegree secondParameter second point *
        primitiveSpinCZeroModeTangentialPairingMatrix
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          first second) =
      (∑ axis : Fin 3,
        star
            (primitiveSpinCNullSpherePowerAngularDerivative
              axis firstDegree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            axis secondDegree secondParameter point) +
        Complex.I *
          (∑ coordinate : Fin 3,
            star
                (primitiveSpinCNullSpherePowerAmbientDerivative
                  firstDegree firstParameter coordinate point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate secondDegree secondParameter point) := by
  simp [Fin.sum_univ_three,
    primitiveSpinCZeroModeTangentialPairingMatrix,
    d9PrimitiveSpinCBaseUnitRadialCoordinate,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate,
    primitiveSpinCNullSpherePowerAmbientDerivative,
    primitiveSpinCNullSpherePower,
    primitiveSpinCNullSpherePowerAngularDerivative,
    primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullLinearFunctional_apply,
    canonicalRotationVelocity, monopoleSphereCoordinate]
  have hSphere :
      (monopoleSphereCoordinate point 0 : Complex) ^ 2 +
          (monopoleSphereCoordinate point 1 : Complex) ^ 2 +
      (monopoleSphereCoordinate point 2 : Complex) ^ 2 = 1 := by
    exact_mod_cast monopoleSphereCoordinate_sq_sum point
  simp [monopoleSphereCoordinate] at hSphere
  linear_combination
    (-((firstDegree : Complex) * (secondDegree : Complex) *
        (starRingEnd Complex)
            (primitiveSpinCNullSphereScalar firstParameter point) ^
          (firstDegree - 1) *
        primitiveSpinCNullSphereScalar secondParameter point ^
          (secondDegree - 1) *
        ((starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 0) *
            primitiveSpinCSolidNullVector secondParameter 0 +
          (starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 1) *
            primitiveSpinCSolidNullVector secondParameter 1 +
          (starRingEnd Complex)
              (primitiveSpinCSolidNullVector firstParameter 2) *
            primitiveSpinCSolidNullVector secondParameter 2))) * hSphere

/-- The Hopf seed has constant intrinsic pointwise squared norm eight. -/
theorem primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      8 := by
  change
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) = 8
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  rw [d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart sector circleMode time,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroModeLocalCoordinate_self_eq_eight
      period hPeriod point chart hChart sector circleMode]
  have hPhase :
      (starRingEnd Complex)
          (normalRootSpinFrameExponential
            period sector circleMode time) *
        normalRootSpinFrameExponential
            period sector circleMode time = 1 := by
    simpa using
      normalRootSpinFrameExponential_conj_mul
        period sector circleMode circleMode time
  rw [← mul_assoc, hPhase]
  simp

/-- Pointwise scalar-seed pairing in one positive-level block. -/
theorem primitiveSpinCAllLevelNullHarmonicScalar_pointwise_pairing
    (positiveLevel : Nat)
    (firstMultiplicity secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel firstMultiplicity sector circleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel secondMultiplicity sector circleMode
          |>.scalarSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      8 *
        star
            (primitiveSpinCNullSpherePower
              (positiveLevel + 1)
              (primitiveSpinCNullGeometricParameter
                positiveLevel firstMultiplicity) point) *
          primitiveSpinCNullSpherePower
            (positiveLevel + 1)
            (primitiveSpinCNullGeometricParameter
              positiveLevel secondMultiplicity) point := by
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  change
    d9DoubledMatterSpinorHermitianPairing
        (show D9DoubledMatterFiber from
          primitiveSpinCNullPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter
              positiveLevel firstMultiplicity)
            sector circleMode (positiveLevel + 1)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time))
        (show D9DoubledMatterFiber from
          primitiveSpinCNullPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter
              positiveLevel secondMultiplicity)
            sector circleMode (positiveLevel + 1)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) = _
  rw [
    primitiveSpinCNullPowerSection_apply_movingWitness
      period hPeriod,
    primitiveSpinCNullPowerSection_apply_movingWitness
      period hPeriod,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
      period hPeriod sector circleMode point time]
  simp only [primitiveSpinCNullSpherePower, starRingEnd_apply]
  ring

/-- Pointwise geometric pairing of two reconstructed gradients in one
positive-level block. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pointwise_pairing
    (positiveLevel : Nat)
    (firstMultiplicity secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel firstMultiplicity sector circleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel secondMultiplicity sector circleMode
          |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      8 *
        ((∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis (positiveLevel + 1)
                (primitiveSpinCNullGeometricParameter
                  positiveLevel firstMultiplicity) point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis (positiveLevel + 1)
              (primitiveSpinCNullGeometricParameter
                positiveLevel secondMultiplicity) point) +
          Complex.I *
            (∑ coordinate : Fin 3,
              star
                  (primitiveSpinCNullSpherePowerAmbientDerivative
                    (positiveLevel + 1)
                    (primitiveSpinCNullGeometricParameter
                      positiveLevel firstMultiplicity)
                    coordinate point) *
                primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (positiveLevel + 1)
                  (primitiveSpinCNullGeometricParameter
                    positiveLevel secondMultiplicity) point)) := by
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  rw [
    primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness
      period hPeriod positiveLevel firstMultiplicity sector circleMode
        point time,
    primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness
      period hPeriod positiveLevel secondMultiplicity sector circleMode
        point time,
    primitiveSpinCHopfTangentialCombination_pairing
      period hPeriod,
    primitiveSpinCNullSpherePower_tangentialMatrix_contraction
      period hPeriod,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
      period hPeriod sector circleMode point time]
  ring

/-- At each circle time, the sphere-integrated gradient pairing is the
round-sphere Casimir energy times the scalar-seed pairing. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_sphere_pairing_eq_casimir
    (positiveLevel : Nat)
    (firstMultiplicity secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel firstMultiplicity sector circleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel secondMultiplicity sector circleMode
            |>.gradientSection)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
        ∂SphereMeasure) =
      (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel firstMultiplicity sector circleMode
              |>.scalarSection)
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel secondMultiplicity sector circleMode
              |>.scalarSection)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
          ∂SphereMeasure := by
  let firstParameter :=
    primitiveSpinCNullGeometricParameter
      positiveLevel firstMultiplicity
  let secondParameter :=
    primitiveSpinCNullGeometricParameter
      positiveLevel secondMultiplicity
  let degree := positiveLevel + 1
  let angularIntegrand : MonopoleSphere → Complex := fun point =>
    ∑ axis : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAngularDerivative
            axis degree firstParameter point) *
        primitiveSpinCNullSpherePowerAngularDerivative
          axis degree secondParameter point
  let mixedIntegrand : MonopoleSphere → Complex := fun point =>
    ∑ coordinate : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAmbientDerivative
            degree firstParameter coordinate point) *
        primitiveSpinCNullSpherePowerAngularDerivative
          coordinate degree secondParameter point
  let scalarIntegrand : MonopoleSphere → Complex := fun point =>
    star
        (primitiveSpinCNullSpherePower
          degree firstParameter point) *
      primitiveSpinCNullSpherePower
        degree secondParameter point
  have hAngularIntegrable :
      Integrable angularIntegrand SphereMeasure :=
    integrable_finsetSum _ fun axis _ =>
      ((primitiveSpinCNullSpherePowerAngularDerivative_continuous
        axis degree firstParameter).star.mul
          (primitiveSpinCNullSpherePowerAngularDerivative_continuous
            axis degree secondParameter))
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hMixedIntegrable :
      Integrable mixedIntegrand SphereMeasure :=
    integrable_finsetSum _ fun coordinate _ =>
      ((primitiveSpinCNullSpherePowerAmbientDerivative_continuous
        degree firstParameter coordinate).star.mul
          (primitiveSpinCNullSpherePowerAngularDerivative_continuous
            coordinate degree secondParameter))
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  calc
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel firstMultiplicity sector circleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel secondMultiplicity sector circleMode
            |>.gradientSection)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
        ∂SphereMeasure) =
        ∫ point,
          8 * (angularIntegrand point +
            Complex.I * mixedIntegrand point)
          ∂SphereMeasure := by
      apply integral_congr_ae
      filter_upwards with point
      rw [primitiveSpinCAllLevelNullHarmonicGradient_pointwise_pairing
        period hPeriod positiveLevel firstMultiplicity secondMultiplicity
        sector circleMode point time]
    _ = 8 * ((∫ point, angularIntegrand point ∂SphereMeasure) +
        Complex.I * ∫ point, mixedIntegrand point ∂SphereMeasure) := by
      rw [integral_const_mul,
        integral_add hAngularIntegrable
          (hMixedIntegrable.const_mul Complex.I),
        integral_const_mul]
    _ = 8 *
        (((degree : Complex) * (degree + 1 : Nat)) *
            (∫ point, scalarIntegrand point ∂SphereMeasure) +
          Complex.I * 0) := by
      rw [
        show (∫ point, angularIntegrand point ∂SphereMeasure) =
            ((degree : Complex) * (degree + 1 : Nat)) *
              ∫ point, scalarIntegrand point ∂SphereMeasure by
          exact primitiveSpinCNullSpherePower_angular_energy_eq_casimir
            degree firstParameter secondParameter,
        show (∫ point, mixedIntegrand point ∂SphereMeasure) = 0 by
          exact
            primitiveSpinCNullSpherePowerAmbientDerivative_angular_sum_zero
              degree firstParameter secondParameter]
    _ = (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        ∫ point, 8 * scalarIntegrand point ∂SphereMeasure := by
      rw [integral_const_mul, primitiveSpinCHarmonicSphereEnergy_eq]
      dsimp only [degree]
      push_cast
      ring
    _ = (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel firstMultiplicity sector circleMode
              |>.scalarSection)
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel secondMultiplicity sector circleMode
              |>.scalarSection)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
          ∂SphereMeasure := by
      congr 1
      apply integral_congr_ae
      filter_upwards with point
      rw [primitiveSpinCAllLevelNullHarmonicScalar_pointwise_pairing
        period hPeriod positiveLevel firstMultiplicity secondMultiplicity
        sector circleMode point time]
      dsimp only [scalarIntegrand, degree, firstParameter, secondParameter]
      ring

/-- The global geometric `L²` gradient pairing is exactly the sphere
Casimir energy times the scalar-seed pairing. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pairing_eq_casimir
    (positiveLevel : Nat)
    (firstMultiplicity secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel firstMultiplicity sector circleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel secondMultiplicity sector circleMode
          |>.gradientSection) =
      (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel firstMultiplicity sector circleMode
            |>.scalarSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel secondMultiplicity sector circleMode
            |>.scalarSection) := by
  let firstGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel firstMultiplicity sector circleMode
      |>.gradientSection)
  let secondGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel secondMultiplicity sector circleMode
      |>.gradientSection)
  let firstScalar : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel firstMultiplicity sector circleMode
      |>.scalarSection)
  let secondScalar : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel secondMultiplicity sector circleMode
      |>.scalarSection)
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter firstGradient secondGradient =
      (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter firstScalar secondScalar
  rw [
    d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
      period hPeriod .positiveQuarter firstGradient secondGradient,
    d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
      period hPeriod .positiveQuarter firstScalar secondScalar]
  have hGradientIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter firstGradient secondGradient
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hGradientIntrinsic
  have hGradientPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstGradient secondGradient
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hGradientIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  have hScalarIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter firstScalar secondScalar
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hScalarIntrinsic
  have hScalarPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstScalar secondScalar
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hScalarIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  unfold canonicalLatitudeBaseMeasure at hGradientPullback hScalarPullback ⊢
  rw [integral_prod_symm _ hGradientPullback,
    integral_prod_symm _ hScalarPullback,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with time
  change
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter firstGradient secondGradient
          (canonicalLatitudeThroatMap period hPeriod (point, time))
        ∂SphereMeasure) =
      (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstScalar secondScalar
            (canonicalLatitudeThroatMap period hPeriod (point, time))
          ∂SphereMeasure
  simp_rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
  exact
    primitiveSpinCAllLevelNullHarmonicGradient_sphere_pairing_eq_casimir
      period hPeriod positiveLevel firstMultiplicity secondMultiplicity
      sector circleMode time

/-- The product of the scalar coefficients of the two opposite signed
branches is minus the positive sphere-Casimir energy. -/
theorem primitiveSpinCGeometricL2SignedBranchScalarCoefficient_pos_neg
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    star
          (primitiveSpinCGeometricL2SignedBranchScalarCoefficient
            period positiveLevel .positive sector circleMode) *
        primitiveSpinCGeometricL2SignedBranchScalarCoefficient
          period positiveLevel .negative sector circleMode =
      -(primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) := by
  have hReal :
      (primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode -
          normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) *
        (-primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode -
          normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) =
      -primitiveSpinCHarmonicSphereEnergy positiveLevel := by
    have hSquare :=
      primitiveSpinCHarmonicDiracFrequency_sq
        period positiveLevel sector circleMode
    nlinarith
  simpa [primitiveSpinCGeometricL2SignedBranchScalarCoefficient,
    primitiveSpinCDiracBranchSign_positive,
    primitiveSpinCDiracBranchSign_negative] using
      congrArg (fun value : Real => (value : Complex)) hReal

/-- Opposite signed raw packets are exactly orthogonal at fixed spectral
labels, including arbitrary multiplicities. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_pos_neg_orthogonal
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (firstMultiplicity secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel .positive sector circleMode
            firstMultiplicity)
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel .negative sector circleMode
            secondMultiplicity) =
      0 := by
  rw [
    primitiveSpinCGeometricL2SignedBranchRawFamily_pairing_eq_diagonal,
    primitiveSpinCGeometricL2SignedBranchScalarCoefficient_pos_neg,
    primitiveSpinCAllLevelNullHarmonicGradient_pairing_eq_casimir]
  ring

/-- The complete positive and negative first-order blocks are orthogonal
in the independently constructed geometric `L²` product. -/
theorem primitiveSpinCGeometricL2SignedBranchBlocks_isOrtho
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel .positive sector circleMode ⟂
      primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel .negative sector circleMode := by
  unfold primitiveSpinCGeometricL2SignedBranchBlock
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨firstMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2SignedBranchRawFamily
            period hPeriod positiveLevel .positive sector circleMode
              firstMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨secondMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2SignedBranchRawFamily
              period hPeriod positiveLevel .positive sector circleMode
                firstMultiplicity)
            (primitiveSpinCGeometricL2SignedBranchRawFamily
              period hPeriod positiveLevel .negative sector circleMode
                secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2SignedBranchRawFamily_pos_neg_orthogonal
          period hPeriod positiveLevel sector circleMode
          firstMultiplicity secondMultiplicity
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

/-- Assumption-free certificate for the exact gradient/Casimir transfer and
opposite-sign orthogonality. -/
structure ProgramPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
    where
  mixedTermZero :
    ∀ degree firstParameter secondParameter,
      (∫ point,
          ∑ coordinate : Fin 3,
            star
                (primitiveSpinCNullSpherePowerAmbientDerivative
                  degree firstParameter coordinate point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate degree secondParameter point
          ∂SphereMeasure) = 0
  angularCasimir :
    ∀ degree firstParameter secondParameter,
      (∫ point,
          ∑ axis : Fin 3,
            star
                (primitiveSpinCNullSpherePowerAngularDerivative
                  axis degree firstParameter point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                axis degree secondParameter point
          ∂SphereMeasure) =
        ((degree : Complex) * (degree + 1 : Nat)) *
          ∫ point,
            star
                (primitiveSpinCNullSpherePower
                  degree firstParameter point) *
              primitiveSpinCNullSpherePower
                degree secondParameter point
            ∂SphereMeasure
  gradientPairing :
    ∀ positiveLevel firstMultiplicity secondMultiplicity sector circleMode,
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel firstMultiplicity sector circleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel secondMultiplicity sector circleMode
            |>.gradientSection) =
        (primitiveSpinCHarmonicSphereEnergy positiveLevel : Complex) *
          d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel firstMultiplicity sector circleMode
              |>.scalarSection)
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel secondMultiplicity sector circleMode
              |>.scalarSection)
  oppositeSignedBlocks :
    ∀ positiveLevel sector circleMode,
      primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel .positive sector circleMode ⟂
        primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel .negative sector circleMode

def programPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
      period hPeriod where
  mixedTermZero :=
    primitiveSpinCNullSpherePowerAmbientDerivative_angular_sum_zero
  angularCasimir :=
    primitiveSpinCNullSpherePower_angular_energy_eq_casimir
  gradientPairing :=
    primitiveSpinCAllLevelNullHarmonicGradient_pairing_eq_casimir
      period hPeriod
  oppositeSignedBlocks :=
    primitiveSpinCGeometricL2SignedBranchBlocks_isOrtho
      period hPeriod

theorem primitiveSpinCGeometricL2GradientCasimir_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
end JanusFormal
