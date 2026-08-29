import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSignedPolynomialTangentExhaustion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensity4D

/-!
# Fourier--monopole completeness for the geometric primitive SpinC Dirac space

Polynomial monopole packets and temporal Fourier modes reconstruct the signed
Hopf frame uniformly on the compact throat.  The resulting pointwise estimate
proves density in the geometric L2 completion and promotes the signed synthesis
to a global linear isometric equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D

open Module
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleSpectralBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCMonopoleFiniteFrame4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSignedPolynomialTangentExhaustion4D
open P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCThroatFourierMonopoleDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

local instance throatBaseCompactSpace :
    CompactSpace
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance canonicalThroatFiniteMeasure :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance d9DoubledMatterFiberComplexModule :
    Module Complex D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorLinearEquiv.toAddEquiv.module Complex

abbrev SolidPolynomial :=
  MvPolynomial (Fin 3) Complex

abbrev SolidPolynomialVector :=
  Fin 3 → SolidPolynomial

def solidPolynomialTangentSection
    (vector : SolidPolynomialVector)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  ∑ coordinate : Fin 3,
    solidPolynomialSection
      period hPeriod (vector coordinate)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector circleMode)

theorem solidPolynomialTangentSection_apply
    (vector : SolidPolynomialVector)
    (sector : NormalRootChoice) (circleMode : Int) (base) :
    (show D9DoubledMatterFiber from
      solidPolynomialTangentSection
        period hPeriod vector sector circleMode base) =
      ∑ coordinate : Fin 3,
        d9PrimitiveSpinCComplexActionCLM
          (MvPolynomial.eval
            (fun direction =>
              (P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D.d9PrimitiveMonopoleBaseCoordinate
                period hPeriod direction base : Complex))
            (vector coordinate))
          (show D9DoubledMatterFiber from
            primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode base) := by
  unfold solidPolynomialTangentSection
  change
    (show D9DoubledMatterFiber from
      d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base
        (∑ coordinate : Fin 3,
          solidPolynomialSection
            period hPeriod (vector coordinate)
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode))) = _
  rw [map_sum]
  simp only [d9PrimitiveSpinCSectionEvaluation_apply,
    solidPolynomialSection_apply]
  rfl

theorem solidPolynomialSection_state_add
    (polynomial : SolidPolynomial)
    (first second : SmoothSection period hPeriod) :
    solidPolynomialSection
        period hPeriod polynomial (first + second) =
      solidPolynomialSection period hPeriod polynomial first +
        solidPolynomialSection period hPeriod polynomial second := by
  apply DFunLike.ext _ _
  intro base
  rw [show
    (solidPolynomialSection period hPeriod polynomial first +
      solidPolynomialSection period hPeriod polynomial second) base =
        solidPolynomialSection period hPeriod polynomial first base +
          solidPolynomialSection period hPeriod polynomial second base by
    rfl]
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod polynomial (first + second) base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection period hPeriod polynomial first base) +
        (show D9DoubledMatterFiber from
          solidPolynomialSection period hPeriod polynomial second base)
  rw [solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    show
    (show D9DoubledMatterFiber from (first + second) base) =
      (show D9DoubledMatterFiber from first base) +
        (show D9DoubledMatterFiber from second base) by rfl,
    map_add]

theorem solidPolynomialSection_state_smul
    (polynomial : SolidPolynomial) (scalar : Complex)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection
        period hPeriod polynomial (scalar • state) =
      scalar • solidPolynomialSection
        period hPeriod polynomial state := by
  apply DFunLike.ext _ _
  intro base
  rw [primitiveSpinCComplex_smul]
  rw [show
    (scalar • solidPolynomialSection
      period hPeriod polynomial state) base =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar
          (solidPolynomialSection
            period hPeriod polynomial state) base by rfl]
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod polynomial
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state) base) =
      (show D9DoubledMatterFiber from
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar
          (solidPolynomialSection
            period hPeriod polynomial state) base)
  rw [solidPolynomialSection_apply,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction,
    solidPolynomialSection_apply,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1
  ring

def solidPolynomialSectionStateLinearMap
    (polynomial : SolidPolynomial) :
    SmoothSection period hPeriod →ₗ[Complex]
      SmoothSection period hPeriod where
  toFun state :=
    solidPolynomialSection period hPeriod polynomial state
  map_add' :=
    solidPolynomialSection_state_add period hPeriod polynomial
  map_smul' :=
    solidPolynomialSection_state_smul period hPeriod polynomial

@[simp]
theorem solidPolynomialSectionStateLinearMap_apply
    (polynomial : SolidPolynomial)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSectionStateLinearMap
        period hPeriod polynomial state =
      solidPolynomialSection period hPeriod polynomial state :=
  rfl

theorem solidPolynomialSection_sub
    (first second : SolidPolynomial)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection period hPeriod (first - second) state =
      solidPolynomialSection period hPeriod first state -
        solidPolynomialSection period hPeriod second state := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod (first - second) state base) =
      (show D9DoubledMatterFiber from
        (solidPolynomialSection period hPeriod first state -
          solidPolynomialSection period hPeriod second state) base)
  rw [show
    (show D9DoubledMatterFiber from
      (solidPolynomialSection period hPeriod first state -
        solidPolynomialSection period hPeriod second state) base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection period hPeriod first state base) -
        (show D9DoubledMatterFiber from
          solidPolynomialSection period hPeriod second state base) by rfl,
    solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    map_sub]
  simp only [← d9DoubledMatterFiber_complex_smul_eq_action]
  module

theorem solidPolynomialSection_X_mul
    (coordinate : Fin 3) (polynomial : SolidPolynomial)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection
        period hPeriod (MvPolynomial.X coordinate * polynomial) state =
      solidPolynomialSection
        period hPeriod polynomial
        (primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod coordinate state) := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod (MvPolynomial.X coordinate * polynomial) state base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection period hPeriod polynomial
          (primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod coordinate state) base)
  rw [solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    MvPolynomial.eval_mul, MvPolynomial.eval_X]
  let coordinateValue :=
    d9PrimitiveMonopoleBaseCoordinate
      period hPeriod coordinate base
  let polynomialValue :=
    MvPolynomial.eval
      (fun direction =>
        (d9PrimitiveMonopoleBaseCoordinate
          period hPeriod direction base : Complex))
      polynomial
  let matter : D9DoubledMatterFiber := state base
  change
    d9PrimitiveSpinCComplexActionCLM
        ((coordinateValue : Complex) * polynomialValue) matter =
      d9PrimitiveSpinCComplexActionCLM polynomialValue
        (coordinateValue • matter)
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_smul]
  module

def solidPolynomialDot
    (vector : SolidPolynomialVector) : SolidPolynomial :=
  ∑ coordinate : Fin 3, MvPolynomial.X coordinate * vector coordinate

def solidPolynomialCurl
    (vector : SolidPolynomialVector) : SolidPolynomialVector :=
  ![
    MvPolynomial.pderiv 1 (vector 2) -
      MvPolynomial.pderiv 2 (vector 1),
    MvPolynomial.pderiv 2 (vector 0) -
      MvPolynomial.pderiv 0 (vector 2),
    MvPolynomial.pderiv 0 (vector 1) -
      MvPolynomial.pderiv 1 (vector 0)]

def solidPolynomialCross
    (vector : SolidPolynomialVector) : SolidPolynomialVector :=
  ![
    MvPolynomial.X 1 * vector 2 -
      MvPolynomial.X 2 * vector 1,
    MvPolynomial.X 2 * vector 0 -
      MvPolynomial.X 0 * vector 2,
    MvPolynomial.X 0 * vector 1 -
      MvPolynomial.X 1 * vector 0]

def solidPolynomialGradient
    (polynomial : SolidPolynomial) : SolidPolynomialVector :=
  fun coordinate => MvPolynomial.pderiv coordinate polynomial

theorem solidPolynomialGradient_dot
    (degree : Nat) (vector : SolidPolynomialVector)
    (hVector :
      ∀ coordinate, (vector coordinate).IsHomogeneous degree) :
    solidPolynomialGradient (solidPolynomialDot vector) =
      fun coordinate =>
        ((degree + 1 : Nat) : Complex) • vector coordinate +
          solidPolynomialCross (solidPolynomialCurl vector) coordinate := by
  have hEuler0 := (hVector 0).sum_X_mul_pderiv
  have hEuler1 := (hVector 1).sum_X_mul_pderiv
  have hEuler2 := (hVector 2).sum_X_mul_pderiv
  simp only [Fin.sum_univ_three, nsmul_eq_mul] at hEuler0 hEuler1 hEuler2
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [solidPolynomialGradient, solidPolynomialDot,
      solidPolynomialCross, solidPolynomialCurl,
      Fin.sum_univ_three, MvPolynomial.smul_eq_C_mul]
  · linear_combination hEuler0
  · linear_combination hEuler1
  · linear_combination hEuler2

theorem solidPolynomialTangentSection_cross
    (vector : SolidPolynomialVector)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (solidPolynomialCross vector) sector circleMode =
      (-Complex.I) •
        solidPolynomialTangentSection
          period hPeriod vector sector circleMode := by
  unfold solidPolynomialTangentSection
  simp only [Fin.sum_univ_three]
  rw [show
      solidPolynomialCross vector 0 =
        MvPolynomial.X 1 * vector 2 -
          MvPolynomial.X 2 * vector 1 by
      simp [solidPolynomialCross],
    show
      solidPolynomialCross vector 1 =
        MvPolynomial.X 2 * vector 0 -
          MvPolynomial.X 0 * vector 2 by
      simp [solidPolynomialCross],
    show
      solidPolynomialCross vector 2 =
        MvPolynomial.X 0 * vector 1 -
          MvPolynomial.X 1 * vector 0 by
      simp [solidPolynomialCross]]
  rw [solidPolynomialSection_sub,
    solidPolynomialSection_sub,
    solidPolynomialSection_sub,
    solidPolynomialSection_X_mul,
    solidPolynomialSection_X_mul,
    solidPolynomialSection_X_mul,
    solidPolynomialSection_X_mul,
    solidPolynomialSection_X_mul,
    solidPolynomialSection_X_mul]
  let tangent : Fin 3 → SmoothSection period hPeriod := fun coordinate =>
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector circleMode
  let coefficient : Fin 3 →
      SmoothSection period hPeriod →ₗ[Complex]
        SmoothSection period hPeriod := fun coordinate =>
    solidPolynomialSectionStateLinearMap
      period hPeriod (vector coordinate)
  let coordinateMap : Fin 3 →
      SmoothSection period hPeriod →ₗ[Complex]
        SmoothSection period hPeriod := fun coordinate =>
    primitiveSpinCCoordinateMultiplicationComplexLinearMap
      period hPeriod coordinate
  change
    coefficient 2 (coordinateMap 1 (tangent 0)) -
          coefficient 1 (coordinateMap 2 (tangent 0)) +
        (coefficient 0 (coordinateMap 2 (tangent 1)) -
          coefficient 2 (coordinateMap 0 (tangent 1))) +
      (coefficient 1 (coordinateMap 0 (tangent 2)) -
        coefficient 0 (coordinateMap 1 (tangent 2))) =
      (-Complex.I) •
        (coefficient 0 (tangent 0) +
          coefficient 1 (tangent 1) +
            coefficient 2 (tangent 2))
  calc
    _ =
        coefficient 0
            (coordinateMap 2 (tangent 1) -
              coordinateMap 1 (tangent 2)) +
          coefficient 1
            (coordinateMap 0 (tangent 2) -
              coordinateMap 2 (tangent 0)) +
        coefficient 2
          (coordinateMap 1 (tangent 0) -
            coordinateMap 0 (tangent 1)) := by
      simp only [map_sub]
      abel
    _ =
        coefficient 0 ((-Complex.I) • tangent 0) +
          coefficient 1 ((-Complex.I) • tangent 1) +
        coefficient 2 ((-Complex.I) • tangent 2) := by
      rw [show
          coordinateMap 2 (tangent 1) -
              coordinateMap 1 (tangent 2) =
            (-Complex.I) • tangent 0 by
          exact tangent_cross_basis_zero
            period hPeriod sector circleMode,
        show
          coordinateMap 0 (tangent 2) -
              coordinateMap 2 (tangent 0) =
            (-Complex.I) • tangent 1 by
          exact tangent_cross_basis_one
            period hPeriod sector circleMode,
        show
          coordinateMap 1 (tangent 0) -
              coordinateMap 0 (tangent 1) =
            (-Complex.I) • tangent 2 by
          exact tangent_cross_basis_two
            period hPeriod sector circleMode]
    _ = _ := by
      rw [map_smul, map_smul, map_smul]
      module

theorem solidPolynomialTangentSection_add
    (first second : SolidPolynomialVector)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (first + second) sector circleMode =
      solidPolynomialTangentSection
          period hPeriod first sector circleMode +
        solidPolynomialTangentSection
          period hPeriod second sector circleMode := by
  unfold solidPolynomialTangentSection
  simp_rw [Pi.add_apply,
    solidPolynomialSection_add period hPeriod]
  exact Finset.sum_add_distrib

theorem solidPolynomialTangentSection_smul
    (scalar : Complex) (vector : SolidPolynomialVector)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (scalar • vector) sector circleMode =
      scalar •
        solidPolynomialTangentSection
          period hPeriod vector sector circleMode := by
  unfold solidPolynomialTangentSection
  simp_rw [Pi.smul_apply,
    solidPolynomialSection_smul period hPeriod]
  rw [Finset.smul_sum]

theorem solidPolynomialTangentSection_gradient_dot
    (degree : Nat) (vector : SolidPolynomialVector)
    (hVector :
      ∀ coordinate, (vector coordinate).IsHomogeneous degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod
        (solidPolynomialGradient (solidPolynomialDot vector))
        sector circleMode =
      ((degree + 1 : Nat) : Complex) •
          solidPolynomialTangentSection
            period hPeriod vector sector circleMode +
        (-Complex.I) •
          solidPolynomialTangentSection
            period hPeriod (solidPolynomialCurl vector)
            sector circleMode := by
  rw [solidPolynomialGradient_dot degree vector hVector]
  change
    solidPolynomialTangentSection
        period hPeriod
        (((((degree + 1 : Nat) : Complex) • vector) +
          solidPolynomialCross (solidPolynomialCurl vector)))
        sector circleMode = _
  rw [solidPolynomialTangentSection_add,
    solidPolynomialTangentSection_smul,
    solidPolynomialTangentSection_cross]

theorem solidPolynomialTangentSection_homotopy
    (degree : Nat) (vector : SolidPolynomialVector)
    (hVector :
      ∀ coordinate, (vector coordinate).IsHomogeneous degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod vector sector circleMode =
      ((((degree + 1 : Nat) : Complex)⁻¹) •
        (solidPolynomialTangentSection
            period hPeriod
            (solidPolynomialGradient (solidPolynomialDot vector))
            sector circleMode +
          Complex.I •
            solidPolynomialTangentSection
              period hPeriod (solidPolynomialCurl vector)
              sector circleMode)) := by
  have hDegree :
      (((degree + 1 : Nat) : Complex)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero degree
  rw [solidPolynomialTangentSection_gradient_dot
    period hPeriod degree vector hVector sector circleMode]
  rw [smul_add, smul_smul, smul_add, smul_smul,
    smul_smul, inv_mul_cancel₀ hDegree, one_smul]
  module

theorem hopfTangential_radial_sum
    (sector : NormalRootChoice) (circleMode : Int) :
    (∑ coordinate : Fin 3,
      primitiveSpinCCoordinateMultiplicationComplexLinearMap
        period hPeriod coordinate
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode)) = 0 := by
  apply DFunLike.ext _ _
  intro base
  change
    d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base
        (∑ coordinate : Fin 3,
          primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod coordinate
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode)) =
      (0 : D9PrimitiveSpinCFiber
        period hPeriod .positiveQuarter base)
  rw [map_sum]
  simp only [d9PrimitiveSpinCSectionEvaluation_apply,
    primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let n : Fin 3 → Real := fun coordinate =>
    d9PrimitiveMonopoleBaseCoordinate
      period hPeriod coordinate base
  have hRadial :
      ∑ coordinate : Fin 3,
          n coordinate •
            d9DoubledMatterFiberCliffordGammaCLM
              coordinate matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [d9PrimitiveSpinCBaseUnitRadialClifford,
      d9PrimitiveSpinCBaseUnitRadialCoordinate,
      n, matter] using
      primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base
  have hSphere :
      ∑ coordinate : Fin 3, n coordinate ^ 2 = 1 := by
    let point :=
      d9ThroatMonopoleSphereProjection period hPeriod base
    simpa [Fin.sum_univ_three, n,
      d9PrimitiveMonopoleBaseCoordinate, point] using
      monopoleSphereCoordinate_sq_sum point
  unfold d9PrimitiveSpinCBaseUnitRadialCoordinate
  change
    (∑ coordinate : Fin 3,
      n coordinate •
        (d9DoubledMatterFiberCliffordGammaCLM coordinate matter -
          n coordinate •
            d9PrimitiveSpinCImaginaryAction matter)) = 0
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, hRadial]
  rw [show
      (∑ coordinate : Fin 3,
        n coordinate •
          (n coordinate •
            d9PrimitiveSpinCImaginaryAction matter)) =
        (∑ coordinate : Fin 3, n coordinate ^ 2) •
          d9PrimitiveSpinCImaginaryAction matter by
      simp_rw [smul_smul, sq]
      rw [Finset.sum_smul],
    hSphere, one_smul, sub_self]

theorem nullHarmonicGradient_mem_signedBlock
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode).gradientSection ∈
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode := by
  let seed :=
    (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel multiplicity sector circleMode
  let block :=
    primitiveSpinCGeometricL2SignedBlock
      period hPeriod positiveLevel sector circleMode
  have hPositive : seed.positiveSection ∈ block := by
    exact Submodule.mem_sup_left
      (Submodule.subset_span ⟨multiplicity, rfl⟩)
  have hScalar : seed.scalarSection ∈ block := by
    exact nullHarmonicScalar_mem_signedBlock
      period hPeriod positiveLevel multiplicity sector circleMode
  have hIdentity :
      seed.gradientSection =
        seed.positiveSection -
          ((primitiveSpinCHarmonicDiracFrequency
                period positiveLevel sector circleMode -
            normalRootLeviCivitaCorrectedFrequency
              period sector circleMode : Real) : Complex) •
            seed.scalarSection := by
    rw [d9PrimitiveSpinCGeometricL2_complex_smul,
      d9PrimitiveSpinCComplexScalarSection_ofReal]
    unfold PrimitiveSpinCHarmonicDiracSeed4D.positiveSection
    module
  change seed.gradientSection ∈ block
  rw [hIdentity]
  exact Submodule.sub_mem block hPositive
    (Submodule.smul_mem block _ hScalar)

theorem nullHarmonicGradient_coe_mem_globalRange
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    (((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode).gradientSection :
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter) ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap :=
  coe_mem_globalRange_of_mem_signedBlock
    period hPeriod positiveLevel sector circleMode _
    (nullHarmonicGradient_mem_signedBlock
      period hPeriod positiveLevel multiplicity sector circleMode)

theorem solidPolynomialSection_radiusSquared_mul
    (polynomial : SolidPolynomial)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection
        period hPeriod
        (primitiveSpinCSolidRadiusSquared * polynomial) state =
      solidPolynomialSection period hPeriod polynomial state := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod
        (primitiveSpinCSolidRadiusSquared * polynomial) state base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection period hPeriod polynomial state base)
  rw [solidPolynomialSection_apply, solidPolynomialSection_apply,
    MvPolynomial.eval_mul]
  have hSphere :
      ∑ coordinate : Fin 3,
          d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base ^ 2 =
        1 := by
    let point :=
      d9ThroatMonopoleSphereProjection period hPeriod base
    simpa [Fin.sum_univ_three,
      d9PrimitiveMonopoleBaseCoordinate, point] using
      monopoleSphereCoordinate_sq_sum point
  have hRadius :
      MvPolynomial.eval
          (fun coordinate =>
            (d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base : Complex))
          primitiveSpinCSolidRadiusSquared =
        1 := by
    simp [primitiveSpinCSolidRadiusSquared,
      Fin.sum_univ_three]
    have hSphere' :
        d9PrimitiveMonopoleBaseCoordinate period hPeriod 0 base ^ 2 +
              d9PrimitiveMonopoleBaseCoordinate period hPeriod 1 base ^ 2 +
            d9PrimitiveMonopoleBaseCoordinate period hPeriod 2 base ^ 2 =
          1 := by
      simpa [Fin.sum_univ_three] using hSphere
    exact_mod_cast hSphere'
  rw [hRadius, one_mul]

theorem solidPolynomialGradient_radiusSquared_mul
    (polynomial : SolidPolynomial) :
    solidPolynomialGradient
        (primitiveSpinCSolidRadiusSquared * polynomial) =
      fun coordinate =>
        (2 : Complex) •
            (MvPolynomial.X coordinate * polynomial) +
          primitiveSpinCSolidRadiusSquared *
            MvPolynomial.pderiv coordinate polynomial := by
  have hTwo :
      (MvPolynomial.C (2 : Complex) : SolidPolynomial) = 2 := by
    exact MvPolynomial.C_eq_coe_nat 2
  funext coordinate
  fin_cases coordinate <;>
    simp [solidPolynomialGradient,
      primitiveSpinCSolidRadiusSquared,
      Fin.sum_univ_three, MvPolynomial.smul_eq_C_mul] <;>
    rw [hTwo] <;>
    ring

theorem solidPolynomialTangentSection_gradient_radiusSquared_mul
    (polynomial : SolidPolynomial)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod
        (solidPolynomialGradient
          (primitiveSpinCSolidRadiusSquared * polynomial))
        sector circleMode =
      solidPolynomialTangentSection
        period hPeriod (solidPolynomialGradient polynomial)
        sector circleMode := by
  rw [solidPolynomialGradient_radiusSquared_mul]
  unfold solidPolynomialTangentSection
  simp_rw [solidPolynomialSection_add,
    solidPolynomialSection_smul,
    solidPolynomialSection_radiusSquared_mul]
  rw [Finset.sum_add_distrib]
  have hRadial :
      (∑ coordinate : Fin 3,
        (2 : Complex) •
          solidPolynomialSection period hPeriod
            (MvPolynomial.X coordinate * polynomial)
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector circleMode)) = 0 := by
    rw [← Finset.smul_sum]
    simp_rw [solidPolynomialSection_X_mul]
    change
      (2 : Complex) •
        (∑ coordinate : Fin 3,
          solidPolynomialSectionStateLinearMap
              period hPeriod polynomial
            (primitiveSpinCCoordinateMultiplicationComplexLinearMap
              period hPeriod coordinate
              (primitiveSpinCHopfFirstSphereTangentialSection
                period hPeriod coordinate sector circleMode))) = 0
    rw [← map_sum,
      hopfTangential_radial_sum period hPeriod sector circleMode,
      map_zero, smul_zero]
  rw [hRadial, zero_add]
  rfl

theorem solidHarmonicPacket_pderiv_eval_sphere
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (coordinate : Fin 3) (point : MonopoleSphere) :
    MvPolynomial.eval
        (fun direction : Fin 3 =>
          (monopoleSphereCoordinate point direction : Complex))
        (MvPolynomial.pderiv coordinate
          (primitiveSpinCSolidHarmonicPacket degree multiplicity)) =
      primitiveSpinCNullSpherePowerAmbientDerivative
        degree
        (primitiveSpinCSolidPacketParameter degree multiplicity)
        coordinate point := by
  fin_cases coordinate <;>
    simp [primitiveSpinCSolidHarmonicPacket,
      primitiveSpinCNullSpherePowerAmbientDerivative,
      primitiveSpinCNullSpherePower,
      primitiveSpinCNullSphereScalar,
      primitiveSpinCSolidNullLinearForm,
      Fin.sum_univ_three] <;>
    ring

theorem solidHarmonicGeometricPacket_gradient_apply_movingWitness
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    (show D9DoubledMatterFiber from
      solidPolynomialTangentSection
        period hPeriod
        (solidPolynomialGradient
          (primitiveSpinCSolidHarmonicGeometricPacket
            (positiveLevel + 1) multiplicity))
        sector circleMode
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)) =
      (show D9DoubledMatterFiber from
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) := by
  rw [solidPolynomialTangentSection_apply,
    primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp_rw [primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  congr 1
  apply congrArg d9PrimitiveSpinCComplexActionCLM
  unfold solidPolynomialGradient
    primitiveSpinCSolidHarmonicGeometricPacket
    primitiveSpinCNullGeometricParameter
  exact solidHarmonicPacket_pderiv_eval_sphere
    (positiveLevel + 1)
    (Fin.cast
      (primitiveSpinCSolidPacket_degeneracy_eq (positiveLevel + 1))
      multiplicity)
    coordinate point

theorem nullPacketMovingWitnessBase_of_cover
    (cover :
      MappingTorusCover (fixedEquatorData period hPeriod)) :
    primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod
        (d9MonopoleSphereCoverProjection period hPeriod cover)
        cover.time =
      mappingTorusMk (fixedEquatorData period hPeriod) cover := by
  unfold primitiveSpinCNullPacketMovingWitnessBase
    primitiveSpinCNullPacketMovingWitnessCover
  congr 1
  apply MappingTorusCover.ext
  · simp [d9MonopoleSphereCoverProjection]
  · rfl

theorem nullPacketMovingWitnessBase_surjective :
    Function.Surjective
      (fun pointTime : MonopoleSphere × Real =>
        primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod pointTime.1 pointTime.2) := by
  intro base
  refine Quotient.inductionOn base ?_
  intro cover
  exact
    ⟨(d9MonopoleSphereCoverProjection period hPeriod cover,
        cover.time),
      nullPacketMovingWitnessBase_of_cover period hPeriod cover⟩

def solidHarmonicGeometricPacketGradientSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  solidPolynomialTangentSection
    period hPeriod
    (solidPolynomialGradient
      (primitiveSpinCSolidHarmonicGeometricPacket
        (positiveLevel + 1) multiplicity))
    sector circleMode

theorem solidHarmonicGeometricPacket_gradientSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidHarmonicGeometricPacketGradientSection
        period hPeriod positiveLevel multiplicity sector circleMode =
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.gradientSection) := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidHarmonicGeometricPacketGradientSection
        period hPeriod positiveLevel multiplicity sector circleMode
        base) =
      (show D9DoubledMatterFiber from
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection)
          base)
  obtain ⟨⟨point, time⟩, hBase⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  rw [← hBase]
  simpa [solidHarmonicGeometricPacketGradientSection] using
    solidHarmonicGeometricPacket_gradient_apply_movingWitness
      period hPeriod positiveLevel multiplicity sector circleMode
      point time

def signedGlobalSmoothRange :
    Submodule Complex (SmoothSection period hPeriod) :=
  (LinearMap.range
      (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
        period hPeriod).toLinearMap).comap
    (d9PrimitiveSpinCGeometricL2Embedding
      period hPeriod .positiveQuarter).toLinearMap

theorem solidHarmonicGeometricPacketGradient_mem_signedGlobalSmoothRange
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidHarmonicGeometricPacketGradientSection
        period hPeriod positiveLevel multiplicity sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  rw [solidHarmonicGeometricPacket_gradientSection]
  exact nullHarmonicGradient_coe_mem_globalRange
    period hPeriod positiveLevel multiplicity sector circleMode

theorem solidPolynomialGradient_add
    (first second : SolidPolynomial) :
    solidPolynomialGradient (first + second) =
      solidPolynomialGradient first + solidPolynomialGradient second := by
  funext coordinate
  simp [solidPolynomialGradient]

theorem solidPolynomialGradient_smul
    (scalar : Complex) (polynomial : SolidPolynomial) :
    solidPolynomialGradient (scalar • polynomial) =
      scalar • solidPolynomialGradient polynomial := by
  funext coordinate
  simp [solidPolynomialGradient]

def solidPolynomialGradientTangentLinearMap
    (sector : NormalRootChoice) (circleMode : Int) :
    SolidPolynomial →ₗ[Complex] SmoothSection period hPeriod where
  toFun polynomial :=
    solidPolynomialTangentSection
      period hPeriod (solidPolynomialGradient polynomial)
      sector circleMode
  map_add' first second := by
    rw [solidPolynomialGradient_add,
      solidPolynomialTangentSection_add]
  map_smul' scalar polynomial := by
    rw [solidPolynomialGradient_smul,
      solidPolynomialTangentSection_smul]
    rfl

@[simp]
theorem solidPolynomialGradientTangentLinearMap_apply
    (polynomial : SolidPolynomial)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialGradientTangentLinearMap
        period hPeriod sector circleMode polynomial =
      solidPolynomialTangentSection
        period hPeriod (solidPolynomialGradient polynomial)
        sector circleMode :=
  rfl

theorem solidPolynomialSection_zero
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection period hPeriod 0 state = 0 := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection period hPeriod 0 state base) = 0
  rw [solidPolynomialSection_apply]
  simp

theorem solidHarmonicPacketGradient_mem_signedGlobalSmoothRange
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod
        (solidPolynomialGradient
          (primitiveSpinCSolidHarmonicPacket degree multiplicity))
        sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  cases degree with
  | zero =>
      change
        solidPolynomialTangentSection
            period hPeriod (solidPolynomialGradient 1)
            sector circleMode ∈
          signedGlobalSmoothRange period hPeriod
      have hZero :
          solidPolynomialGradient (1 : SolidPolynomial) = 0 := by
        funext coordinate
        simp [solidPolynomialGradient]
      rw [hZero]
      have hTangentZero :
          solidPolynomialTangentSection
              period hPeriod 0 sector circleMode =
            0 := by
        unfold solidPolynomialTangentSection
        simp [solidPolynomialSection_zero]
      rw [hTangentZero]
      exact Submodule.zero_mem _
  | succ positiveLevel =>
      let physicalMultiplicity :
          Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) :=
        Fin.cast
          (primitiveSpinCSolidPacket_degeneracy_eq
            (positiveLevel + 1)).symm multiplicity
      have hPacket :
          primitiveSpinCSolidHarmonicGeometricPacket
              (positiveLevel + 1) physicalMultiplicity =
            primitiveSpinCSolidHarmonicPacket
              (positiveLevel + 1) multiplicity := by
        unfold primitiveSpinCSolidHarmonicGeometricPacket
          physicalMultiplicity
        congr 1
      rw [← hPacket]
      change
        solidHarmonicGeometricPacketGradientSection
            period hPeriod positiveLevel physicalMultiplicity
            sector circleMode ∈
          signedGlobalSmoothRange period hPeriod
      exact
        solidHarmonicGeometricPacketGradient_mem_signedGlobalSmoothRange
          period hPeriod positiveLevel physicalMultiplicity
          sector circleMode

theorem solidHarmonicGradient_mem_signedGlobalSmoothRange
    (degree : Nat)
    (harmonic : solidHarmonicHomogeneousSubmodule degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (solidPolynomialGradient harmonic.1)
        sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  let gradientMap :
      solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
        SmoothSection period hPeriod :=
    (solidPolynomialGradientTangentLinearMap
      period hPeriod sector circleMode).comp
      (solidHarmonicHomogeneousSubmodule degree).subtype
  have hLe :
      Submodule.span Complex
          (Set.range (solidHarmonicPacketElement degree)) ≤
        (signedGlobalSmoothRange period hPeriod).comap gradientMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨multiplicity, rfl⟩
    change
      solidPolynomialTangentSection
          period hPeriod
          (solidPolynomialGradient
            (primitiveSpinCSolidHarmonicPacket degree multiplicity))
          sector circleMode ∈
        signedGlobalSmoothRange period hPeriod
    exact solidHarmonicPacketGradient_mem_signedGlobalSmoothRange
      period hPeriod degree multiplicity sector circleMode
  rw [solidHarmonicPacketElement_span_eq_top] at hLe
  exact hLe (Submodule.mem_top)

theorem solidHomogeneousGradient_mem_signedGlobalSmoothRange
    (degree : Nat)
    (polynomial :
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (solidPolynomialGradient polynomial.1)
        sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  induction degree using Nat.strong_induction_on with
  | h degree inductionHypothesis =>
      by_cases hSmall : degree < 2
      · have hRange :
            polynomial ∈ solidHarmonicHomogeneousRange degree := by
          rw [solidHarmonicHomogeneousRange_eq_top_of_lt_two
            degree hSmall]
          exact Submodule.mem_top
        obtain ⟨harmonic, hHarmonic⟩ := hRange
        have hValue : harmonic.1 = polynomial.1 :=
          congrArg Subtype.val hHarmonic
        rw [← hValue]
        exact solidHarmonicGradient_mem_signedGlobalSmoothRange
          period hPeriod degree harmonic sector circleMode
      · obtain ⟨radialDegree, rfl⟩ :
            ∃ radialDegree : Nat, degree = radialDegree + 2 := by
          exact ⟨degree - 2, by omega⟩
        obtain ⟨harmonic, radial, hDecomposition⟩ :=
          solidFischer_exists_harmonic_add_radial
            radialDegree polynomial
        have hHarmonic :
            solidPolynomialTangentSection
                period hPeriod
                (solidPolynomialGradient harmonic.1)
                sector circleMode ∈
              signedGlobalSmoothRange period hPeriod :=
          solidHarmonicGradient_mem_signedGlobalSmoothRange
            period hPeriod (radialDegree + 2)
            harmonic sector circleMode
        have hRadial :
            solidPolynomialTangentSection
                period hPeriod
                (solidPolynomialGradient radial.1)
                sector circleMode ∈
              signedGlobalSmoothRange period hPeriod :=
          inductionHypothesis radialDegree (by omega) radial
        rw [hDecomposition, solidPolynomialGradient_add,
          solidPolynomialTangentSection_add,
          solidPolynomialTangentSection_gradient_radiusSquared_mul]
        exact
          (signedGlobalSmoothRange period hPeriod).add_mem
            hHarmonic hRadial

theorem solidPolynomialGradient_mem_signedGlobalSmoothRange
    (polynomial : SolidPolynomial)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (solidPolynomialGradient polynomial)
        sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  change
    solidPolynomialGradientTangentLinearMap
        period hPeriod sector circleMode polynomial ∈
      signedGlobalSmoothRange period hPeriod
  rw [← polynomial.sum_homogeneousComponent, map_sum]
  apply Submodule.sum_mem
  intro degree _
  exact solidHomogeneousGradient_mem_signedGlobalSmoothRange
    period hPeriod degree
    ⟨polynomial.homogeneousComponent degree,
      MvPolynomial.homogeneousComponent_isHomogeneous
        degree polynomial⟩
    sector circleMode

theorem solidPolynomialCurl_eq_zero_of_homogeneous_zero
    (vector : SolidPolynomialVector)
    (hVector : ∀ coordinate, (vector coordinate).IsHomogeneous 0) :
    solidPolynomialCurl vector = 0 := by
  have hDerivative (component coordinate : Fin 3) :
      MvPolynomial.pderiv coordinate (vector component) = 0 := by
    have hTotalDegree :
        (vector component).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr
        (hVector component)
    have hConstant :
        vector component =
          MvPolynomial.C ((vector component).coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hTotalDegree
    rw [hConstant, MvPolynomial.pderiv_C]
  funext coordinate
  fin_cases coordinate <;>
    simp [solidPolynomialCurl, hDerivative]

theorem solidHomogeneousTangent_mem_signedGlobalSmoothRange
    (degree : Nat) (vector : SolidPolynomialVector)
    (hVector :
      ∀ coordinate, (vector coordinate).IsHomogeneous degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod vector sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  induction degree using Nat.strong_induction_on generalizing vector with
  | h degree inductionHypothesis =>
      have hGradient :
          solidPolynomialTangentSection
              period hPeriod
              (solidPolynomialGradient (solidPolynomialDot vector))
              sector circleMode ∈
            signedGlobalSmoothRange period hPeriod :=
        solidPolynomialGradient_mem_signedGlobalSmoothRange
          period hPeriod (solidPolynomialDot vector)
          sector circleMode
      have hCurl :
          solidPolynomialTangentSection
              period hPeriod (solidPolynomialCurl vector)
              sector circleMode ∈
            signedGlobalSmoothRange period hPeriod := by
        by_cases hZero : degree = 0
        · subst degree
          rw [solidPolynomialCurl_eq_zero_of_homogeneous_zero
            vector hVector]
          have hTangentZero :
              solidPolynomialTangentSection
                  period hPeriod 0 sector circleMode =
                0 := by
            unfold solidPolynomialTangentSection
            simp [solidPolynomialSection_zero]
          rw [hTangentZero]
          exact Submodule.zero_mem _
        · have hCurlHomogeneous :
              ∀ coordinate,
                (solidPolynomialCurl vector coordinate).IsHomogeneous
                  (degree - 1) := by
            intro coordinate
            fin_cases coordinate <;>
              simp only [solidPolynomialCurl] <;>
              exact
                ((hVector _).pderiv).sub ((hVector _).pderiv)
          exact inductionHypothesis (degree - 1)
            (Nat.sub_lt (Nat.zero_lt_of_ne_zero hZero) (by omega))
            (solidPolynomialCurl vector) hCurlHomogeneous
      rw [solidPolynomialTangentSection_homotopy
        period hPeriod degree vector hVector sector circleMode]
      exact
        (signedGlobalSmoothRange period hPeriod).smul_mem _
          ((signedGlobalSmoothRange period hPeriod).add_mem
            hGradient
            ((signedGlobalSmoothRange period hPeriod).smul_mem _
              hCurl))

def solidPolynomialFrameLinearMap
    (state : SmoothSection period hPeriod) :
    SolidPolynomial →ₗ[Complex] SmoothSection period hPeriod where
  toFun polynomial :=
    solidPolynomialSection period hPeriod polynomial state
  map_add' first second :=
    solidPolynomialSection_add period hPeriod first second state
  map_smul' scalar polynomial :=
    solidPolynomialSection_smul
      period hPeriod scalar polynomial state

@[simp]
theorem solidPolynomialFrameLinearMap_apply
    (polynomial : SolidPolynomial)
    (state : SmoothSection period hPeriod) :
    solidPolynomialFrameLinearMap period hPeriod state polynomial =
      solidPolynomialSection period hPeriod polynomial state :=
  rfl

theorem solidPolynomialTangentSection_single
    (coordinate : Fin 3) (polynomial : SolidPolynomial)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialTangentSection
        period hPeriod (Pi.single coordinate polynomial)
        sector circleMode =
      solidPolynomialSection
        period hPeriod polynomial
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode) := by
  classical
  unfold solidPolynomialTangentSection
  rw [Finset.sum_eq_single coordinate]
  · simp
  · intro other _ hOther
    rw [Pi.single_apply, if_neg hOther,
      solidPolynomialSection_zero]
  · simp

theorem solidPolynomialTangentialFrame_mem_signedGlobalSmoothRange
    (polynomial : SolidPolynomial) (coordinate : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialSection
        period hPeriod polynomial
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode) ∈
      signedGlobalSmoothRange period hPeriod := by
  change
    solidPolynomialFrameLinearMap
        period hPeriod
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode)
        polynomial ∈
      signedGlobalSmoothRange period hPeriod
  rw [← polynomial.sum_homogeneousComponent, map_sum]
  apply Submodule.sum_mem
  intro degree _
  let vector : SolidPolynomialVector :=
    Pi.single coordinate (polynomial.homogeneousComponent degree)
  have hVector :
      ∀ direction, (vector direction).IsHomogeneous degree := by
    intro direction
    classical
    by_cases hDirection : direction = coordinate
    · subst direction
      simpa [vector, Pi.single_apply] using
        MvPolynomial.homogeneousComponent_isHomogeneous
          degree polynomial
    · simp [vector, hDirection,
        MvPolynomial.isHomogeneous_zero]
  have hMembership :=
    solidHomogeneousTangent_mem_signedGlobalSmoothRange
      period hPeriod degree vector hVector sector circleMode
  rw [solidPolynomialTangentSection_single] at hMembership
  exact hMembership

def solidHarmonicGeometricPacketScalarSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  solidPolynomialSection
    period hPeriod
    (primitiveSpinCSolidHarmonicGeometricPacket
      (positiveLevel + 1) multiplicity)
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode)

theorem solidHarmonicGeometricPacket_scalar_apply_movingWitness
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    (show D9DoubledMatterFiber from
      solidHarmonicGeometricPacketScalarSection
        period hPeriod positiveLevel multiplicity sector circleMode
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)) =
      (show D9DoubledMatterFiber from
        primitiveSpinCNullPowerSection
          period hPeriod
          (primitiveSpinCNullGeometricParameter
            positiveLevel multiplicity)
          sector circleMode (positiveLevel + 1)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) := by
  rw [solidHarmonicGeometricPacketScalarSection,
    solidPolynomialSection_apply,
    primitiveSpinCNullPowerSection_apply_movingWitness]
  simp_rw [primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  congr 1
  apply congrArg d9PrimitiveSpinCComplexActionCLM
  unfold primitiveSpinCSolidHarmonicGeometricPacket
    primitiveSpinCNullGeometricParameter
  exact primitiveSpinCSolidHarmonicPacket_eval_sphere
    (positiveLevel + 1)
    (Fin.cast
      (primitiveSpinCSolidPacket_degeneracy_eq (positiveLevel + 1))
      multiplicity)
    point

theorem solidHarmonicGeometricPacket_scalarSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidHarmonicGeometricPacketScalarSection
        period hPeriod positiveLevel multiplicity sector circleMode =
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.scalarSection) := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidHarmonicGeometricPacketScalarSection
        period hPeriod positiveLevel multiplicity sector circleMode base) =
      (show D9DoubledMatterFiber from
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.scalarSection) base)
  obtain ⟨⟨point, time⟩, hBase⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  rw [← hBase]
  change
    (show D9DoubledMatterFiber from
      solidHarmonicGeometricPacketScalarSection
        period hPeriod positiveLevel multiplicity sector circleMode
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)) =
      (show D9DoubledMatterFiber from
        primitiveSpinCNullPowerSection
          period hPeriod
          (primitiveSpinCNullGeometricParameter
            positiveLevel multiplicity)
          sector circleMode (positiveLevel + 1)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))
  exact
    solidHarmonicGeometricPacket_scalar_apply_movingWitness
      period hPeriod positiveLevel multiplicity sector circleMode
      point time

theorem solidHarmonicGeometricPacketScalar_mem_signedGlobalSmoothRange
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidHarmonicGeometricPacketScalarSection
        period hPeriod positiveLevel multiplicity sector circleMode ∈
      signedGlobalSmoothRange period hPeriod := by
  rw [solidHarmonicGeometricPacket_scalarSection]
  exact nullHarmonicScalar_coe_mem_globalRange
    period hPeriod positiveLevel multiplicity sector circleMode

theorem solidPolynomialSection_one
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection period hPeriod 1 state = state := by
  apply DFunLike.ext _ _
  intro base
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection period hPeriod 1 state base) =
      (show D9DoubledMatterFiber from state base)
  rw [solidPolynomialSection_apply]
  simp

theorem solidHarmonicPacketScalar_mem_signedGlobalSmoothRange
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialSection
        period hPeriod
        (primitiveSpinCSolidHarmonicPacket degree multiplicity)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) ∈
      signedGlobalSmoothRange period hPeriod := by
  cases degree with
  | zero =>
      change
        solidPolynomialSection
            period hPeriod 1
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode) ∈
          signedGlobalSmoothRange period hPeriod
      rw [solidPolynomialSection_one]
      exact hopfZeroMode_coe_mem_globalRange
        period hPeriod sector circleMode
  | succ positiveLevel =>
      let physicalMultiplicity :
          Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) :=
        Fin.cast
          (primitiveSpinCSolidPacket_degeneracy_eq
            (positiveLevel + 1)).symm multiplicity
      have hPacket :
          primitiveSpinCSolidHarmonicGeometricPacket
              (positiveLevel + 1) physicalMultiplicity =
            primitiveSpinCSolidHarmonicPacket
              (positiveLevel + 1) multiplicity := by
        unfold primitiveSpinCSolidHarmonicGeometricPacket
          physicalMultiplicity
        congr 1
      rw [← hPacket]
      change
        solidHarmonicGeometricPacketScalarSection
            period hPeriod positiveLevel physicalMultiplicity
            sector circleMode ∈
          signedGlobalSmoothRange period hPeriod
      exact
        solidHarmonicGeometricPacketScalar_mem_signedGlobalSmoothRange
          period hPeriod positiveLevel physicalMultiplicity
          sector circleMode

theorem solidHarmonicScalar_mem_signedGlobalSmoothRange
    (degree : Nat)
    (harmonic : solidHarmonicHomogeneousSubmodule degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialSection
        period hPeriod harmonic.1
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) ∈
      signedGlobalSmoothRange period hPeriod := by
  let scalarMap :
      solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
        SmoothSection period hPeriod :=
    (solidPolynomialFrameLinearMap
      period hPeriod
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector circleMode)).comp
      (solidHarmonicHomogeneousSubmodule degree).subtype
  have hLe :
      Submodule.span Complex
          (Set.range (solidHarmonicPacketElement degree)) ≤
        (signedGlobalSmoothRange period hPeriod).comap scalarMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨multiplicity, rfl⟩
    change
      solidPolynomialSection
          period hPeriod
          (primitiveSpinCSolidHarmonicPacket degree multiplicity)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode) ∈
        signedGlobalSmoothRange period hPeriod
    exact solidHarmonicPacketScalar_mem_signedGlobalSmoothRange
      period hPeriod degree multiplicity sector circleMode
  rw [solidHarmonicPacketElement_span_eq_top] at hLe
  exact hLe Submodule.mem_top

theorem solidHomogeneousScalar_mem_signedGlobalSmoothRange
    (degree : Nat)
    (polynomial :
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialSection
        period hPeriod polynomial.1
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) ∈
      signedGlobalSmoothRange period hPeriod := by
  induction degree using Nat.strong_induction_on with
  | h degree inductionHypothesis =>
      by_cases hSmall : degree < 2
      · have hRange :
            polynomial ∈ solidHarmonicHomogeneousRange degree := by
          rw [solidHarmonicHomogeneousRange_eq_top_of_lt_two
            degree hSmall]
          exact Submodule.mem_top
        obtain ⟨harmonic, hHarmonic⟩ := hRange
        have hValue : harmonic.1 = polynomial.1 :=
          congrArg Subtype.val hHarmonic
        rw [← hValue]
        exact solidHarmonicScalar_mem_signedGlobalSmoothRange
          period hPeriod degree harmonic sector circleMode
      · obtain ⟨radialDegree, rfl⟩ :
            ∃ radialDegree : Nat, degree = radialDegree + 2 := by
          exact ⟨degree - 2, by omega⟩
        obtain ⟨harmonic, radial, hDecomposition⟩ :=
          solidFischer_exists_harmonic_add_radial
            radialDegree polynomial
        have hHarmonic :=
          solidHarmonicScalar_mem_signedGlobalSmoothRange
            period hPeriod (radialDegree + 2)
            harmonic sector circleMode
        have hRadial :=
          inductionHypothesis radialDegree (by omega) radial
        rw [hDecomposition, solidPolynomialSection_add,
          solidPolynomialSection_radiusSquared_mul]
        exact
          (signedGlobalSmoothRange period hPeriod).add_mem
            hHarmonic hRadial

theorem solidPolynomialScalar_mem_signedGlobalSmoothRange
    (polynomial : SolidPolynomial)
    (sector : NormalRootChoice) (circleMode : Int) :
    solidPolynomialSection
        period hPeriod polynomial
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) ∈
      signedGlobalSmoothRange period hPeriod := by
  change
    solidPolynomialFrameLinearMap
        period hPeriod
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode)
        polynomial ∈
      signedGlobalSmoothRange period hPeriod
  rw [← polynomial.sum_homogeneousComponent, map_sum]
  apply Submodule.sum_mem
  intro degree _
  exact solidHomogeneousScalar_mem_signedGlobalSmoothRange
    period hPeriod degree
    ⟨polynomial.homogeneousComponent degree,
      MvPolynomial.homogeneousComponent_isHomogeneous
        degree polynomial⟩
    sector circleMode

theorem smoothSection_value_eq_of_localCoordinate_eq
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (first second : SmoothSection period hPeriod)
    (hLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base first =
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base second) :
    first base = second base := by
  let trivialization :=
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter).localTriv index
  apply
    (trivialization.linearEquivAt Real base hBase).injective
  simpa [trivialization,
    primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
      period hPeriod index base hBase] using hLocal

theorem complexScalarSection_value_eq_action
    (scalar : Complex) (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (show D9DoubledMatterFiber from
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar state base) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (show D9DoubledMatterFiber from state base) := by
  rw [d9PrimitiveSpinCComplexScalarSection_apply,
    d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]

def signedHopfSeedCoefficient
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) : Complex :=
  (8 : Complex)⁻¹ *
    d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod .positiveQuarter
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0)
      state base

def signedHopfTangentCoefficient
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice) (coordinate : Fin 3)
    (base : MappingTorus (fixedEquatorData period hPeriod)) : Complex :=
  (16 : Complex)⁻¹ *
    d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod .positiveQuarter
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector 0)
      state base

def hopfSectorFiberReconstruction
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM
      (signedHopfSeedCoefficient
        period hPeriod state sector base)
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0 base) +
    ∑ coordinate : Fin 3,
      d9PrimitiveSpinCComplexActionCLM
          (signedHopfTangentCoefficient
            period hPeriod state sector coordinate base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector 0 base)

def hopfSectorConstantReconstruction
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCComplexScalarSection
      period hPeriod .positiveQuarter
      (signedHopfSeedCoefficient
        period hPeriod state sector base)
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0) +
    ∑ coordinate : Fin 3,
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter
        (signedHopfTangentCoefficient
          period hPeriod state sector coordinate base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector 0)

theorem hopfSectorConstantReconstruction_apply
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (show D9DoubledMatterFiber from
      hopfSectorConstantReconstruction
        period hPeriod state sector base base) =
      hopfSectorFiberReconstruction
        period hPeriod state sector base := by
  unfold hopfSectorConstantReconstruction
    hopfSectorFiberReconstruction
  change
    (show D9DoubledMatterFiber from
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter
        (signedHopfSeedCoefficient
          period hPeriod state sector base)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector 0) base) +
      ∑ coordinate : Fin 3,
        (show D9DoubledMatterFiber from
          d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (signedHopfTangentCoefficient
              period hPeriod state sector coordinate base)
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod coordinate sector 0) base) =
      _
  simp_rw [complexScalarSection_value_eq_action period hPeriod]

def signedHopfFiberReconstruction
    (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    D9DoubledMatterFiber :=
  hopfSectorFiberReconstruction
      period hPeriod state .positiveQuarter base +
    hopfSectorFiberReconstruction
      period hPeriod state .negativeQuarter base

def signedHopfConstantReconstruction
    (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    SmoothSection period hPeriod :=
  hopfSectorConstantReconstruction
      period hPeriod state .positiveQuarter base +
    hopfSectorConstantReconstruction
      period hPeriod state .negativeQuarter base

theorem signedHopfConstantReconstruction_apply
    (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (show D9DoubledMatterFiber from
      signedHopfConstantReconstruction
        period hPeriod state base base) =
      signedHopfFiberReconstruction
        period hPeriod state base := by
  change
    (show D9DoubledMatterFiber from
      hopfSectorConstantReconstruction
        period hPeriod state .positiveQuarter base base) +
      (show D9DoubledMatterFiber from
        hopfSectorConstantReconstruction
          period hPeriod state .negativeQuarter base base) =
      _
  rw [hopfSectorConstantReconstruction_apply,
    hopfSectorConstantReconstruction_apply]
  rfl

theorem hopfSectorConstantReconstruction_localCoordinate_moving
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice)
    (point : MonopoleSphere) (time : Real)
    (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (hopfSectorConstantReconstruction
          period hPeriod state sector
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)) =
      localHopfFrameReconstruction
          period hPeriod point chart sector 0 time
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCNullPacketMovingWitnessIndexAt
              period hPeriod point time chart)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
            state) := by
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let base :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  unfold hopfSectorConstantReconstruction
  simp only [map_add, map_sum]
  simp_rw [
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      hBase]
  rw [localHopfFrameReconstruction_apply]
  unfold signedHopfSeedCoefficient signedHopfTangentCoefficient
  simp_rw [d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    hBase]
  rfl

theorem smoothSection_signedHopfFiberReconstruction
    (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (show D9DoubledMatterFiber from state base) =
      signedHopfFiberReconstruction
        period hPeriod state base := by
  obtain ⟨⟨point, time⟩, hBaseValue⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  subst base
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let movingBase :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      movingBase ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  have hLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase state =
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase
          (signedHopfConstantReconstruction
            period hPeriod state movingBase) := by
    rw [show
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index movingBase
            (signedHopfConstantReconstruction
              period hPeriod state movingBase) =
          localSignedHopfFrameReconstruction
              period hPeriod point chart 0 0 time
              (primitiveSpinCGeometricSectionLocalCoordinate
                period hPeriod index movingBase state) by
      unfold signedHopfConstantReconstruction
      rw [map_add,
        hopfSectorConstantReconstruction_localCoordinate_moving
          period hPeriod state .positiveQuarter point time chart hChart,
        hopfSectorConstantReconstruction_localCoordinate_moving
          period hPeriod state .negativeQuarter point time chart hChart]
      rfl]
    exact congrArg
      (fun operator :
          D9DoubledMatterFiber →ₗ[Complex] D9DoubledMatterFiber =>
        operator
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index movingBase state))
      (localSignedHopfFrameReconstruction_eq_id
        period hPeriod point chart hChart 0 0 time) |>.symm
  have hValue :=
    smoothSection_value_eq_of_localCoordinate_eq
      period hPeriod index movingBase hBase state
      (signedHopfConstantReconstruction
        period hPeriod state movingBase) hLocal
  rw [hValue,
    signedHopfConstantReconstruction_apply
      period hPeriod state movingBase]

theorem solidPolynomialSection_localCoordinate
    (polynomial : SolidPolynomial)
    (state : SmoothSection period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (solidPolynomialSection
          period hPeriod polynomial state) =
      d9PrimitiveSpinCComplexActionCLM
        (MvPolynomial.eval
          (fun coordinate =>
            (d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base : Complex))
          polynomial)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state) := by
  let scalar :=
    MvPolynomial.eval
      (fun coordinate =>
        (d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate base : Complex))
      polynomial
  rw [←
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod index base hBase scalar state]
  rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
      period hPeriod index base hBase,
    primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
      period hPeriod index base hBase]
  apply congrArg
    (fun value :
        D9PrimitiveSpinCFiber
          period hPeriod .positiveQuarter base =>
      ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod .positiveQuarter).localTriv index
        ⟨base, value⟩).2)
  change
      (show D9DoubledMatterFiber from
        solidPolynomialSection
          period hPeriod polynomial state base) =
        (show D9DoubledMatterFiber from
          d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state base)
  rw [solidPolynomialSection_apply,
    complexScalarSection_value_eq_action]

theorem localHopfFrameTangent_zero_time_mode_independent
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (firstMode secondMode : Int) :
    localHopfFrameTangent
        period hPeriod point chart sector firstMode 0 coordinate =
      localHopfFrameTangent
        period hPeriod point chart sector secondMode 0 coordinate := by
  unfold localHopfFrameTangent
  rw [primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_eq
      period hPeriod point chart hChart coordinate sector firstMode 0,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_eq
      period hPeriod point chart hChart coordinate sector secondMode 0]
  have hSeed :=
    localHopfFrameSeed_zero_time_mode_independent
      period hPeriod point chart hChart sector firstMode secondMode
  unfold localHopfFrameSeed at hSeed
  rw [hSeed]

theorem solidHarmonicPacket_eval_movingWitness
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (point : MonopoleSphere) (time : Real) :
    MvPolynomial.eval
        (fun coordinate =>
          (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time) : Complex))
        (primitiveSpinCSolidHarmonicPacket degree multiplicity) =
      solidHarmonicPacketSphereRestriction
        ⟨degree, multiplicity⟩ point := by
  rw [solidHarmonicPacketSphereRestriction_apply]
  simp_rw [primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  exact primitiveSpinCSolidHarmonicPacket_eval_sphere
    degree multiplicity point

theorem d9ThroatFourierMonopoleMode_mul_tangent_eq_solidPolynomial_local
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (fourierMode : Int)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice) (time : Real) :
    d9PrimitiveSpinCComplexActionCLM
        (d9ThroatFourierMonopoleMode period hPeriod
          ((⟨degree, multiplicity⟩ :
              SolidHarmonicPacketLabel), fourierMode)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))
        (localHopfFrameTangent
          period hPeriod point chart sector 0 time coordinate) =
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (solidPolynomialSection
          period hPeriod
          (primitiveSpinCSolidHarmonicPacket degree multiplicity)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector fourierMode)) := by
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let base :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  rw [solidPolynomialSection_localCoordinate
    period hPeriod _ _ index base hBase]
  rw [solidHarmonicPacket_eval_movingWitness]
  rw [d9ThroatFourierMonopoleMode_movingWitness]
  unfold localHopfFrameTangent
  rw [
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart coordinate sector 0 time,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart coordinate sector fourierMode time]
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  rw [mul_assoc,
    fourier_mul_normalRootSpinFrameExponential
      period hPeriod point fourierMode 0 time sector]
  have hTangent :=
    localHopfFrameTangent_zero_time_mode_independent
      period hPeriod point chart hChart coordinate sector 0 fourierMode
  unfold localHopfFrameTangent at hTangent
  rw [hTangent]
  simp

theorem d9ThroatFourierMonopoleMode_mul_seed_eq_solidPolynomial_local
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (fourierMode : Int)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (time : Real) :
    d9PrimitiveSpinCComplexActionCLM
        (d9ThroatFourierMonopoleMode period hPeriod
          ((⟨degree, multiplicity⟩ :
              SolidHarmonicPacketLabel), fourierMode)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))
        (localHopfFrameSeed
          period hPeriod point chart sector 0 time) =
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (solidPolynomialSection
          period hPeriod
          (primitiveSpinCSolidHarmonicPacket degree multiplicity)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector fourierMode)) := by
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let base :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  rw [solidPolynomialSection_localCoordinate
    period hPeriod _ _ index base hBase]
  rw [solidHarmonicPacket_eval_movingWitness]
  rw [d9ThroatFourierMonopoleMode_movingWitness]
  unfold localHopfFrameSeed
  rw [
    primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart sector 0 time,
    primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart sector fourierMode time]
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  rw [mul_assoc,
    fourier_mul_normalRootSpinFrameExponential
      period hPeriod point fourierMode 0 time sector]
  have hSeed :=
    localHopfFrameSeed_zero_time_mode_independent
      period hPeriod point chart hChart sector 0 fourierMode
  unfold localHopfFrameSeed at hSeed
  rw [hSeed]
  simp

theorem d9ThroatFourierMonopoleMode_mul_seed_eq_solidPolynomial
    (label : FourierMonopoleLabel)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    d9PrimitiveSpinCComplexActionCLM
        (d9ThroatFourierMonopoleMode
          period hPeriod label base)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector 0 base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection
          period hPeriod
          (primitiveSpinCSolidHarmonicPacket
            label.1.1 label.1.2)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector label.2) base) := by
  obtain ⟨⟨point, time⟩, hBaseValue⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  subst base
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let movingBase :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      movingBase ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  let left : SmoothSection period hPeriod :=
    d9PrimitiveSpinCComplexScalarSection
      period hPeriod .positiveQuarter
      (d9ThroatFourierMonopoleMode
        period hPeriod label movingBase)
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0)
  let right : SmoothSection period hPeriod :=
    solidPolynomialSection
      period hPeriod
      (primitiveSpinCSolidHarmonicPacket
        label.1.1 label.1.2)
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector label.2)
  have hLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase left =
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase right := by
    unfold left right
    rw [
      primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
        period hPeriod index movingBase hBase]
    exact
      d9ThroatFourierMonopoleMode_mul_seed_eq_solidPolynomial_local
        period hPeriod label.1.1 label.1.2 label.2
        point chart hChart sector time
  have hValue :=
    smoothSection_value_eq_of_localCoordinate_eq
      period hPeriod index movingBase hBase left right hLocal
  change
    (show D9DoubledMatterFiber from left movingBase) =
      (show D9DoubledMatterFiber from right movingBase)
    at hValue
  rw [show
      (show D9DoubledMatterFiber from left movingBase) =
        d9PrimitiveSpinCComplexActionCLM
          (d9ThroatFourierMonopoleMode
            period hPeriod label movingBase)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector 0 movingBase) by
      unfold left
      exact complexScalarSection_value_eq_action
        period hPeriod _ _ _] at hValue
  simpa [movingBase, right] using hValue

theorem d9ThroatFourierMonopoleMode_mul_tangent_eq_solidPolynomial
    (label : FourierMonopoleLabel)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    d9PrimitiveSpinCComplexActionCLM
        (d9ThroatFourierMonopoleMode
          period hPeriod label base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector 0 base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection
          period hPeriod
          (primitiveSpinCSolidHarmonicPacket
            label.1.1 label.1.2)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector label.2) base) := by
  obtain ⟨⟨point, time⟩, hBaseValue⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  subst base
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let movingBase :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase :
      movingBase ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  let left : SmoothSection period hPeriod :=
    d9PrimitiveSpinCComplexScalarSection
      period hPeriod .positiveQuarter
      (d9ThroatFourierMonopoleMode
        period hPeriod label movingBase)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector 0)
  let right : SmoothSection period hPeriod :=
    solidPolynomialSection
      period hPeriod
      (primitiveSpinCSolidHarmonicPacket
        label.1.1 label.1.2)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector label.2)
  have hLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase left =
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index movingBase right := by
    unfold left right
    rw [
      primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
        period hPeriod index movingBase hBase]
    exact
      d9ThroatFourierMonopoleMode_mul_tangent_eq_solidPolynomial_local
        period hPeriod label.1.1 label.1.2 label.2
        point chart hChart coordinate sector time
  have hValue :=
    smoothSection_value_eq_of_localCoordinate_eq
      period hPeriod index movingBase hBase left right hLocal
  change
    (show D9DoubledMatterFiber from left movingBase) =
      (show D9DoubledMatterFiber from right movingBase)
    at hValue
  rw [show
      (show D9DoubledMatterFiber from left movingBase) =
        d9PrimitiveSpinCComplexActionCLM
          (d9ThroatFourierMonopoleMode
            period hPeriod label movingBase)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector 0 movingBase) by
      unfold left
      exact complexScalarSection_value_eq_action
        period hPeriod _ _ _] at hValue
  simpa [movingBase, right] using hValue

theorem d9ThroatFourierMonopoleSpan_frame_realization
    (frame : SmoothSection period hPeriod)
    (generator : FourierMonopoleLabel → SmoothSection period hPeriod)
    (hGeneratorRange :
      ∀ label,
        generator label ∈ signedGlobalSmoothRange period hPeriod)
    (hGeneratorApply :
      ∀ label base,
        (show D9DoubledMatterFiber from generator label base) =
          d9PrimitiveSpinCComplexActionCLM
            (d9ThroatFourierMonopoleMode
              period hPeriod label base)
            (show D9DoubledMatterFiber from frame base))
    (function :
      C(MappingTorus (fixedEquatorData period hPeriod), Complex))
    (hFunction :
      function ∈ d9ThroatFourierMonopoleSpan period hPeriod) :
    ∃ state : SmoothSection period hPeriod,
      state ∈ signedGlobalSmoothRange period hPeriod ∧
        ∀ base,
          (show D9DoubledMatterFiber from state base) =
            d9PrimitiveSpinCComplexActionCLM
              (function base)
              (show D9DoubledMatterFiber from frame base) := by
  refine Submodule.span_induction
    (p := fun function _ =>
      ∃ state : SmoothSection period hPeriod,
        state ∈ signedGlobalSmoothRange period hPeriod ∧
          ∀ base,
            (show D9DoubledMatterFiber from state base) =
              d9PrimitiveSpinCComplexActionCLM
                (function base)
                (show D9DoubledMatterFiber from frame base))
    ?_ ?_ ?_ ?_ hFunction
  · rintro _ ⟨label, rfl⟩
    exact ⟨generator label, hGeneratorRange label,
      hGeneratorApply label⟩
  · refine ⟨0, (signedGlobalSmoothRange period hPeriod).zero_mem, ?_⟩
    intro base
    change
      (0 : D9DoubledMatterFiber) =
        d9PrimitiveSpinCComplexActionCLM 0
          (show D9DoubledMatterFiber from frame base)
    rw [d9PrimitiveSpinCComplexActionCLM_zero]
  · intro first second _ _ hFirst hSecond
    obtain ⟨firstState, hFirstRange, hFirstApply⟩ := hFirst
    obtain ⟨secondState, hSecondRange, hSecondApply⟩ := hSecond
    refine
      ⟨firstState + secondState,
        (signedGlobalSmoothRange period hPeriod).add_mem
          hFirstRange hSecondRange, ?_⟩
    intro base
    change
      (show D9DoubledMatterFiber from firstState base) +
          (show D9DoubledMatterFiber from secondState base) =
        d9PrimitiveSpinCComplexActionCLM
          (first base + second base)
          (show D9DoubledMatterFiber from frame base)
    rw [hFirstApply base, hSecondApply base,
      d9PrimitiveSpinCComplexAction_add_scalar]
  · intro scalar function _ hState
    obtain ⟨state, hRange, hApply⟩ := hState
    refine
      ⟨scalar • state,
        (signedGlobalSmoothRange period hPeriod).smul_mem
          scalar hRange, ?_⟩
    intro base
    rw [d9PrimitiveSpinCGeometricL2_complex_smul]
    change
      (show D9DoubledMatterFiber from
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state base) =
        d9PrimitiveSpinCComplexActionCLM
          (scalar * function base)
          (show D9DoubledMatterFiber from frame base)
    rw [complexScalarSection_value_eq_action,
      hApply base, d9PrimitiveSpinCComplexAction_mul]

theorem d9ThroatFourierMonopoleSpan_seed_realization
    (sector : NormalRootChoice)
    (function :
      C(MappingTorus (fixedEquatorData period hPeriod), Complex))
    (hFunction :
      function ∈ d9ThroatFourierMonopoleSpan period hPeriod) :
    ∃ state : SmoothSection period hPeriod,
      state ∈ signedGlobalSmoothRange period hPeriod ∧
        ∀ base,
          (show D9DoubledMatterFiber from state base) =
            d9PrimitiveSpinCComplexActionCLM
              (function base)
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector 0 base) := by
  apply d9ThroatFourierMonopoleSpan_frame_realization
    period hPeriod
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector 0)
    (fun label =>
      solidPolynomialSection
        period hPeriod
        (primitiveSpinCSolidHarmonicPacket
          label.1.1 label.1.2)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector label.2))
  · intro label
    exact solidPolynomialScalar_mem_signedGlobalSmoothRange
      period hPeriod
      (primitiveSpinCSolidHarmonicPacket
        label.1.1 label.1.2)
      sector label.2
  · intro label base
    exact
      (d9ThroatFourierMonopoleMode_mul_seed_eq_solidPolynomial
        period hPeriod label sector base).symm
  · exact hFunction

theorem d9ThroatFourierMonopoleSpan_tangent_realization
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (function :
      C(MappingTorus (fixedEquatorData period hPeriod), Complex))
    (hFunction :
      function ∈ d9ThroatFourierMonopoleSpan period hPeriod) :
    ∃ state : SmoothSection period hPeriod,
      state ∈ signedGlobalSmoothRange period hPeriod ∧
        ∀ base,
          (show D9DoubledMatterFiber from state base) =
            d9PrimitiveSpinCComplexActionCLM
              (function base)
              (primitiveSpinCHopfFirstSphereTangentialSection
                period hPeriod coordinate sector 0 base) := by
  apply d9ThroatFourierMonopoleSpan_frame_realization
    period hPeriod
    (primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector 0)
    (fun label =>
      solidPolynomialSection
        period hPeriod
        (primitiveSpinCSolidHarmonicPacket
          label.1.1 label.1.2)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector label.2))
  · intro label
    exact solidPolynomialTangentialFrame_mem_signedGlobalSmoothRange
      period hPeriod
      (primitiveSpinCSolidHarmonicPacket
        label.1.1 label.1.2)
      coordinate sector label.2
  · intro label base
    exact
      (d9ThroatFourierMonopoleMode_mul_tangent_eq_solidPolynomial
        period hPeriod label coordinate sector base).symm
  · exact hFunction

def signedHopfSeedCoefficientContinuousMap
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice) :
    C(MappingTorus (fixedEquatorData period hPeriod), Complex) :=
  ⟨signedHopfSeedCoefficient period hPeriod state sector,
    continuous_const.mul
      (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector 0)
        state)⟩

def signedHopfTangentCoefficientContinuousMap
    (state : SmoothSection period hPeriod)
    (sector : NormalRootChoice) (coordinate : Fin 3) :
    C(MappingTorus (fixedEquatorData period hPeriod), Complex) :=
  ⟨signedHopfTangentCoefficient
      period hPeriod state sector coordinate,
    continuous_const.mul
      (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector 0)
        state)⟩

theorem d9ThroatFourierMonopoleSpan_exists_dist_lt
    (function :
      C(MappingTorus (fixedEquatorData period hPeriod), Complex))
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ approximation :
        C(MappingTorus (fixedEquatorData period hPeriod), Complex),
      approximation ∈
          d9ThroatFourierMonopoleSpan period hPeriod ∧
        dist approximation function < epsilon := by
  have hClosure :
      function ∈
        (d9ThroatFourierMonopoleSpan
          period hPeriod).topologicalClosure := by
    rw [d9ThroatFourierMonopoleSpan_closure_eq_top]
    exact Submodule.mem_top
  rw [← SetLike.mem_coe,
    Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hClosure
  obtain ⟨approximation, hApproximation, hDistance⟩ :=
    hClosure epsilon hEpsilon
  exact ⟨approximation, hApproximation,
    by simpa [dist_comm] using hDistance⟩

theorem d9DoubledMatterSpinorHermitianPairing_complexAction_self_re
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    (d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCComplexActionCLM scalar matter)
        (d9PrimitiveSpinCComplexActionCLM scalar matter)).re =
      Complex.normSq scalar *
        (d9DoubledMatterSpinorHermitianPairing matter matter).re := by
  have hImaginary :
      (d9DoubledMatterSpinorHermitianPairing matter matter).im = 0 := by
    have hConjugate :=
      congrArg Complex.im
        (d9DoubledMatterSpinorHermitianPairing_conj_symm
          matter matter)
    change
      -(d9DoubledMatterSpinorHermitianPairing matter matter).im =
        (d9DoubledMatterSpinorHermitianPairing matter matter).im
      at hConjugate
    linarith
  rw [d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right]
  simp [Complex.normSq_apply, Complex.mul_re, hImaginary]
  ring

theorem d9DoubledMatterSpinorHermitianPairing_add_self_re_le
    (first second : D9DoubledMatterFiber) :
    (d9DoubledMatterSpinorHermitianPairing
        (first + second) (first + second)).re ≤
      2 *
        ((d9DoubledMatterSpinorHermitianPairing
            first first).re +
          (d9DoubledMatterSpinorHermitianPairing
            second second).re) := by
  have hDifference :=
    d9DoubledMatterSpinorHermitianPairing_self_re_nonnegative
      (first - second)
  have hConjugate :=
    congrArg Complex.re
      (d9DoubledMatterSpinorHermitianPairing_conj_symm
        first second)
  rw [show first - second = first + (-second) by abel,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_neg_left,
    d9DoubledMatterSpinorHermitianPairing_neg_right,
    d9DoubledMatterSpinorHermitianPairing_neg_right,
    d9DoubledMatterSpinorHermitianPairing_neg_left] at hDifference
  simp only [Complex.add_re, Complex.neg_re] at hDifference
  change
    (d9DoubledMatterSpinorHermitianPairing first second).re =
      (d9DoubledMatterSpinorHermitianPairing second first).re
    at hConjugate
  rw [d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_right]
  change
    (d9DoubledMatterSpinorHermitianPairing first first).re +
          (d9DoubledMatterSpinorHermitianPairing first second).re +
        ((d9DoubledMatterSpinorHermitianPairing second first).re +
          (d9DoubledMatterSpinorHermitianPairing second second).re) ≤
      2 *
        ((d9DoubledMatterSpinorHermitianPairing first first).re +
          (d9DoubledMatterSpinorHermitianPairing second second).re)
  linarith

theorem primitiveSpinCHopfZeroMode_self_global
    (sector : NormalRootChoice) (circleMode : Int)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base) =
      8 := by
  obtain ⟨⟨point, time⟩, hBaseValue⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  subst base
  exact primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
    period hPeriod sector circleMode point time

theorem primitiveSpinCHopfTangent_self_re_le_eight
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (circleMode : Int)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base)).re ≤
      8 := by
  obtain ⟨⟨point, time⟩, hBaseValue⟩ :=
    nullPacketMovingWitnessBase_surjective period hPeriod base
  subst base
  rw [primitiveSpinCHopfZeroMode_tangential_pairing,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight]
  have hSphere := monopoleSphereCoordinate_sq_sum point
  fin_cases coordinate <;>
    simp [primitiveSpinCZeroModeTangentialPairingMatrix,
      d9PrimitiveSpinCBaseUnitRadialCoordinate,
      primitiveSpinCNullPacketMovingWitnessBase_coordinate] <;>
    nlinarith [sq_nonneg (monopoleSphereCoordinate point 0),
      sq_nonneg (monopoleSphereCoordinate point 1),
      sq_nonneg (monopoleSphereCoordinate point 2)]

theorem primitiveSpinCHopfSeed_scaled_self_re_le
    (error : Complex) (delta : Real)
    (hError : Complex.normSq error ≤ delta ^ 2)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCComplexActionCLM error
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector 0 base))
        (d9PrimitiveSpinCComplexActionCLM error
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector 0 base))).re ≤
      8 * delta ^ 2 := by
  rw [d9DoubledMatterSpinorHermitianPairing_complexAction_self_re,
    primitiveSpinCHopfZeroMode_self_global]
  norm_num at ⊢
  nlinarith

theorem primitiveSpinCHopfTangent_scaled_self_re_le
    (error : Complex) (delta : Real)
    (hError : Complex.normSq error ≤ delta ^ 2)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCComplexActionCLM error
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector 0 base))
        (d9PrimitiveSpinCComplexActionCLM error
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector 0 base))).re ≤
      8 * delta ^ 2 := by
  rw [d9DoubledMatterSpinorHermitianPairing_complexAction_self_re]
  have hFrame :=
    primitiveSpinCHopfTangent_self_re_le_eight
      period hPeriod coordinate sector 0 base
  have hNormSq := Complex.normSq_nonneg error
  nlinarith [sq_nonneg delta]

def hopfTangentFiberError
    (errors : Fin 3 → Complex)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    D9DoubledMatterFiber :=
  ∑ coordinate : Fin 3,
    d9PrimitiveSpinCComplexActionCLM
      (errors coordinate)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector 0 base)

theorem hopfTangentFiberError_self_re_le
    (errors : Fin 3 → Complex) (delta : Real)
    (hErrors :
      ∀ coordinate, Complex.normSq (errors coordinate) ≤ delta ^ 2)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (hopfTangentFiberError
          period hPeriod errors sector base)
        (hopfTangentFiberError
          period hPeriod errors sector base)).re ≤
      96 * delta ^ 2 := by
  let tangent : Fin 3 → D9DoubledMatterFiber :=
    fun coordinate =>
      d9PrimitiveSpinCComplexActionCLM
        (errors coordinate)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector 0 base)
  have hTerm (coordinate : Fin 3) :
      (d9DoubledMatterSpinorHermitianPairing
          (tangent coordinate) (tangent coordinate)).re ≤
        8 * delta ^ 2 :=
    primitiveSpinCHopfTangent_scaled_self_re_le
      period hPeriod (errors coordinate) delta
      (hErrors coordinate) coordinate sector base
  have hOneTwo :=
    d9DoubledMatterSpinorHermitianPairing_add_self_re_le
      (tangent 1) (tangent 2)
  have hAll :=
    d9DoubledMatterSpinorHermitianPairing_add_self_re_le
      (tangent 0) (tangent 1 + tangent 2)
  unfold hopfTangentFiberError
  rw [Fin.sum_univ_three]
  change
    (d9DoubledMatterSpinorHermitianPairing
        (tangent 0 + tangent 1 + tangent 2)
        (tangent 0 + tangent 1 + tangent 2)).re ≤
      96 * delta ^ 2
  rw [add_assoc]
  nlinarith [hTerm 0, hTerm 1, hTerm 2, sq_nonneg delta]

def hopfSectorFiberError
    (seedError : Complex) (tangentErrors : Fin 3 → Complex)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM seedError
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0 base) +
    hopfTangentFiberError
      period hPeriod tangentErrors sector base

theorem hopfSectorFiberError_self_re_le
    (seedError : Complex) (tangentErrors : Fin 3 → Complex)
    (delta : Real)
    (hSeed : Complex.normSq seedError ≤ delta ^ 2)
    (hTangent :
      ∀ coordinate,
        Complex.normSq (tangentErrors coordinate) ≤ delta ^ 2)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (hopfSectorFiberError
          period hPeriod seedError tangentErrors sector base)
        (hopfSectorFiberError
          period hPeriod seedError tangentErrors sector base)).re ≤
      256 * delta ^ 2 := by
  let seed :=
    d9PrimitiveSpinCComplexActionCLM seedError
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector 0 base)
  let tangent :=
    hopfTangentFiberError
      period hPeriod tangentErrors sector base
  have hSeedBound :=
    primitiveSpinCHopfSeed_scaled_self_re_le
      period hPeriod seedError delta hSeed sector base
  have hTangentBound :=
    hopfTangentFiberError_self_re_le
      period hPeriod tangentErrors delta hTangent sector base
  have hAdd :=
    d9DoubledMatterSpinorHermitianPairing_add_self_re_le
      seed tangent
  change
    (d9DoubledMatterSpinorHermitianPairing
        (seed + tangent) (seed + tangent)).re ≤
      256 * delta ^ 2
  nlinarith [sq_nonneg delta]

def signedHopfFiberError
    (positiveSeedError negativeSeedError : Complex)
    (positiveTangentErrors negativeTangentErrors : Fin 3 → Complex)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    D9DoubledMatterFiber :=
  hopfSectorFiberError period hPeriod
      positiveSeedError positiveTangentErrors .positiveQuarter base +
    hopfSectorFiberError period hPeriod
      negativeSeedError negativeTangentErrors .negativeQuarter base

theorem signedHopfFiberError_self_re_le
    (positiveSeedError negativeSeedError : Complex)
    (positiveTangentErrors negativeTangentErrors : Fin 3 → Complex)
    (delta : Real)
    (hPositiveSeed :
      Complex.normSq positiveSeedError ≤ delta ^ 2)
    (hNegativeSeed :
      Complex.normSq negativeSeedError ≤ delta ^ 2)
    (hPositiveTangent :
      ∀ coordinate,
        Complex.normSq (positiveTangentErrors coordinate) ≤ delta ^ 2)
    (hNegativeTangent :
      ∀ coordinate,
        Complex.normSq (negativeTangentErrors coordinate) ≤ delta ^ 2)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    (d9DoubledMatterSpinorHermitianPairing
        (signedHopfFiberError period hPeriod
          positiveSeedError negativeSeedError
          positiveTangentErrors negativeTangentErrors base)
        (signedHopfFiberError period hPeriod
          positiveSeedError negativeSeedError
          positiveTangentErrors negativeTangentErrors base)).re ≤
      1024 * delta ^ 2 := by
  let positive :=
    hopfSectorFiberError period hPeriod
      positiveSeedError positiveTangentErrors .positiveQuarter base
  let negative :=
    hopfSectorFiberError period hPeriod
      negativeSeedError negativeTangentErrors .negativeQuarter base
  have hPositive :=
    hopfSectorFiberError_self_re_le
      period hPeriod positiveSeedError positiveTangentErrors delta
      hPositiveSeed hPositiveTangent .positiveQuarter base
  have hNegative :=
    hopfSectorFiberError_self_re_le
      period hPeriod negativeSeedError negativeTangentErrors delta
      hNegativeSeed hNegativeTangent .negativeQuarter base
  have hAdd :=
    d9DoubledMatterSpinorHermitianPairing_add_self_re_le
      positive negative
  change
    (d9DoubledMatterSpinorHermitianPairing
        (positive + negative) (positive + negative)).re ≤
      1024 * delta ^ 2
  nlinarith [sq_nonneg delta]

theorem d9PrimitiveSpinCComplexAction_sub_scalar
    (first second : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (first - second) matter =
      d9PrimitiveSpinCComplexActionCLM first matter -
        d9PrimitiveSpinCComplexActionCLM second matter := by
  rw [sub_eq_add_neg,
    d9PrimitiveSpinCComplexAction_add_scalar]
  rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im,
    d9PrimitiveSpinCComplexActionCLM_eq_re_add_im,
    d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  simp
  abel

theorem hopfTangentFiberError_sub
    (first second : Fin 3 → Complex)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    hopfTangentFiberError period hPeriod first sector base -
        hopfTangentFiberError period hPeriod second sector base =
      hopfTangentFiberError period hPeriod
        (fun coordinate => first coordinate - second coordinate)
        sector base := by
  unfold hopfTangentFiberError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [d9PrimitiveSpinCComplexAction_sub_scalar]

theorem hopfSectorFiberError_sub
    (firstSeed secondSeed : Complex)
    (firstTangent secondTangent : Fin 3 → Complex)
    (sector : NormalRootChoice)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    hopfSectorFiberError period hPeriod
          firstSeed firstTangent sector base -
        hopfSectorFiberError period hPeriod
          secondSeed secondTangent sector base =
      hopfSectorFiberError period hPeriod
        (firstSeed - secondSeed)
        (fun coordinate =>
          firstTangent coordinate - secondTangent coordinate)
        sector base := by
  unfold hopfSectorFiberError
  rw [d9PrimitiveSpinCComplexAction_sub_scalar,
    ← hopfTangentFiberError_sub]
  abel

theorem signedHopfFiberError_sub
    (firstPositiveSeed firstNegativeSeed : Complex)
    (firstPositiveTangent firstNegativeTangent : Fin 3 → Complex)
    (secondPositiveSeed secondNegativeSeed : Complex)
    (secondPositiveTangent secondNegativeTangent : Fin 3 → Complex)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    signedHopfFiberError period hPeriod
          firstPositiveSeed firstNegativeSeed
          firstPositiveTangent firstNegativeTangent base -
        signedHopfFiberError period hPeriod
          secondPositiveSeed secondNegativeSeed
          secondPositiveTangent secondNegativeTangent base =
      signedHopfFiberError period hPeriod
        (firstPositiveSeed - secondPositiveSeed)
        (firstNegativeSeed - secondNegativeSeed)
        (fun coordinate =>
          firstPositiveTangent coordinate -
            secondPositiveTangent coordinate)
        (fun coordinate =>
          firstNegativeTangent coordinate -
            secondNegativeTangent coordinate)
        base := by
  unfold signedHopfFiberError
  rw [← hopfSectorFiberError_sub,
    ← hopfSectorFiberError_sub]
  abel

theorem signedHopfFiberReconstruction_eq_error
    (state : SmoothSection period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    signedHopfFiberReconstruction period hPeriod state base =
      signedHopfFiberError period hPeriod
        (signedHopfSeedCoefficient
          period hPeriod state .positiveQuarter base)
        (signedHopfSeedCoefficient
          period hPeriod state .negativeQuarter base)
        (fun coordinate =>
          signedHopfTangentCoefficient
            period hPeriod state .positiveQuarter coordinate base)
        (fun coordinate =>
          signedHopfTangentCoefficient
            period hPeriod state .negativeQuarter coordinate base)
        base := by
  rfl

theorem continuousMap_pointwise_sub_normSq_le
    (first second :
      C(MappingTorus (fixedEquatorData period hPeriod), Complex))
    (delta : Real) (hDistance : dist first second < delta)
    (base : MappingTorus (fixedEquatorData period hPeriod)) :
    Complex.normSq (second base - first base) ≤ delta ^ 2 := by
  have hPointwise :
      dist (first base) (second base) < delta :=
    lt_of_le_of_lt
      (ContinuousMap.dist_apply_le_dist
        (f := first) (g := second) base)
      hDistance
  have hNorm :
      ‖second base - first base‖ < delta := by
    simpa [dist_eq_norm, norm_sub_rev] using hPointwise
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (second base - first base)]

theorem primitiveSpinCFourierMonopoleCoreComplete_proved :
    PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod := by
  intro state
  rw [Metric.mem_closure_iff]
  intro epsilon hEpsilon
  let volume :=
    (intrinsicCanonicalThroatVolumeMeasure
      period hPeriod).real Set.univ
  let denominator := 64 * (volume + 1)
  let delta := epsilon / denominator
  have hVolume : 0 ≤ volume := MeasureTheory.measureReal_nonneg
  have hDenominator : 0 < denominator := by
    unfold denominator
    positivity
  have hDelta : 0 < delta := by
    exact div_pos hEpsilon hDenominator
  have hSeedApproximationExists :
      ∀ sector : NormalRootChoice,
        ∃ approximation :
            C(MappingTorus
              (fixedEquatorData period hPeriod), Complex),
          approximation ∈
              d9ThroatFourierMonopoleSpan period hPeriod ∧
            dist approximation
              (signedHopfSeedCoefficientContinuousMap
                period hPeriod state sector) < delta := by
    intro sector
    exact d9ThroatFourierMonopoleSpan_exists_dist_lt
      period hPeriod
      (signedHopfSeedCoefficientContinuousMap
        period hPeriod state sector)
      delta hDelta
  choose seedApproximation hSeedApproximationRange
    hSeedApproximationDistance using hSeedApproximationExists
  have hTangentApproximationExists :
      ∀ sector : NormalRootChoice, ∀ coordinate : Fin 3,
        ∃ approximation :
            C(MappingTorus
              (fixedEquatorData period hPeriod), Complex),
          approximation ∈
              d9ThroatFourierMonopoleSpan period hPeriod ∧
            dist approximation
              (signedHopfTangentCoefficientContinuousMap
                period hPeriod state sector coordinate) < delta := by
    intro sector coordinate
    exact d9ThroatFourierMonopoleSpan_exists_dist_lt
      period hPeriod
      (signedHopfTangentCoefficientContinuousMap
        period hPeriod state sector coordinate)
      delta hDelta
  choose tangentApproximation hTangentApproximationRange
    hTangentApproximationDistance using hTangentApproximationExists
  have hSeedRealization :
      ∀ sector : NormalRootChoice,
        ∃ realizedSection : SmoothSection period hPeriod,
          realizedSection ∈ signedGlobalSmoothRange period hPeriod ∧
            ∀ base,
              (show D9DoubledMatterFiber from realizedSection base) =
                d9PrimitiveSpinCComplexActionCLM
                  (seedApproximation sector base)
                  (primitiveSpinCHopfZeroModeSection
                    period hPeriod sector 0 base) := by
    intro sector
    exact d9ThroatFourierMonopoleSpan_seed_realization
      period hPeriod sector
      (seedApproximation sector)
      (hSeedApproximationRange sector)
  choose seedSection hSeedSectionRange hSeedSectionApply
    using hSeedRealization
  have hTangentRealization :
      ∀ sector : NormalRootChoice, ∀ coordinate : Fin 3,
        ∃ realizedSection : SmoothSection period hPeriod,
          realizedSection ∈ signedGlobalSmoothRange period hPeriod ∧
            ∀ base,
              (show D9DoubledMatterFiber from realizedSection base) =
                d9PrimitiveSpinCComplexActionCLM
                  (tangentApproximation sector coordinate base)
                  (primitiveSpinCHopfFirstSphereTangentialSection
                    period hPeriod coordinate sector 0 base) := by
    intro sector coordinate
    exact d9ThroatFourierMonopoleSpan_tangent_realization
      period hPeriod coordinate sector
      (tangentApproximation sector coordinate)
      (hTangentApproximationRange sector coordinate)
  choose tangentSection hTangentSectionRange hTangentSectionApply
    using hTangentRealization
  let approximation : SmoothSection period hPeriod :=
    (seedSection .positiveQuarter +
        ∑ coordinate : Fin 3,
          tangentSection .positiveQuarter coordinate) +
      (seedSection .negativeQuarter +
        ∑ coordinate : Fin 3,
          tangentSection .negativeQuarter coordinate)
  have hApproximationRange :
      approximation ∈ signedGlobalSmoothRange period hPeriod := by
    unfold approximation
    apply (signedGlobalSmoothRange period hPeriod).add_mem
    · apply (signedGlobalSmoothRange period hPeriod).add_mem
      · exact hSeedSectionRange .positiveQuarter
      · apply Submodule.sum_mem
        intro coordinate _
        exact hTangentSectionRange .positiveQuarter coordinate
    · apply (signedGlobalSmoothRange period hPeriod).add_mem
      · exact hSeedSectionRange .negativeQuarter
      · apply Submodule.sum_mem
        intro coordinate _
        exact hTangentSectionRange .negativeQuarter coordinate
  have hApproximationApply
      (base : MappingTorus (fixedEquatorData period hPeriod)) :
      (show D9DoubledMatterFiber from approximation base) =
        signedHopfFiberError period hPeriod
          (seedApproximation .positiveQuarter base)
          (seedApproximation .negativeQuarter base)
          (fun coordinate =>
            tangentApproximation
              .positiveQuarter coordinate base)
          (fun coordinate =>
            tangentApproximation
              .negativeQuarter coordinate base)
          base := by
    unfold approximation signedHopfFiberError
      hopfSectorFiberError hopfTangentFiberError
    change
      ((show D9DoubledMatterFiber from
          seedSection .positiveQuarter base) +
          ∑ coordinate : Fin 3,
            (show D9DoubledMatterFiber from
              tangentSection .positiveQuarter coordinate base)) +
        ((show D9DoubledMatterFiber from
          seedSection .negativeQuarter base) +
          ∑ coordinate : Fin 3,
            (show D9DoubledMatterFiber from
              tangentSection .negativeQuarter coordinate base)) =
        _
    simp_rw [hSeedSectionApply, hTangentSectionApply]
  have hErrorApply
      (base : MappingTorus (fixedEquatorData period hPeriod)) :
      (show D9DoubledMatterFiber from
        (state - approximation) base) =
        signedHopfFiberError period hPeriod
          (signedHopfSeedCoefficient period hPeriod state
              .positiveQuarter base -
            seedApproximation .positiveQuarter base)
          (signedHopfSeedCoefficient period hPeriod state
              .negativeQuarter base -
            seedApproximation .negativeQuarter base)
          (fun coordinate =>
            signedHopfTangentCoefficient period hPeriod state
                .positiveQuarter coordinate base -
              tangentApproximation
                .positiveQuarter coordinate base)
          (fun coordinate =>
            signedHopfTangentCoefficient period hPeriod state
                .negativeQuarter coordinate base -
              tangentApproximation
                .negativeQuarter coordinate base)
          base := by
    change
      (show D9DoubledMatterFiber from state base) -
          (show D9DoubledMatterFiber from approximation base) =
        _
    rw [smoothSection_signedHopfFiberReconstruction,
      signedHopfFiberReconstruction_eq_error,
      hApproximationApply,
      signedHopfFiberError_sub]
  have hSeedNormSq
      (sector : NormalRootChoice)
      (base : MappingTorus (fixedEquatorData period hPeriod)) :
      Complex.normSq
          (signedHopfSeedCoefficient
              period hPeriod state sector base -
            seedApproximation sector base) ≤
        delta ^ 2 := by
    exact continuousMap_pointwise_sub_normSq_le
      period hPeriod
      (seedApproximation sector)
      (signedHopfSeedCoefficientContinuousMap
        period hPeriod state sector)
      delta (hSeedApproximationDistance sector) base
  have hTangentNormSq
      (sector : NormalRootChoice) (coordinate : Fin 3)
      (base : MappingTorus (fixedEquatorData period hPeriod)) :
      Complex.normSq
          (signedHopfTangentCoefficient
              period hPeriod state sector coordinate base -
            tangentApproximation sector coordinate base) ≤
        delta ^ 2 := by
    exact continuousMap_pointwise_sub_normSq_le
      period hPeriod
      (tangentApproximation sector coordinate)
      (signedHopfTangentCoefficientContinuousMap
        period hPeriod state sector coordinate)
      delta (hTangentApproximationDistance sector coordinate) base
  have hDensity
      (base : MappingTorus (fixedEquatorData period hPeriod)) :
      d9PrimitiveSpinCGeometricL2Density
          period hPeriod .positiveQuarter
          (state - approximation) base ≤
        1024 * delta ^ 2 := by
    unfold d9PrimitiveSpinCGeometricL2Density
      d9PrimitiveSpinCPointwiseHermitianPairing
    rw [hErrorApply]
    exact signedHopfFiberError_self_re_le
      period hPeriod _ _ _ _ delta
      (hSeedNormSq .positiveQuarter base)
      (hSeedNormSq .negativeQuarter base)
      (fun coordinate =>
        hTangentNormSq .positiveQuarter coordinate base)
      (fun coordinate =>
        hTangentNormSq .negativeQuarter coordinate base)
      base
  have hNormSq :
      ‖state - approximation‖ ^ 2 ≤
        1024 * delta ^ 2 * volume := by
    rw [d9PrimitiveSpinCGeometricL2_norm_sq,
      d9PrimitiveSpinCGeometricL2Pairing_self_re]
    calc
      (∫ base,
          d9PrimitiveSpinCGeometricL2Density
            period hPeriod .positiveQuarter
            (state - approximation) base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ≤
          ∫ _ :
              MappingTorus (fixedEquatorData period hPeriod),
            1024 * delta ^ 2
            ∂(intrinsicCanonicalThroatVolumeMeasure
              period hPeriod) := by
        exact MeasureTheory.integral_mono
          (d9PrimitiveSpinCGeometricL2Density_integrable
            period hPeriod .positiveQuarter
            (state - approximation))
          (MeasureTheory.integrable_const (1024 * delta ^ 2))
          hDensity
      _ = 1024 * delta ^ 2 * volume := by
        rw [MeasureTheory.integral_const]
        simp [volume, smul_eq_mul, mul_comm]
  have hAlgebra :
      1024 * delta ^ 2 * volume < epsilon ^ 2 := by
    have hCore :
        1024 * volume < denominator ^ 2 := by
      unfold denominator
      nlinarith [sq_nonneg volume]
    have hEpsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hEpsilon
    have hDenominatorSq : 0 < denominator ^ 2 :=
      sq_pos_of_pos hDenominator
    rw [show
        1024 * delta ^ 2 * volume =
          (epsilon ^ 2 * (1024 * volume)) /
            denominator ^ 2 by
      unfold delta
      field_simp [ne_of_gt hDenominator]]
    rw [div_lt_iff₀ hDenominatorSq]
    exact mul_lt_mul_of_pos_left hCore hEpsilonSq
  have hNorm :
      ‖state - approximation‖ < epsilon := by
    have hNormSqLt :
        ‖state - approximation‖ ^ 2 < epsilon ^ 2 :=
      lt_of_le_of_lt hNormSq hAlgebra
    nlinarith [norm_nonneg (state - approximation)]
  change
    d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter approximation ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap
    at hApproximationRange
  obtain ⟨coefficients, hCoefficients⟩ := hApproximationRange
  refine
    ⟨primitiveSpinCGeometricL2SignedGlobalJointSynthesis
        period hPeriod coefficients,
      ⟨coefficients, rfl⟩, ?_⟩
  change
    dist
      (d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter state)
      ((primitiveSpinCGeometricL2SignedGlobalJointSynthesis
        period hPeriod).toLinearMap coefficients) < epsilon
  rw [hCoefficients]
  rw [dist_eq_norm, ← map_sub]
  simpa [d9PrimitiveSpinCGeometricL2Embedding] using hNorm

theorem primitiveSpinCGeometricL2SignedGlobalDensity_fourierMonopole :
    PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod :=
  primitiveSpinCGeometricL2SignedGlobalDensity_of_coreComplete
    period hPeriod
    (primitiveSpinCFourierMonopoleCoreComplete_proved period hPeriod)

def primitiveSpinCGeometricL2SignedFourierMonopoleUnitary_proved :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  primitiveSpinCGeometricL2SignedFourierMonopoleUnitary
    period hPeriod
    (primitiveSpinCFourierMonopoleCoreComplete_proved period hPeriod)

end
end P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D
end JanusFormal
