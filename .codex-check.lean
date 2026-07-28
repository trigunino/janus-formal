import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSignedPolynomialTangentExhaustion4D

namespace JanusFormal
namespace Check

open Module
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
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
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
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

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
      Fin.sum_univ_three, MvPolynomial.pderiv_mul,
      MvPolynomial.smul_eq_C_mul]
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

end
end Check
end JanusFormal
