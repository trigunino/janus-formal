import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleSpectralBridge4D

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSignedPolynomialTangentExhaustion4D

open Module
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

set_option autoImplicit false
noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

theorem signedBlockSynthesis_surjective_onto
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) (state : SmoothSection period hPeriod)
    (hState :
      state ∈ primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode) :
    ∃ coefficients :
        PrimitiveSpinCGeometricL2SignedBlockCoefficients
          period hPeriod positiveLevel sector circleMode,
      primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveLevel sector circleMode coefficients =
        state := by
  let member :
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode :=
    ⟨state, hState⟩
  let basis :=
    (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
      period hPeriod positiveLevel sector circleMode).toBasis
  let coefficients :
      PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode :=
    WithLp.toLp 2 (fun index => basis.repr member index)
  refine ⟨coefficients, ?_⟩
  change
    (∑ index, basis.repr member index •
      (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod positiveLevel sector circleMode index :
          SmoothSection period hPeriod)) = state
  simpa [basis, member] using congrArg Subtype.val (basis.sum_repr member)

theorem coe_mem_globalRange_of_mem_signedBlock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) (state : SmoothSection period hPeriod)
    (hState :
      state ∈ primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode) :
    (state :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter) ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap := by
  let block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex :=
    ⟨positiveLevel, sector, circleMode⟩
  obtain ⟨coefficients, hCoefficients⟩ :=
    signedBlockSynthesis_surjective_onto
      period hPeriod positiveLevel sector circleMode state hState
  let globalCoefficients :
      PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
        period hPeriod (.positive block) := by
    change
      EuclideanSpace Complex
        (Fin
          (finrank Complex
            (primitiveSpinCGeometricL2SignedBlock
              period hPeriod positiveLevel sector circleMode)))
    exact coefficients
  refine ⟨lp.single 2
    (.positive block) globalCoefficients, ?_⟩
  change
    primitiveSpinCGeometricL2SignedGlobalJointSynthesis period hPeriod
        (lp.single 2 (.positive block) globalCoefficients) =
      (state :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter)
  rw [primitiveSpinCGeometricL2SignedGlobalJointSynthesis_single]
  change
    PrimitiveSpinCGeometricL2SignedBlockCoefficients
      period hPeriod positiveLevel sector circleMode at globalCoefficients
  change
    (primitiveSpinCGeometricL2SignedBlockSynthesis
      period hPeriod positiveLevel sector circleMode globalCoefficients :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter) = state
  have hGlobalCoefficients : globalCoefficients = coefficients := by
    rfl
  rw [hGlobalCoefficients]
  rw [hCoefficients]

theorem nullHarmonicScalar_mem_signedBlock
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode).scalarSection ∈
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode := by
  let seed :=
    (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel multiplicity sector circleMode
  let block :=
    primitiveSpinCGeometricL2SignedBlock
      period hPeriod positiveLevel sector circleMode
  have hPositive :
      seed.positiveSection ∈ block := by
    exact Submodule.mem_sup_left
      (Submodule.subset_span
        ⟨multiplicity, rfl⟩)
  have hNegative :
      seed.negativeSection ∈ block := by
    exact Submodule.mem_sup_right
      (Submodule.subset_span
        ⟨multiplicity, rfl⟩)
  let frequency :=
    primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode
  have hFrequency : (2 * frequency : Complex) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : Real) ≠ 0)
      (ne_of_gt
        (primitiveSpinCHarmonicDiracFrequency_pos
          period positiveLevel sector circleMode))
  have hScaled :
      (2 * frequency : Complex) • seed.scalarSection ∈ block := by
    have hDifference :
        seed.positiveSection - seed.negativeSection =
          (2 * frequency : Complex) • seed.scalarSection := by
      simpa [frequency] using seed.positiveSection_sub_negativeSection
    rw [← hDifference]
    exact Submodule.sub_mem block hPositive hNegative
  have hRecover :
      seed.scalarSection =
        (2 * frequency : Complex)⁻¹ •
          ((2 * frequency : Complex) • seed.scalarSection) := by
    rw [smul_smul, inv_mul_cancel₀ hFrequency, one_smul]
  change seed.scalarSection ∈ block
  rw [hRecover]
  exact Submodule.smul_mem block _ hScaled

theorem nullHarmonicScalar_coe_mem_globalRange
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    (((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode).scalarSection :
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter) ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap :=
  coe_mem_globalRange_of_mem_signedBlock
    period hPeriod positiveLevel sector circleMode _
    (nullHarmonicScalar_mem_signedBlock
      period hPeriod positiveLevel multiplicity sector circleMode)

theorem orthonormalBlockSynthesis_surjective_onto_span
    (sphereLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) (state : SmoothSection period hPeriod)
    (hState :
      state ∈ Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod sphereLevel sector circleMode))) :
    ∃ coefficients :
        EuclideanSpace Complex
          (Fin (primitiveSphereModeDegeneracy sphereLevel)),
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode coefficients =
        state := by
  rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
    period hPeriod sphereLevel sector circleMode] at hState
  obtain ⟨coefficients, hCoefficients⟩ :=
    (Submodule.mem_span_range_iff_exists_fun Complex).mp hState
  exact ⟨WithLp.toLp 2 coefficients, hCoefficients⟩

theorem coe_mem_globalRange_of_mem_zeroBlock
    (sector : NormalRootChoice) (circleMode : Int)
    (state : SmoothSection period hPeriod)
    (hState :
      state ∈ Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 sector circleMode))) :
    (state :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter) ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap := by
  obtain ⟨coefficients, hCoefficients⟩ :=
    orthonormalBlockSynthesis_surjective_onto_span
      period hPeriod 0 sector circleMode state hState
  refine ⟨lp.single 2 (.zero sector circleMode) coefficients, ?_⟩
  change
    primitiveSpinCGeometricL2SignedGlobalJointSynthesis period hPeriod
        (lp.single 2 (.zero sector circleMode) coefficients) =
      (state :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter)
  rw [primitiveSpinCGeometricL2SignedGlobalJointSynthesis_single]
  change
    (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
      period hPeriod 0 sector circleMode coefficients :
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter) = state
  rw [hCoefficients]

theorem hopfZeroMode_coe_mem_globalRange
    (sector : NormalRootChoice) (circleMode : Int) :
    (primitiveSpinCHopfZeroModeSection
        period hPeriod sector circleMode :
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter) ∈
      LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap := by
  apply coe_mem_globalRange_of_mem_zeroBlock
    period hPeriod sector circleMode
  let multiplicity : Fin (primitiveSphereModeDegeneracy 0) :=
    ⟨0, by simp [primitiveSphereModeDegeneracy]⟩
  exact Submodule.subset_span
    ⟨multiplicity, by
      simp [primitiveSpinCGeometricL2RawBlockFamily,
        primitiveSpinCAllModeNullHarmonicRealSection]⟩

def coordinatePowerSection
    (coordinate : Fin 3) (state : SmoothSection period hPeriod) :
    Nat → SmoothSection period hPeriod
  | 0 => state
  | degree + 1 =>
      primitiveSpinCCoordinateMultiplicationComplexLinearMap
        period hPeriod coordinate
        (coordinatePowerSection coordinate state degree)

theorem coordinatePowerSection_apply
    (coordinate : Fin 3) (state : SmoothSection period hPeriod)
    (degree : Nat) (base) :
    (show D9DoubledMatterFiber from
      coordinatePowerSection period hPeriod coordinate state degree base) =
      d9PrimitiveSpinCComplexActionCLM
        ((d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate base : Complex) ^ degree)
        (show D9DoubledMatterFiber from state base) := by
  induction degree with
  | zero =>
      simp [coordinatePowerSection]
  | succ degree ih =>
      simp only [coordinatePowerSection,
        primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
        primitiveSpinCCoordinateMultiplicationLinearMap_apply,
        d9PrimitiveSpinCRealScalarMulSection_apply, ih]
      have hRealAction
          (real : Real) (scalar : Complex)
          (matter : D9DoubledMatterFiber) :
          real • d9PrimitiveSpinCComplexActionCLM scalar matter =
            d9PrimitiveSpinCComplexActionCLM
              ((real : Complex) * scalar) matter := by
        apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
        rw [map_smul,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
        module
      change
        d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base •
            d9PrimitiveSpinCComplexActionCLM
              ((d9PrimitiveMonopoleBaseCoordinate
                period hPeriod coordinate base : Complex) ^ degree)
              (show D9DoubledMatterFiber from state base) =
          d9PrimitiveSpinCComplexActionCLM
            ((d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base : Complex) ^ (degree + 1))
            (show D9DoubledMatterFiber from state base)
      rw [hRealAction, pow_succ']

def solidMonomialSection
    (exponent : Fin 3 →₀ Nat) (state : SmoothSection period hPeriod) :
    SmoothSection period hPeriod :=
  coordinatePowerSection period hPeriod 0
    (coordinatePowerSection period hPeriod 1
      (coordinatePowerSection period hPeriod 2 state (exponent 2))
      (exponent 1))
    (exponent 0)

theorem solidMonomialSection_apply
    (exponent : Fin 3 →₀ Nat) (state : SmoothSection period hPeriod)
    (base) :
    (show D9DoubledMatterFiber from
      solidMonomialSection period hPeriod exponent state base) =
      d9PrimitiveSpinCComplexActionCLM
        (exponent.prod fun coordinate degree =>
          (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate base : Complex) ^ degree)
        (show D9DoubledMatterFiber from state base) := by
  simp only [solidMonomialSection, coordinatePowerSection_apply]
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  rw [exponent.prod_fintype]
  · congr 1
    simp [Fin.prod_univ_succ]
    ring
  · intro
    simp

def solidPolynomialSection
    (polynomial : MvPolynomial (Fin 3) Complex)
    (state : SmoothSection period hPeriod) :
    SmoothSection period hPeriod :=
  polynomial.sum fun exponent coefficient =>
    coefficient •
      solidMonomialSection period hPeriod exponent state

theorem solidPolynomialSection_apply
    (polynomial : MvPolynomial (Fin 3) Complex)
    (state : SmoothSection period hPeriod) (base) :
    (show D9DoubledMatterFiber from
      solidPolynomialSection period hPeriod polynomial state base) =
      d9PrimitiveSpinCComplexActionCLM
        (MvPolynomial.eval
          (fun coordinate =>
            (d9PrimitiveMonopoleBaseCoordinate
              period hPeriod coordinate base : Complex))
          polynomial)
        (show D9DoubledMatterFiber from state base) := by
  classical
  unfold solidPolynomialSection
  rw [MvPolynomial.eval_eq]
  rw [show
    (Finsupp.sum polynomial fun exponent coefficient =>
        coefficient •
          solidMonomialSection period hPeriod exponent state) =
      ∑ exponent ∈ polynomial.support,
        MvPolynomial.coeff exponent polynomial •
          solidMonomialSection period hPeriod exponent state by
    rfl]
  have hSumApply :
      (show D9DoubledMatterFiber from
        (∑ exponent ∈ polynomial.support,
          MvPolynomial.coeff exponent polynomial •
            solidMonomialSection
              period hPeriod exponent state) base) =
        ∑ exponent ∈ polynomial.support,
          (show D9DoubledMatterFiber from
            (MvPolynomial.coeff exponent polynomial •
              solidMonomialSection
                period hPeriod exponent state) base) := by
    have hFiber :
        (∑ exponent ∈ polynomial.support,
          MvPolynomial.coeff exponent polynomial •
            solidMonomialSection
              period hPeriod exponent state) base =
          ∑ exponent ∈ polynomial.support,
            (MvPolynomial.coeff exponent polynomial •
              solidMonomialSection
                period hPeriod exponent state) base := by
      change
        d9PrimitiveSpinCSectionEvaluation
            period hPeriod .positiveQuarter base
            (∑ exponent ∈ polynomial.support,
              MvPolynomial.coeff exponent polynomial •
                solidMonomialSection
                  period hPeriod exponent state) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro exponent _
      rfl
    exact congrArg
      (fun current =>
        (show D9DoubledMatterFiber from current)) hFiber
  rw [hSumApply]
  simp_rw [primitiveSpinCComplex_smul,
    d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  change
    (∑ exponent ∈ polynomial.support,
      d9PrimitiveSpinCComplexActionCLM
        (MvPolynomial.coeff exponent polynomial)
        (show D9DoubledMatterFiber from
          solidMonomialSection
            period hPeriod exponent state base)) =
      d9PrimitiveSpinCComplexActionCLM
        (∑ exponent ∈ polynomial.support,
          MvPolynomial.coeff exponent polynomial *
            exponent.prod fun coordinate degree =>
              (d9PrimitiveMonopoleBaseCoordinate
                period hPeriod coordinate base : Complex) ^ degree)
        (show D9DoubledMatterFiber from state base)
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp_rw [map_sum,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    solidMonomialSection_apply,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro exponent _
  rw [mul_smul]

theorem solidPolynomialSection_add
    (first second : MvPolynomial (Fin 3) Complex)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection period hPeriod (first + second) state =
      solidPolynomialSection period hPeriod first state +
        solidPolynomialSection period hPeriod second state := by
  apply DFunLike.ext _ _
  intro base
  rw [show
    (solidPolynomialSection period hPeriod first state +
      solidPolynomialSection period hPeriod second state) base =
      solidPolynomialSection period hPeriod first state base +
        solidPolynomialSection period hPeriod second state base by
    rfl]
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod (first + second) state base) =
      (show D9DoubledMatterFiber from
        solidPolynomialSection period hPeriod first state base) +
        (show D9DoubledMatterFiber from
          solidPolynomialSection period hPeriod second state base)
  rw [solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    map_add]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_add,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  exact add_smul _ _ _

theorem solidPolynomialSection_smul
    (scalar : Complex) (polynomial : MvPolynomial (Fin 3) Complex)
    (state : SmoothSection period hPeriod) :
    solidPolynomialSection period hPeriod (scalar • polynomial) state =
      scalar •
        solidPolynomialSection period hPeriod polynomial state := by
  apply DFunLike.ext _ _
  intro base
  rw [primitiveSpinCComplex_smul,
    d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  change
    (show D9DoubledMatterFiber from
      solidPolynomialSection
        period hPeriod (scalar • polynomial) state base) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (show D9DoubledMatterFiber from
          solidPolynomialSection
            period hPeriod polynomial state base)
  rw [solidPolynomialSection_apply,
    solidPolynomialSection_apply,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1
  simp [MvPolynomial.smul_eq_C_mul]

theorem tangent_cross_basis_zero
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 2
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 1 sector circleMode) -
        primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 1
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 2 sector circleMode) =
      (-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 0 sector circleMode := by
  apply DFunLike.ext _ _
  intro base
  change
    d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base
        (primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 2
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 1 sector circleMode) -
          primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 1
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 2 sector circleMode)) =
      ((-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 0 sector circleMode) base
  rw [map_sub]
  simp only [
    d9PrimitiveSpinCSectionEvaluation_apply,
    primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply,
    primitiveSpinCComplex_smul,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  unfold d9PrimitiveSpinCBaseUnitRadialCoordinate
  change
    d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 2 base •
        (d9DoubledMatterFiberCliffordGammaCLM 1
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 1 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) -
      d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 1 base •
        (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 2 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 0
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 0 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base))
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let n : Fin 3 → Real :=
    fun direction =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod direction base
  have hRadial :
      n 0 • d9DoubledMatterFiberCliffordGammaCLM 0 matter +
          n 1 • d9DoubledMatterFiberCliffordGammaCLM 1 matter +
        n 2 • d9DoubledMatterFiberCliffordGammaCLM 2 matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [d9PrimitiveSpinCBaseUnitRadialClifford,
      Fin.sum_univ_three, n, matter] using
      primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base
  change
    n 2 •
          (d9DoubledMatterFiberCliffordGammaCLM 1 matter -
            n 1 • d9PrimitiveSpinCImaginaryAction matter) -
        n 1 •
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter -
            n 2 • d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 0 matter -
          n 0 • d9PrimitiveSpinCImaginaryAction matter)
  rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  simp only [Complex.neg_re, Complex.I_re, neg_zero,
    Complex.neg_im, Complex.I_im, zero_smul,
    neg_smul, zero_add, one_smul]
  rw [map_sub, d9PrimitiveSpinCImaginaryAction_clifford,
    map_smul, d9PrimitiveSpinCImaginaryAction_sq, ← hRadial]
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    d9DoubledMatterFiberCliffordGammaCLM_apply]
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberCliffordGamma_sq,
    d9DoubledMatterFiberCliffordGamma_zero_one,
    d9DoubledMatterFiberCliffordGamma_zero_two]
  module

theorem tangent_cross_basis_one
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 0
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 2 sector circleMode) -
        primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 2
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 0 sector circleMode) =
      (-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 1 sector circleMode := by
  apply DFunLike.ext _ _
  intro base
  change
    d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base
        (primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 0
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 2 sector circleMode) -
          primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 2
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 0 sector circleMode)) =
      ((-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 1 sector circleMode) base
  rw [map_sub]
  simp only [
    d9PrimitiveSpinCSectionEvaluation_apply,
    primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply,
    primitiveSpinCComplex_smul,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  unfold d9PrimitiveSpinCBaseUnitRadialCoordinate
  change
    d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 0 base •
        (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 2 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) -
      d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 2 base •
        (d9DoubledMatterFiberCliffordGammaCLM 0
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 0 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 1
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 1 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base))
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let n : Fin 3 → Real := fun direction =>
    d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod direction base
  have hRadial :
      n 0 • d9DoubledMatterFiberCliffordGammaCLM 0 matter +
          n 1 • d9DoubledMatterFiberCliffordGammaCLM 1 matter +
        n 2 • d9DoubledMatterFiberCliffordGammaCLM 2 matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [d9PrimitiveSpinCBaseUnitRadialClifford,
      Fin.sum_univ_three, n, matter] using
      primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base
  change
    n 0 •
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter -
            n 2 • d9PrimitiveSpinCImaginaryAction matter) -
        n 2 •
          (d9DoubledMatterFiberCliffordGammaCLM 0 matter -
            n 0 • d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 1 matter -
          n 1 • d9PrimitiveSpinCImaginaryAction matter)
  rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  simp only [Complex.neg_re, Complex.I_re, neg_zero,
    Complex.neg_im, Complex.I_im, zero_smul,
    neg_smul, zero_add, one_smul]
  rw [map_sub, d9PrimitiveSpinCImaginaryAction_clifford,
    map_smul, d9PrimitiveSpinCImaginaryAction_sq, ← hRadial]
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    d9DoubledMatterFiberCliffordGammaCLM_apply]
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberCliffordGamma_one_zero,
    d9DoubledMatterFiberCliffordGamma_sq,
    d9DoubledMatterFiberCliffordGamma_one_two]
  module

theorem tangent_cross_basis_two
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 1
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 0 sector circleMode) -
        primitiveSpinCCoordinateMultiplicationComplexLinearMap
          period hPeriod 0
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod 1 sector circleMode) =
      (-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 2 sector circleMode := by
  apply DFunLike.ext _ _
  intro base
  change
    d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base
        (primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 1
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 0 sector circleMode) -
          primitiveSpinCCoordinateMultiplicationComplexLinearMap
            period hPeriod 0
            (primitiveSpinCHopfFirstSphereTangentialSection
              period hPeriod 1 sector circleMode)) =
      ((-Complex.I) •
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod 2 sector circleMode) base
  rw [map_sub]
  simp only [
    d9PrimitiveSpinCSectionEvaluation_apply,
    primitiveSpinCCoordinateMultiplicationComplexLinearMap_apply,
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply,
    primitiveSpinCComplex_smul,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  unfold d9PrimitiveSpinCBaseUnitRadialCoordinate
  change
    d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 1 base •
        (d9DoubledMatterFiberCliffordGammaCLM 0
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 0 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) -
      d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod 0 base •
        (d9DoubledMatterFiberCliffordGammaCLM 1
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 1 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base)) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode base) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod 2 base •
            d9PrimitiveSpinCImaginaryAction
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode base))
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  let n : Fin 3 → Real := fun direction =>
    d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod direction base
  have hRadial :
      n 0 • d9DoubledMatterFiberCliffordGammaCLM 0 matter +
          n 1 • d9DoubledMatterFiberCliffordGammaCLM 1 matter +
        n 2 • d9DoubledMatterFiberCliffordGammaCLM 2 matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [d9PrimitiveSpinCBaseUnitRadialClifford,
      Fin.sum_univ_three, n, matter] using
      primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base
  change
    n 1 •
          (d9DoubledMatterFiberCliffordGammaCLM 0 matter -
            n 0 • d9PrimitiveSpinCImaginaryAction matter) -
        n 0 •
          (d9DoubledMatterFiberCliffordGammaCLM 1 matter -
            n 1 • d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (d9DoubledMatterFiberCliffordGammaCLM 2 matter -
          n 2 • d9PrimitiveSpinCImaginaryAction matter)
  rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
  simp only [Complex.neg_re, Complex.I_re, neg_zero,
    Complex.neg_im, Complex.I_im, zero_smul,
    neg_smul, zero_add, one_smul]
  rw [map_sub, d9PrimitiveSpinCImaginaryAction_clifford,
    map_smul, d9PrimitiveSpinCImaginaryAction_sq, ← hRadial]
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    d9DoubledMatterFiberCliffordGammaCLM_apply]
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberCliffordGamma_two_zero,
    d9DoubledMatterFiberCliffordGamma_two_one,
    d9DoubledMatterFiberCliffordGamma_sq]
  module

end
end P0EFTJanusProgramPD9PrimitiveSpinCSignedPolynomialTangentExhaustion4D
end JanusFormal
