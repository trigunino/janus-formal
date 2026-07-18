import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRealSquareRootSpectralObstructions4D

/-!
# Real roots of complex-conjugate spectral blocks in dimension four

A conjugate pair `a ± ib` is represented by the real block
`[[a, -b], [b, a]]`.  This gate constructs its square root on the exact
principal branch, closes the negative-real cut separately, and combines two
blocks in dimension four.  It also treats the size-two complex Jordan chain.

The only remaining classification input is conversion of a raw real
characteristic-polynomial factorization into one of these real canonical
presentations; current Mathlib has no Jordan-chain basis API.
-/

namespace JanusFormal
namespace P0EFTJanusComplexConjugatePairRoot4D

set_option autoImplicit false

noncomputable section

open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusRealSquareRootSpectralObstructions4D

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) Real
abbrev Matrix4 := P0EFTJanusRealSquareRootSpectralObstructions4D.Matrix4

/-- Modulus of the complex number `a + ib`. -/
def complexPairRadius (a b : Real) : Real :=
  Real.sqrt (a ^ 2 + b ^ 2)

theorem complexPairRadius_nonneg (a b : Real) :
    0 ≤ complexPairRadius a b :=
  Real.sqrt_nonneg _

theorem complexPairRadius_sq (a b : Real) :
    complexPairRadius a b ^ 2 = a ^ 2 + b ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

theorem complexPairRadius_pos
    {a b : Real} (hNonzero : a ≠ 0 ∨ b ≠ 0) :
    0 < complexPairRadius a b := by
  rw [complexPairRadius, Real.sqrt_pos]
  rcases hNonzero with ha | hb
  · nlinarith [sq_pos_of_ne_zero ha]
  · nlinarith [sq_pos_of_ne_zero hb]

theorem complexPairRadius_add_real_nonneg (a b : Real) :
    0 ≤ complexPairRadius a b + a := by
  by_cases ha : 0 ≤ a
  · exact add_nonneg (complexPairRadius_nonneg a b) ha
  · have haNeg : a < 0 := lt_of_not_ge ha
    have hRadius := complexPairRadius_nonneg a b
    have hSquare := complexPairRadius_sq a b
    nlinarith [sq_nonneg b]

/-- The denominator of the principal formula vanishes exactly on the closed
negative-real cut, including its endpoint. -/
theorem complexPairRadius_add_real_eq_zero_iff (a b : Real) :
    complexPairRadius a b + a = 0 ↔ b = 0 ∧ a ≤ 0 := by
  constructor
  · intro hZero
    have hRadius := complexPairRadius_nonneg a b
    have hSquare := complexPairRadius_sq a b
    constructor
    · nlinarith [sq_nonneg b]
    · linarith
  · rintro ⟨rfl, ha⟩
    simp [complexPairRadius, Real.sqrt_sq_eq_abs, abs_of_nonpos ha]

theorem complexPairPrincipalBranch_iff (a b : Real) :
    0 < complexPairRadius a b + a ↔ b ≠ 0 ∨ 0 < a := by
  constructor
  · intro hBranch
    by_cases hb : b = 0
    · right
      by_contra ha
      have hCut :=
        (complexPairRadius_add_real_eq_zero_iff a b).2
          ⟨hb, le_of_not_gt ha⟩
      linarith
    · exact Or.inl hb
  · intro hOffCut
    have hNe : complexPairRadius a b + a ≠ 0 := by
      intro hZero
      obtain ⟨hb, ha⟩ :=
        (complexPairRadius_add_real_eq_zero_iff a b).1 hZero
      rcases hOffCut with hbNe | haPos
      · exact hbNe hb
      · linarith
    exact lt_of_le_of_ne (complexPairRadius_add_real_nonneg a b) (Ne.symm hNe)

/-- Nonnegative real coefficient of the principal complex square root. -/
def complexPairPrincipalRootReal (a b : Real) : Real :=
  Real.sqrt ((complexPairRadius a b + a) / 2)

/-- Imaginary coefficient on the open principal branch. -/
def complexPairPrincipalRootImag (a b : Real) : Real :=
  b / (2 * complexPairPrincipalRootReal a b)

theorem complexPairPrincipalRootReal_pos
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    0 < complexPairPrincipalRootReal a b := by
  rw [complexPairPrincipalRootReal, Real.sqrt_pos]
  linarith

theorem complexPairPrincipalRootReal_mul_self
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    complexPairPrincipalRootReal a b *
        complexPairPrincipalRootReal a b =
      (complexPairRadius a b + a) / 2 := by
  exact Real.mul_self_sqrt (by linarith)

theorem complexPairPrincipalRootImag_mul_self
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    complexPairPrincipalRootImag a b *
        complexPairPrincipalRootImag a b =
      (complexPairRadius a b - a) / 2 := by
  have hReal := complexPairPrincipalRootReal_mul_self hBranch
  have hRealNe : complexPairPrincipalRootReal a b ≠ 0 :=
    ne_of_gt (complexPairPrincipalRootReal_pos hBranch)
  have hFactor :
      b ^ 2 =
        (complexPairRadius a b - a) * (complexPairRadius a b + a) := by
    have hRadius := complexPairRadius_sq a b
    nlinarith
  unfold complexPairPrincipalRootImag
  field_simp [hRealNe]
  nlinarith

theorem complexPairPrincipalRoot_real_identity
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    complexPairPrincipalRootReal a b *
          complexPairPrincipalRootReal a b -
        complexPairPrincipalRootImag a b *
          complexPairPrincipalRootImag a b = a := by
  rw [complexPairPrincipalRootReal_mul_self hBranch,
    complexPairPrincipalRootImag_mul_self hBranch]
  ring

theorem complexPairPrincipalRoot_imag_identity
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    2 * complexPairPrincipalRootReal a b *
        complexPairPrincipalRootImag a b = b := by
  have hRealNe : complexPairPrincipalRootReal a b ≠ 0 :=
    ne_of_gt (complexPairPrincipalRootReal_pos hBranch)
  unfold complexPairPrincipalRootImag
  field_simp [hRealNe]

/-- Real representation of multiplication by `a + ib`. -/
def complexPairTarget2 (a b : Real) : Matrix2 :=
  ![![a, -b], ![b, a]]

def complexPairPrincipalRoot2 (a b : Real) : Matrix2 :=
  ![![complexPairPrincipalRootReal a b,
      -complexPairPrincipalRootImag a b],
    ![complexPairPrincipalRootImag a b,
      complexPairPrincipalRootReal a b]]

theorem complexPairPrincipalRoot2_square
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    complexPairPrincipalRoot2 a b * complexPairPrincipalRoot2 a b =
      complexPairTarget2 a b := by
  have hReal := complexPairPrincipalRoot_real_identity hBranch
  have hImag := complexPairPrincipalRoot_imag_identity hBranch
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPairPrincipalRoot2, complexPairTarget2, Matrix.mul_apply,
      Fin.sum_univ_two] <;> nlinarith [hReal, hImag]

/-- Global imaginary coefficient.  The negative-real cut is closed by the
positive imaginary root, while the principal formula is used off the cut. -/
def complexPairRootImag (a b : Real) : Real :=
  if complexPairRadius a b + a = 0 then Real.sqrt (-a)
  else complexPairPrincipalRootImag a b

def complexPairRoot2 (a b : Real) : Matrix2 :=
  ![![complexPairPrincipalRootReal a b, -complexPairRootImag a b],
    ![complexPairRootImag a b, complexPairPrincipalRootReal a b]]

theorem complexPairRoot_coefficients (a b : Real) :
    complexPairPrincipalRootReal a b *
          complexPairPrincipalRootReal a b -
        complexPairRootImag a b * complexPairRootImag a b = a ∧
      2 * complexPairPrincipalRootReal a b * complexPairRootImag a b = b := by
  by_cases hCut : complexPairRadius a b + a = 0
  · obtain ⟨hb, ha⟩ :=
      (complexPairRadius_add_real_eq_zero_iff a b).1 hCut
    have hReal : complexPairPrincipalRootReal a b = 0 := by
      simp [complexPairPrincipalRootReal, hCut]
    have hImag : complexPairRootImag a b = Real.sqrt (-a) := by
      simp [complexPairRootImag, hCut]
    have hImagSquare : Real.sqrt (-a) * Real.sqrt (-a) = -a :=
      Real.mul_self_sqrt (by linarith)
    constructor
    · rw [hReal, hImag, hImagSquare]
      ring
    · rw [hReal, hb]
      ring
  · have hBranch : 0 < complexPairRadius a b + a :=
      lt_of_le_of_ne (complexPairRadius_add_real_nonneg a b) (Ne.symm hCut)
    simpa [complexPairRootImag, hCut] using
      And.intro (complexPairPrincipalRoot_real_identity hBranch)
        (complexPairPrincipalRoot_imag_identity hBranch)

theorem complexPairRoot2_square (a b : Real) :
    complexPairRoot2 a b * complexPairRoot2 a b =
      complexPairTarget2 a b := by
  obtain ⟨hReal, hImag⟩ := complexPairRoot_coefficients a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPairRoot2, complexPairTarget2, Matrix.mul_apply,
      Fin.sum_univ_two] <;> nlinarith [hReal, hImag]

theorem complexPair_nonzero_hasRealRoot2
    (a b : Real) (_hNonzero : a ≠ 0 ∨ b ≠ 0) :
    ∃ root : Matrix2, root * root = complexPairTarget2 a b :=
  ⟨complexPairRoot2 a b, complexPairRoot2_square a b⟩

theorem continuous_complexPairRadius :
    Continuous (fun point : Real × Real =>
      complexPairRadius point.1 point.2) := by
  unfold complexPairRadius
  fun_prop

theorem continuous_complexPairPrincipalRootReal :
    Continuous (fun point : Real × Real =>
      complexPairPrincipalRootReal point.1 point.2) := by
  unfold complexPairPrincipalRootReal
  exact Real.continuous_sqrt.comp
    ((continuous_complexPairRadius.add continuous_fst).div_const 2)

/-- The principal branch is coefficientwise stable precisely off the closed
negative-real cut. -/
theorem continuousAt_complexPairPrincipalRootImag
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    ContinuousAt (fun point : Real × Real =>
      complexPairPrincipalRootImag point.1 point.2) (a, b) := by
  have hDenominator :
      2 * complexPairPrincipalRootReal a b ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (ne_of_gt (complexPairPrincipalRootReal_pos hBranch))
  have hNumerator :
      ContinuousAt (fun point : Real × Real => point.2) (a, b) :=
    continuous_snd.continuousAt
  have hDenominatorContinuous :
      ContinuousAt (fun point : Real × Real =>
        2 * complexPairPrincipalRootReal point.1 point.2) (a, b) :=
    (continuous_const.mul continuous_complexPairPrincipalRootReal).continuousAt
  unfold complexPairPrincipalRootImag
  exact hNumerator.div hDenominatorContinuous hDenominator

theorem continuousAt_complexPairPrincipalRoot2
    {a b : Real} (hBranch : 0 < complexPairRadius a b + a) :
    ContinuousAt (fun point : Real × Real =>
      complexPairPrincipalRoot2 point.1 point.2) (a, b) := by
  have hReal :
      ContinuousAt (fun point : Real × Real =>
        complexPairPrincipalRootReal point.1 point.2) (a, b) :=
    continuous_complexPairPrincipalRootReal.continuousAt
  have hImag := continuousAt_complexPairPrincipalRootImag hBranch
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [complexPairPrincipalRoot2] using hReal
  · simpa [complexPairPrincipalRoot2] using hImag.neg
  · simpa [complexPairPrincipalRoot2] using hImag
  · simpa [complexPairPrincipalRoot2] using hReal

theorem complexPairRoot_norm_sq (a b : Real) :
    complexPairPrincipalRootReal a b *
          complexPairPrincipalRootReal a b +
        complexPairRootImag a b * complexPairRootImag a b =
      complexPairRadius a b := by
  obtain ⟨hReal, hImag⟩ := complexPairRoot_coefficients a b
  let normSquare :=
    complexPairPrincipalRootReal a b *
        complexPairPrincipalRootReal a b +
      complexPairRootImag a b * complexPairRootImag a b
  have hNormNonneg : 0 ≤ normSquare := by
    dsimp [normSquare]
    exact add_nonneg (mul_self_nonneg _ ) (mul_self_nonneg _)
  have hNormSquare :
      normSquare ^ 2 = a ^ 2 + b ^ 2 := by
    calc
      normSquare ^ 2 =
          (complexPairPrincipalRootReal a b *
                complexPairPrincipalRootReal a b -
              complexPairRootImag a b * complexPairRootImag a b) ^ 2 +
            (2 * complexPairPrincipalRootReal a b *
              complexPairRootImag a b) ^ 2 := by
        dsimp [normSquare]
        ring
      _ = a ^ 2 + b ^ 2 := by rw [hReal, hImag]
  have hRadiusSquare := complexPairRadius_sq a b
  have hProduct :
      (normSquare - complexPairRadius a b) *
          (normSquare + complexPairRadius a b) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hProduct with hEqual | hOpposite
  · linarith
  · have hRadiusNonneg := complexPairRadius_nonneg a b
    linarith

/-- Along the positive real axis, targets of size `t²` have roots of size
`t`; this is the exact square-root scaling at the zero threshold. -/
theorem positiveAxis_root_quadratic_scaling
    (t : Real) (ht : 0 ≤ t) :
    complexPairPrincipalRootReal (t ^ 2) 0 = t := by
  simp [complexPairPrincipalRootReal, complexPairRadius,
    Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

/-- The root/target quotient is unbounded at zero, so no uniform linear
(Lipschitz) stability estimate can hold there. -/
theorem positiveAxis_root_ratio_unbounded
    (constant : Real) (hConstant : 0 ≤ constant) :
    ∃ t : Real, 0 < t ∧
      constant * t ^ 2 < t ∧
      complexPairPrincipalRootReal (t ^ 2) 0 = t := by
  let t := (constant + 1)⁻¹
  have hDenominator : 0 < constant + 1 := by linarith
  have ht : 0 < t := inv_pos.mpr hDenominator
  have hScale : (constant + 1) * t = 1 := by
    simp [t, ne_of_gt hDenominator]
  have hRatio : constant * t < 1 := by
    calc
      constant * t < (constant + 1) * t := by
        exact mul_lt_mul_of_pos_right (by linarith) ht
      _ = 1 := hScale
  refine ⟨t, ht, ?_, positiveAxis_root_quadratic_scaling t ht.le⟩
  have hScaled := mul_lt_mul_of_pos_right hRatio ht
  nlinarith

theorem complexPairRoot2_zero :
    complexPairRoot2 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPairRoot2, complexPairRootImag,
      complexPairPrincipalRootReal, complexPairRadius]

/-- The square-map linearization at the zero four-dimensional root is
singular. -/
theorem sylvesterOperator_zero_not_injective :
    ¬ Function.Injective (sylvesterOperator (0 : Matrix4)) := by
  intro hInjective
  have hEqual :
      sylvesterOperator (0 : Matrix4) (0 : Matrix4) =
        sylvesterOperator (0 : Matrix4) (1 : Matrix4) := by
    simp [sylvesterOperator_apply]
  exact zero_ne_one (hInjective hEqual)

/-- Direct sum of two real conjugate-pair blocks. -/
def complexPairSumTarget4
    (firstReal firstImag secondReal secondImag : Real) : Matrix4 :=
  ![![firstReal, -firstImag, 0, 0],
    ![firstImag, firstReal, 0, 0],
    ![0, 0, secondReal, -secondImag],
    ![0, 0, secondImag, secondReal]]

def complexPairSumRoot4
    (firstReal firstImag secondReal secondImag : Real) : Matrix4 :=
  let firstRootReal :=
    complexPairPrincipalRootReal firstReal firstImag
  let firstRootImag := complexPairRootImag firstReal firstImag
  let secondRootReal :=
    complexPairPrincipalRootReal secondReal secondImag
  let secondRootImag := complexPairRootImag secondReal secondImag
  ![![firstRootReal, -firstRootImag, 0, 0],
    ![firstRootImag, firstRootReal, 0, 0],
    ![0, 0, secondRootReal, -secondRootImag],
    ![0, 0, secondRootImag, secondRootReal]]

theorem complexPairSumRoot4_square
    (firstReal firstImag secondReal secondImag : Real) :
    complexPairSumRoot4 firstReal firstImag secondReal secondImag *
        complexPairSumRoot4 firstReal firstImag secondReal secondImag =
      complexPairSumTarget4 firstReal firstImag secondReal secondImag := by
  obtain ⟨hFirstReal, hFirstImag⟩ :=
    complexPairRoot_coefficients firstReal firstImag
  obtain ⟨hSecondReal, hSecondImag⟩ :=
    complexPairRoot_coefficients secondReal secondImag
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPairSumRoot4, complexPairSumTarget4, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    nlinarith [hFirstReal, hFirstImag, hSecondReal, hSecondImag]

theorem complexPairSum_hasRealSquareRoot
    (firstReal firstImag secondReal secondImag : Real) :
    HasRealSquareRoot
      (complexPairSumTarget4 firstReal firstImag secondReal secondImag) :=
  ⟨complexPairSumRoot4 firstReal firstImag secondReal secondImag,
    complexPairSumRoot4_square firstReal firstImag secondReal secondImag⟩

/-- Real size-two Jordan chain for one nonzero complex-conjugate pair. -/
def complexJordan2Target4 (a b : Real) : Matrix4 :=
  ![![a, -b, 1, 0],
    ![b, a, 0, 1],
    ![0, 0, a, -b],
    ![0, 0, b, a]]

def complexJordan2CorrectionReal (a b : Real) : Real :=
  complexPairPrincipalRootReal a b / (2 * complexPairRadius a b)

def complexJordan2CorrectionImag (a b : Real) : Real :=
  -complexPairRootImag a b / (2 * complexPairRadius a b)

def complexJordan2Root4 (a b : Real) : Matrix4 :=
  let rootReal := complexPairPrincipalRootReal a b
  let rootImag := complexPairRootImag a b
  let correctionReal := complexJordan2CorrectionReal a b
  let correctionImag := complexJordan2CorrectionImag a b
  ![![rootReal, -rootImag, correctionReal, -correctionImag],
    ![rootImag, rootReal, correctionImag, correctionReal],
    ![0, 0, rootReal, -rootImag],
    ![0, 0, rootImag, rootReal]]

theorem complexJordan2_correction_real_identity
    {a b : Real} (hNonzero : a ≠ 0 ∨ b ≠ 0) :
    2 *
        (complexPairPrincipalRootReal a b *
            complexJordan2CorrectionReal a b -
          complexPairRootImag a b * complexJordan2CorrectionImag a b) = 1 := by
  have hRadiusNe : complexPairRadius a b ≠ 0 :=
    ne_of_gt (complexPairRadius_pos hNonzero)
  have hNorm := complexPairRoot_norm_sq a b
  unfold complexJordan2CorrectionReal complexJordan2CorrectionImag
  field_simp [hRadiusNe]
  nlinarith

theorem complexJordan2_correction_imag_identity
    {a b : Real} (hNonzero : a ≠ 0 ∨ b ≠ 0) :
    2 *
        (complexPairPrincipalRootReal a b *
            complexJordan2CorrectionImag a b +
          complexPairRootImag a b * complexJordan2CorrectionReal a b) = 0 := by
  have hRadiusNe : complexPairRadius a b ≠ 0 :=
    ne_of_gt (complexPairRadius_pos hNonzero)
  unfold complexJordan2CorrectionReal complexJordan2CorrectionImag
  field_simp [hRadiusNe]
  ring

theorem complexJordan2Root4_square
    {a b : Real} (hNonzero : a ≠ 0 ∨ b ≠ 0) :
    complexJordan2Root4 a b * complexJordan2Root4 a b =
      complexJordan2Target4 a b := by
  obtain ⟨hReal, hImag⟩ := complexPairRoot_coefficients a b
  have hCorrectionReal :=
    complexJordan2_correction_real_identity hNonzero
  have hCorrectionImag :=
    complexJordan2_correction_imag_identity hNonzero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexJordan2Root4, complexJordan2Target4, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    nlinarith [hReal, hImag, hCorrectionReal, hCorrectionImag]

theorem complexJordan2_hasRealSquareRoot
    (a b : Real) (hNonzero : a ≠ 0 ∨ b ≠ 0) :
    HasRealSquareRoot (complexJordan2Target4 a b) :=
  ⟨complexJordan2Root4 a b, complexJordan2Root4_square hNonzero⟩

theorem hasRealSquareRoot_of_similarity
    {target canonicalRoot canonicalTarget change inverse : Matrix4}
    (hSquare : canonicalRoot * canonicalRoot = canonicalTarget)
    (hInverseChange : inverse * change = 1)
    (hTarget : target = change * canonicalTarget * inverse) :
    HasRealSquareRoot target := by
  refine ⟨change * canonicalRoot * inverse, ?_⟩
  calc
    (change * canonicalRoot * inverse) *
        (change * canonicalRoot * inverse) =
      change * canonicalRoot * (inverse * change) *
        canonicalRoot * inverse := by noncomm_ring
    _ = change * (canonicalRoot * canonicalRoot) * inverse := by
      rw [hInverseChange]
      noncomm_ring
    _ = change * canonicalTarget * inverse := by rw [hSquare]
    _ = target := hTarget.symm

/-- The two real canonical possibilities for a purely nonreal spectrum in
dimension four: two pair blocks, or one size-two complex Jordan chain. -/
def HasPureNonrealJordanPresentation4 (target : Matrix4) : Prop :=
  (∃ firstReal firstImag secondReal secondImag : Real,
      firstImag ≠ 0 ∧ secondImag ≠ 0 ∧
      ∃ change inverse : Matrix4,
        change * inverse = 1 ∧ inverse * change = 1 ∧
          target = change *
            complexPairSumTarget4 firstReal firstImag secondReal secondImag *
              inverse) ∨
    (∃ realPart imaginaryPart : Real,
      imaginaryPart ≠ 0 ∧
      ∃ change inverse : Matrix4,
        change * inverse = 1 ∧ inverse * change = 1 ∧
          target = change * complexJordan2Target4 realPart imaginaryPart *
            inverse)

theorem hasRealSquareRoot_of_pureNonrealJordanPresentation
    {target : Matrix4} (hPresentation : HasPureNonrealJordanPresentation4 target) :
    HasRealSquareRoot target := by
  rcases hPresentation with hSplit | hChain
  · obtain ⟨firstReal, firstImag, secondReal, secondImag,
      _hFirstNonreal, _hSecondNonreal, change, inverse,
      _hChangeInverse, hInverseChange, hTarget⟩ := hSplit
    exact hasRealSquareRoot_of_similarity
      (complexPairSumRoot4_square
        firstReal firstImag secondReal secondImag)
      hInverseChange hTarget
  · obtain ⟨realPart, imaginaryPart, hNonreal, change, inverse,
      _hChangeInverse, hInverseChange, hTarget⟩ := hChain
    exact hasRealSquareRoot_of_similarity
      (complexJordan2Root4_square (Or.inr hNonreal))
      hInverseChange hTarget

/-- Irreducible real quadratic associated with `a ± ib`. -/
def conjugatePairQuadratic (a b : Real) : Polynomial Real :=
  X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)

/-- Raw characteristic-polynomial criterion for a purely nonreal spectrum. -/
def PureNonrealConjugatePairCharpoly4 (target : Matrix4) : Prop :=
  ∃ firstReal firstImag secondReal secondImag : Real,
    firstImag ≠ 0 ∧ secondImag ≠ 0 ∧
      target.charpoly =
        conjugatePairQuadratic firstReal firstImag *
          conjugatePairQuadratic secondReal secondImag

/-- The sole remaining presentation theorem on this spectral sector. -/
def PureNonrealJordanPresentationBridge4 : Prop :=
  ∀ target : Matrix4, PureNonrealConjugatePairCharpoly4 target →
    HasPureNonrealJordanPresentation4 target

theorem pureNonrealCharpoly_hasRealSquareRoot
    (bridge : PureNonrealJordanPresentationBridge4)
    {target : Matrix4} (hSpectrum : PureNonrealConjugatePairCharpoly4 target) :
    HasRealSquareRoot target :=
  hasRealSquareRoot_of_pureNonrealJordanPresentation
    (bridge target hSpectrum)

end

end P0EFTJanusComplexConjugatePairRoot4D
end JanusFormal
