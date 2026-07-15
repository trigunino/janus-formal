import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalSylvesterInverse

/-!
# Local co-diagonal Lorentz square-root chart

For two positive scale spectra `sPlus` and `sMinus`, this file constructs

`gPlus  = diag (-sPlus_0^2,  sPlus_1^2,  sPlus_2^2,  sPlus_3^2)`,
`gMinus = diag (-sMinus_0^2, sMinus_1^2, sMinus_2^2, sMinus_3^2)`

and the positive diagonal relative root

`X = diag (sMinus_i / sPlus_i)`.

The inverse metrics and root are explicit, `X^2 = gPlus^{-1} gMinus`, the
root determinant is positive, and the root is unique among positive diagonal
roots.  The already constructed positive-diagonal Sylvester inverse therefore
applies on this chart.

This is a local co-diagonal chart with a shared timelike coordinate and shared
spacelike coordinate hyperplane.  It is not the full Hassan--Kocic
causal-compatible Lorentz domain, does not cover non-simultaneously-diagonal
metric pairs, and makes no global branch-continuation claim.
-/

namespace JanusFormal
namespace P0EFTJanusCoDiagonalLorentzRootChart

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

abbrev Spectrum4 := Fin 4 → ℝ

/-- Positive lapse/spatial scales on the co-diagonal chart. -/
abbrev PositiveScales := PositiveDiagonalSpectrum

/-- Diagonal Lorentz signature, with index zero timelike. -/
def lorentzSign (i : Fin 4) : ℝ :=
  if i = 0 then -1 else 1

@[simp]
theorem lorentzSign_sq (i : Fin 4) :
    lorentzSign i * lorentzSign i = 1 := by
  fin_cases i <;> norm_num [lorentzSign]

/-- Co-diagonal Lorentz metric associated with positive scales. -/
def lorentzMetric (scales : PositiveScales) : Matrix4 :=
  Matrix.diagonal (fun i => lorentzSign i * scales.1 i ^ 2)

/-- Explicit inverse of `lorentzMetric`. -/
def lorentzMetricInverse (scales : PositiveScales) : Matrix4 :=
  Matrix.diagonal (fun i => lorentzSign i / scales.1 i ^ 2)

theorem lorentzMetric_symmetric (scales : PositiveScales) :
    (lorentzMetric scales).transpose = lorentzMetric scales := by
  simp [lorentzMetric]

/-- The shared coordinate `0` is timelike. -/
theorem lorentzMetric_time_negative (scales : PositiveScales) :
    lorentzMetric scales 0 0 < 0 := by
  simpa [lorentzMetric, lorentzSign] using
    (sq_pos_of_pos (scales.2 0))

/-- Every nonzero coordinate index is spacelike. -/
theorem lorentzMetric_spatial_positive
    (scales : PositiveScales) (i : Fin 4) (hi : i ≠ 0) :
    0 < lorentzMetric scales i i := by
  simpa [lorentzMetric, lorentzSign, hi] using
    (sq_pos_of_pos (scales.2 i))

theorem lorentzMetric_offDiagonal
    (scales : PositiveScales) (i j : Fin 4) (hij : i ≠ j) :
    lorentzMetric scales i j = 0 := by
  simp [lorentzMetric, hij]

theorem lorentzMetricInverse_mul_metric (scales : PositiveScales) :
    lorentzMetricInverse scales * lorentzMetric scales = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lorentzMetricInverse, lorentzMetric]
    field_simp [ne_of_gt (scales.2 i)]
    nlinarith [lorentzSign_sq i]
  · simp [lorentzMetricInverse, lorentzMetric,
      hij]

theorem lorentzMetric_mul_inverse (scales : PositiveScales) :
    lorentzMetric scales * lorentzMetricInverse scales = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lorentzMetricInverse, lorentzMetric]
    field_simp [ne_of_gt (scales.2 i)]
    nlinarith [lorentzSign_sq i]
  · simp [lorentzMetricInverse, lorentzMetric,
      hij]

/-- The explicit metric inverse packaged in the matrix witness used by
Candidate A. -/
def lorentzMetricInverseWitness (scales : PositiveScales) :
    FrameInverseWitness (lorentzMetric scales) (lorentzMetricInverse scales) :=
  { inverse_mul := lorentzMetricInverse_mul_metric scales
    mul_inverse := lorentzMetric_mul_inverse scales }

/-- Positive eigenvalue ratios of the relative square root. -/
def rootRatioSpectrum
    (plusScales minusScales : PositiveScales) : PositiveDiagonalSpectrum :=
  ⟨fun i => minusScales.1 i / plusScales.1 i,
    fun i => div_pos (minusScales.2 i) (plusScales.2 i)⟩

/-- Positive co-diagonal relative root. -/
def rootMatrix
    (plusScales minusScales : PositiveScales) : Matrix4 :=
  Matrix.diagonal (rootRatioSpectrum plusScales minusScales).1

/-- Explicit inverse root, obtained by reversing the two scale spectra. -/
def rootMatrixInverse
    (plusScales minusScales : PositiveScales) : Matrix4 :=
  rootMatrix minusScales plusScales

theorem rootMatrixInverse_mul_rootMatrix
    (plusScales minusScales : PositiveScales) :
    rootMatrixInverse plusScales minusScales *
        rootMatrix plusScales minusScales = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rootMatrixInverse, rootMatrix, rootRatioSpectrum,
      ne_of_gt (plusScales.2 i),
      ne_of_gt (minusScales.2 i)]
  · simp [rootMatrixInverse, rootMatrix, rootRatioSpectrum,
      hij]

theorem rootMatrix_mul_inverse
    (plusScales minusScales : PositiveScales) :
    rootMatrix plusScales minusScales *
        rootMatrixInverse plusScales minusScales = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rootMatrixInverse, rootMatrix, rootRatioSpectrum,
      ne_of_gt (plusScales.2 i),
      ne_of_gt (minusScales.2 i)]
  · simp [rootMatrixInverse, rootMatrix, rootRatioSpectrum,
      hij]

def rootMatrixInverseWitness
    (plusScales minusScales : PositiveScales) :
    FrameInverseWitness (rootMatrix plusScales minusScales)
      (rootMatrixInverse plusScales minusScales) :=
  { inverse_mul := rootMatrixInverse_mul_rootMatrix plusScales minusScales
    mul_inverse := rootMatrix_mul_inverse plusScales minusScales }

/-- The positive co-diagonal root squares to the actual relative metric. -/
theorem rootMatrix_square_eq_relativeMetric
    (plusScales minusScales : PositiveScales) :
    rootMatrix plusScales minusScales *
        rootMatrix plusScales minusScales =
      lorentzMetricInverse plusScales * lorentzMetric minusScales := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rootMatrix, rootRatioSpectrum, lorentzMetricInverse,
      lorentzMetric]
    field_simp [ne_of_gt (plusScales.2 i)]
    have hSign : lorentzSign i ^ 2 = 1 := by
      rw [pow_two]
      exact lorentzSign_sq i
    rw [hSign, mul_one]
  · simp [rootMatrix, rootRatioSpectrum, lorentzMetricInverse,
      lorentzMetric, hij]

/-- The selected root has positive determinant. -/
theorem rootMatrix_det_pos
    (plusScales minusScales : PositiveScales) :
    0 < Matrix.det (rootMatrix plusScales minusScales) := by
  rw [rootMatrix, Matrix.det_diagonal]
  exact Finset.prod_pos fun i _ =>
    (rootRatioSpectrum plusScales minusScales).2 i

/-- Matrices admissible for the local branch are precisely positive diagonal
matrices. -/
def IsPositiveDiagonalRoot (root : Matrix4) : Prop :=
  ∃ spectrum : PositiveDiagonalSpectrum,
    root = Matrix.diagonal spectrum.1

/-- Positive diagonal square roots of one target are unique. -/
theorem positiveDiagonalRoot_unique
    {left right target : Matrix4}
    (hLeft : IsPositiveDiagonalRoot left)
    (hRight : IsPositiveDiagonalRoot right)
    (hLeftSquare : left * left = target)
    (hRightSquare : right * right = target) :
    left = right := by
  rcases hLeft with ⟨leftSpectrum, rfl⟩
  rcases hRight with ⟨rightSpectrum, rfl⟩
  ext i j
  by_cases hij : i = j
  · subst j
    have hEntry := congrArg (fun matrix : Matrix4 => matrix i i)
      (hLeftSquare.trans hRightSquare.symm)
    have hSquares :
        leftSpectrum.1 i * leftSpectrum.1 i =
          rightSpectrum.1 i * rightSpectrum.1 i := by
      simpa [Matrix.diagonal_mul_diagonal] using hEntry
    simp only [Matrix.diagonal_apply_eq]
    nlinarith [leftSpectrum.2 i, rightSpectrum.2 i]
  · simp [hij]

/-- Actual local branch selector, rather than a supplied uniqueness
proposition. -/
def positiveDiagonalRootBranch : SquareRootBranch where
  admissible := IsPositiveDiagonalRoot
  unique := positiveDiagonalRoot_unique

/-- The two Lorentz metrics and their selected root packaged as Candidate-A
point data. -/
def coDiagonalSquareRootPointData
    (plusScales minusScales : PositiveScales) : SquareRootPointData where
  plusMetric := lorentzMetric plusScales
  plusInverse := lorentzMetricInverse plusScales
  minusMetric := lorentzMetric minusScales
  minusInverse := lorentzMetricInverse minusScales
  root := rootMatrix plusScales minusScales
  rootInverse := rootMatrixInverse plusScales minusScales
  branch := positiveDiagonalRootBranch
  plusInverseWitness := lorentzMetricInverseWitness plusScales
  minusInverseWitness := lorentzMetricInverseWitness minusScales
  rootInverseWitness := rootMatrixInverseWitness plusScales minusScales
  plusMetricSymmetric := lorentzMetric_symmetric plusScales
  minusMetricSymmetric := lorentzMetric_symmetric minusScales
  rootDeterminantPositive := rootMatrix_det_pos plusScales minusScales
  squareRootEquation := rootMatrix_square_eq_relativeMetric
    plusScales minusScales
  rootAdmissible :=
    ⟨rootRatioSpectrum plusScales minusScales, rfl⟩

/-- Both metrics have the displayed shared co-diagonal Lorentz signature. -/
theorem coDiagonal_pair_has_shared_time_and_space
    (plusScales minusScales : PositiveScales) :
    lorentzMetric plusScales 0 0 < 0 ∧
      lorentzMetric minusScales 0 0 < 0 ∧
      (∀ i : Fin 4, i ≠ 0 →
        0 < lorentzMetric plusScales i i ∧
          0 < lorentzMetric minusScales i i) := by
  refine ⟨lorentzMetric_time_negative plusScales,
    lorentzMetric_time_negative minusScales, ?_⟩
  intro i hi
  exact ⟨lorentzMetric_spatial_positive plusScales i hi,
    lorentzMetric_spatial_positive minusScales i hi⟩

/-- The co-diagonal Lorentz chart instantiates the explicit two-sided
Sylvester inverse. -/
def coDiagonalSylvesterInverseWitness
    (plusScales minusScales : PositiveScales) :
    SylvesterInverseWitness (rootMatrix plusScales minusScales) := by
  simpa [rootMatrix] using
    positiveDiagonalSylvesterInverseWitness
      (rootRatioSpectrum plusScales minusScales)

/-- Any differentiable square-root selection through this chart has the
explicit entrywise Sylvester derivative.  Existence beyond this chart is not
inferred. -/
theorem coDiagonal_squareRoot_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[ℝ] Matrix4}
    {point : E}
    (plusScales minusScales : PositiveScales)
    (hValue : root point = rootMatrix plusScales minusScales)
    (hRoot : DifferentiableAt ℝ root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    HasFDerivAt root
      ((diagonalSylvesterInverse
        (rootRatioSpectrum plusScales minusScales)).comp targetDerivative)
      point := by
  apply positiveDiagonal_squareRoot_hasFDerivAt
    (rootRatioSpectrum plusScales minusScales)
  · simpa [rootMatrix] using hValue
  · exact hRoot
  · exact hTarget
  · exact hSquare

end

end P0EFTJanusCoDiagonalLorentzRootChart
end JanusFormal
