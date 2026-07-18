import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableSylvesterInverse4D

/-!
# Unified selector for positive real Jordan partitions in dimension four

All five positive real Jordan partitions of four are represented by one
typed sum.  The selector dispatches to the already proved blockwise roots,
has an exact square and a bijective Sylvester operator, and is continuous on
each presentation stratum.  Only the existence of such a presentation for an
arbitrary raw matrix remains an explicit hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRealJordanPartitionSelector4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusTwoRoot4D
open P0EFTJanusPositiveJordanThreePlusOneRoot4D
open P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalSylvesterInverse.Matrix4

/-- Exact one-block size-four locus inside the complete single-eigenvalue
gate.  In dimension four, nonvanishing of the nilpotent cube forces one
Jordan block of size four. -/
def strictPositiveBlock4Locus : Set PositiveSingleEigenvalueJordanData :=
  {data | scaledJordanNilpotent data * scaledJordanNilpotent data *
    scaledJordanNilpotent data ≠ 0}

abbrev StrictPositiveBlock4Data := strictPositiveBlock4Locus

/-- Topology-friendly positive diagonal presentation.  The supplied spectrum
contains the four target eigenvalues, not their square roots. -/
abbrev TargetSpectrum4 := Fin 4 → Real

def positiveTargetSpectrumLocus4 : Set TargetSpectrum4 :=
  {spectrum | ∀ index, 0 < spectrum index}

abbrev PositiveTargetSpectrum4 := positiveTargetSpectrumLocus4

abbrev RawPositiveDiagonalPresentation4 :=
  PositiveTargetSpectrum4 × (Matrix4 × Matrix4)

def positiveDiagonalPresentationLocus4 :
    Set RawPositiveDiagonalPresentation4 :=
  {data | data.2.2 * data.2.1 = 1 ∧ data.2.1 * data.2.2 = 1}

abbrev PositiveDiagonalPresentation4 := positiveDiagonalPresentationLocus4

def diagonalPresentationSpectrum
    (data : PositiveDiagonalPresentation4) : PositiveTargetSpectrum4 :=
  data.1.1

def diagonalPresentationChange
    (data : PositiveDiagonalPresentation4) : Matrix4 :=
  data.1.2.1

def diagonalPresentationInverse
    (data : PositiveDiagonalPresentation4) : Matrix4 :=
  data.1.2.2

def diagonalPresentationTarget
    (data : PositiveDiagonalPresentation4) : Matrix4 :=
  diagonalPresentationChange data *
    Matrix.diagonal (diagonalPresentationSpectrum data).1 *
    diagonalPresentationInverse data

def diagonalPresentationAsPositiveDiagonalizable
    (data : PositiveDiagonalPresentation4) :
    PositiveDiagonalizableRelativeMatrix where
  target := diagonalPresentationTarget data
  eigenbasis := diagonalPresentationChange data
  eigenbasisInv := diagonalPresentationInverse data
  eigenvalue := (diagonalPresentationSpectrum data).1
  eigenvalue_pos := (diagonalPresentationSpectrum data).2
  inv_mul_basis := data.property.1
  basis_mul_inv := data.property.2
  target_eq := rfl

def diagonalPresentationRoot
    (data : PositiveDiagonalPresentation4) : Matrix4 :=
  positiveSimilarityRoot (diagonalPresentationAsPositiveDiagonalizable data)

theorem diagonalPresentationRoot_square
    (data : PositiveDiagonalPresentation4) :
    diagonalPresentationRoot data * diagonalPresentationRoot data =
      diagonalPresentationTarget data := by
  exact positiveSimilarityRoot_square
    (diagonalPresentationAsPositiveDiagonalizable data)

theorem diagonalPresentationSylvester_bijective
    (data : PositiveDiagonalPresentation4) :
    Function.Bijective (sylvesterOperator (diagonalPresentationRoot data)) :=
  positiveDiagonalizable_sylvester_bijective
    (diagonalPresentationAsPositiveDiagonalizable data)

theorem diagonalPresentationRoot_continuous :
    Continuous diagonalPresentationRoot := by
  have hSpectrum : Continuous
      (fun data : PositiveDiagonalPresentation4 =>
        (diagonalPresentationSpectrum data).1) := by
    unfold diagonalPresentationSpectrum
    fun_prop
  have hRootSpectrum : Continuous
      (fun data : PositiveDiagonalPresentation4 =>
        fun index => Real.sqrt ((diagonalPresentationSpectrum data).1 index)) := by
    apply continuous_pi
    intro index
    exact Real.continuous_sqrt.comp ((continuous_apply index).comp hSpectrum)
  have hDiagonal : Continuous
      (fun data : PositiveDiagonalPresentation4 =>
        Matrix.diagonal
          (fun index =>
            Real.sqrt ((diagonalPresentationSpectrum data).1 index))) :=
    hRootSpectrum.matrix_diagonal
  have hChange : Continuous diagonalPresentationChange := by
    unfold diagonalPresentationChange
    fun_prop
  have hInverse : Continuous diagonalPresentationInverse := by
    unfold diagonalPresentationInverse
    fun_prop
  unfold diagonalPresentationRoot positiveSimilarityRoot
    positiveSimilarityDiagonalRoot positiveSimilarityRootSpectrum
    diagonalPresentationAsPositiveDiagonalizable
  exact (hChange.matrix_mul hDiagonal).matrix_mul hInverse

/-- The five exact positive real Jordan partitions in dimension four. -/
inductive PositiveRealJordanPresentation4 where
  | block4 : StrictPositiveBlock4Data → PositiveRealJordanPresentation4
  | block31 : Jordan31Data → PositiveRealJordanPresentation4
  | block22 : Jordan22Data → PositiveRealJordanPresentation4
  | block211 : Jordan211Data → PositiveRealJordanPresentation4
  | diagonal : PositiveDiagonalPresentation4 → PositiveRealJordanPresentation4

def presentationTarget : PositiveRealJordanPresentation4 → Matrix4
  | .block4 data => selectedTarget data.1
  | .block31 data => jordan31Target data
  | .block22 data => jordan22Target data
  | .block211 data => jordan211Target data
  | .diagonal data => diagonalPresentationTarget data

/-- One selector, with no branch ambiguity once a typed presentation is
supplied. -/
def positiveRealJordanSelector : PositiveRealJordanPresentation4 → Matrix4
  | .block4 data => positiveSingleEigenvalueJordanRoot data.1
  | .block31 data => jordan31Root data
  | .block22 data => jordan22Root data
  | .block211 data => jordan211Root data
  | .diagonal data => diagonalPresentationRoot data

@[simp]
theorem positiveRealJordanSelector_block4 (data : StrictPositiveBlock4Data) :
    positiveRealJordanSelector (.block4 data) =
      positiveSingleEigenvalueJordanRoot data.1 := rfl

@[simp]
theorem positiveRealJordanSelector_block31 (data : Jordan31Data) :
    positiveRealJordanSelector (.block31 data) = jordan31Root data := rfl

@[simp]
theorem positiveRealJordanSelector_block22 (data : Jordan22Data) :
    positiveRealJordanSelector (.block22 data) = jordan22Root data := rfl

@[simp]
theorem positiveRealJordanSelector_block211 (data : Jordan211Data) :
    positiveRealJordanSelector (.block211 data) = jordan211Root data := rfl

@[simp]
theorem positiveRealJordanSelector_diagonal
    (data : PositiveDiagonalPresentation4) :
    positiveRealJordanSelector (.diagonal data) =
      diagonalPresentationRoot data := rfl

theorem positiveRealJordanSelector_square
    (presentation : PositiveRealJordanPresentation4) :
    positiveRealJordanSelector presentation *
        positiveRealJordanSelector presentation =
      presentationTarget presentation := by
  cases presentation with
  | block4 data => exact positiveSingleEigenvalueJordanRoot_square data.1
  | block31 data => exact jordan31Root_square data
  | block22 data => exact jordan22Root_square data
  | block211 data => exact jordan211Root_square data
  | diagonal data => exact diagonalPresentationRoot_square data

theorem positiveRealJordanSelector_sylvester_bijective
    (presentation : PositiveRealJordanPresentation4) :
    Function.Bijective
      (sylvesterOperator (positiveRealJordanSelector presentation)) := by
  cases presentation with
  | block4 data =>
      change Function.Bijective
        (sylvesterOperator (positiveSingleEigenvalueJordanRoot data.1))
      have hOperator :
          (sylvesterOperator (positiveSingleEigenvalueJordanRoot data.1) :
              Matrix4 → Matrix4) =
            positiveSingleEigenvalueSylvester data.1 := by
        funext variation
        rfl
      rw [hOperator]
      exact positiveSingleEigenvalueSylvester_bijective data.1
  | block31 data => exact jordan31Sylvester_bijective data
  | block22 data => exact jordan22Sylvester_bijective data
  | block211 data => exact jordan211Sylvester_bijective data
  | diagonal data => exact diagonalPresentationSylvester_bijective data

/-- Continuity is asserted on each stratum, without claiming that distinct
Jordan strata glue continuously across degenerations. -/
theorem positiveRealJordanSelector_continuous_block4 :
    Continuous (fun data : StrictPositiveBlock4Data =>
      positiveRealJordanSelector (.block4 data)) :=
  positiveSingleEigenvalueJordanRoot_continuous.comp continuous_subtype_val

theorem positiveRealJordanSelector_continuous_block31 :
    Continuous (fun data : Jordan31Data =>
      positiveRealJordanSelector (.block31 data)) :=
  jordan31Root_continuous

theorem positiveRealJordanSelector_continuous_block22 :
    Continuous (fun data : Jordan22Data =>
      positiveRealJordanSelector (.block22 data)) :=
  jordan22Root_continuous

theorem positiveRealJordanSelector_continuous_block211 :
    Continuous (fun data : Jordan211Data =>
      positiveRealJordanSelector (.block211 data)) :=
  jordan211Root_continuous

theorem positiveRealJordanSelector_continuous_diagonal :
    Continuous (fun data : PositiveDiagonalPresentation4 =>
      positiveRealJordanSelector (.diagonal data)) :=
  diagonalPresentationRoot_continuous

/-- Exhaustive Presburger classification of decreasing, zero-padded block
sizes with total dimension four. -/
theorem positiveRealJordanPartitions4_exhaustive
    (first second third fourth : Nat) :
    (first ≥ second ∧ second ≥ third ∧ third ≥ fourth ∧
        first + second + third + fourth = 4) ↔
      (first = 4 ∧ second = 0 ∧ third = 0 ∧ fourth = 0) ∨
      (first = 3 ∧ second = 1 ∧ third = 0 ∧ fourth = 0) ∨
      (first = 2 ∧ second = 2 ∧ third = 0 ∧ fourth = 0) ∨
      (first = 2 ∧ second = 1 ∧ third = 1 ∧ fourth = 0) ∨
      (first = 1 ∧ second = 1 ∧ third = 1 ∧ fourth = 1) := by
  omega

/-- This is the sole remaining matrix-level hypothesis: a raw matrix must be
equipped with one of the five positive real Jordan presentations. -/
def HasPositiveRealJordanPresentation (target : Matrix4) : Prop :=
  ∃ presentation : PositiveRealJordanPresentation4,
    presentationTarget presentation = target

def PositiveRealJordanPresentableMatrix :=
  {target : Matrix4 // HasPositiveRealJordanPresentation target}

noncomputable def chosenPositiveRealJordanPresentation
    (target : PositiveRealJordanPresentableMatrix) :
    PositiveRealJordanPresentation4 :=
  Classical.choose target.property

theorem chosenPositiveRealJordanPresentation_target
    (target : PositiveRealJordanPresentableMatrix) :
    presentationTarget (chosenPositiveRealJordanPresentation target) = target.1 :=
  Classical.choose_spec target.property

noncomputable def positiveRealJordanRootOfPresentable
    (target : PositiveRealJordanPresentableMatrix) : Matrix4 :=
  positiveRealJordanSelector (chosenPositiveRealJordanPresentation target)

theorem positiveRealJordanRootOfPresentable_square
    (target : PositiveRealJordanPresentableMatrix) :
    positiveRealJordanRootOfPresentable target *
        positiveRealJordanRootOfPresentable target = target.1 := by
  rw [positiveRealJordanRootOfPresentable,
    positiveRealJordanSelector_square,
    chosenPositiveRealJordanPresentation_target]

theorem positiveRealJordanRootOfPresentable_sylvester_bijective
    (target : PositiveRealJordanPresentableMatrix) :
    Function.Bijective
      (sylvesterOperator (positiveRealJordanRootOfPresentable target)) :=
  positiveRealJordanSelector_sylvester_bijective
    (chosenPositiveRealJordanPresentation target)

end

end P0EFTJanusPositiveRealJordanPartitionSelector4D
end JanusFormal
