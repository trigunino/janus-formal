import Mathlib

namespace JanusFormal
namespace P0EFTJanusGradedFusionRules

set_option autoImplicit false

/-- Twice the `Spin(3)=SU(2)` spin, so all labels are natural numbers. -/
abbrev TwiceSpin := ℕ

/-- Triangle condition for three `SU(2)` labels. -/
def TriangleAllowed
    (first second third : TwiceSpin) : Prop :=
  first ≤ second + third /\
  second ≤ first + third /\
  third ≤ first + second

/-- Arithmetic Clebsch--Gordan singlet criterion for a trilinear invariant. -/
def Spin3TripleSinglet
    (first second third : TwiceSpin) : Prop :=
  TriangleAllowed first second third /\
  Even (first + second + third)

instance spin3TripleSingletDecidable
    (first second third : TwiceSpin) :
    Decidable (Spin3TripleSinglet first second third) := by
  unfold Spin3TripleSinglet TriangleAllowed
  infer_instance

/-- Low-spin labels used by Janus. -/
def scalarSpin : TwiceSpin := 0

def fundamentalSpinorSpin : TwiceSpin := 1

def vectorSpin : TwiceSpin := 2

def spinTwoSpin : TwiceSpin := 4

/-- A scalar occurs in a bilinear tensor product exactly for equal self-dual spin labels. -/
def Spin3BilinearSinglet
    (first second : TwiceSpin) : Prop :=
  first = second

@[simp] theorem scalar_scalar_bilinear_singlet :
    Spin3BilinearSinglet scalarSpin scalarSpin := by
  rfl

@[simp] theorem vector_vector_bilinear_singlet :
    Spin3BilinearSinglet vectorSpin vectorSpin := by
  rfl

@[simp] theorem spin_two_spin_two_bilinear_singlet :
    Spin3BilinearSinglet spinTwoSpin spinTwoSpin := by
  rfl

@[simp] theorem spinor_spinor_bilinear_singlet :
    Spin3BilinearSinglet fundamentalSpinorSpin fundamentalSpinorSpin := by
  rfl

@[simp] theorem scalar_vector_bilinear_not_singlet :
    Not (Spin3BilinearSinglet scalarSpin vectorSpin) := by
  norm_num [Spin3BilinearSinglet, scalarSpin, vectorSpin]

@[simp] theorem vector_vector_scalar_trilinear_singlet :
    Spin3TripleSinglet vectorSpin vectorSpin scalarSpin := by
  native_decide

@[simp] theorem vector_vector_spin_two_trilinear_singlet :
    Spin3TripleSinglet vectorSpin vectorSpin spinTwoSpin := by
  native_decide

@[simp] theorem spin_two_cubic_trilinear_singlet :
    Spin3TripleSinglet spinTwoSpin spinTwoSpin spinTwoSpin := by
  native_decide

@[simp] theorem vector_cubic_so3_trilinear_singlet :
    Spin3TripleSinglet vectorSpin vectorSpin vectorSpin := by
  native_decide

@[simp] theorem spinor_spinor_scalar_trilinear_singlet :
    Spin3TripleSinglet
      fundamentalSpinorSpin fundamentalSpinorSpin scalarSpin := by
  native_decide

@[simp] theorem spinor_spinor_vector_trilinear_singlet :
    Spin3TripleSinglet
      fundamentalSpinorSpin fundamentalSpinorSpin vectorSpin := by
  native_decide

@[simp] theorem spinor_spinor_spin_two_not_trilinear_singlet :
    Not (Spin3TripleSinglet
      fundamentalSpinorSpin fundamentalSpinorSpin spinTwoSpin) := by
  native_decide

/-- Inversion parity needed to distinguish an `O(3)` scalar from a pseudoscalar. -/
abbrev InversionParity := ZMod 2

/-- Polar-vector parity and ordinary even tensor/scalar parity. -/
def scalarInversionParity : InversionParity := 0

def vectorInversionParity : InversionParity := 1

def spinTwoInversionParity : InversionParity := 0

/-- `O(3)` scalar trilinear criterion. -/
def O3TripleScalarAllowed
    (firstSpin secondSpin thirdSpin : TwiceSpin)
    (firstParity secondParity thirdParity : InversionParity) : Prop :=
  Spin3TripleSinglet firstSpin secondSpin thirdSpin /\
  firstParity + secondParity + thirdParity = 0

instance o3TripleScalarAllowedDecidable
    (firstSpin secondSpin thirdSpin : TwiceSpin)
    (firstParity secondParity thirdParity : InversionParity) :
    Decidable (O3TripleScalarAllowed
      firstSpin secondSpin thirdSpin
      firstParity secondParity thirdParity) := by
  unfold O3TripleScalarAllowed
  infer_instance

/-- The epsilon-type vector cubic is an `SO(3)` pseudoscalar, not an `O(3)` scalar. -/
@[simp] theorem vector_cubic_forbidden_by_o3_inversion :
    Not (O3TripleScalarAllowed
      vectorSpin vectorSpin vectorSpin
      vectorInversionParity vectorInversionParity vectorInversionParity) := by
  native_decide

/-- The standard spin-two coupling to two vectors is an ordinary `O(3)` scalar. -/
@[simp] theorem vector_vector_spin_two_o3_scalar :
    O3TripleScalarAllowed
      vectorSpin vectorSpin spinTwoSpin
      vectorInversionParity vectorInversionParity spinTwoInversionParity := by
  native_decide

/-- The spin-two cubic trace invariant is an ordinary `O(3)` scalar. -/
@[simp] theorem spin_two_cubic_o3_scalar :
    O3TripleScalarAllowed
      spinTwoSpin spinTwoSpin spinTwoSpin
      spinTwoInversionParity spinTwoInversionParity spinTwoInversionParity := by
  native_decide

/-- Complete additive grading used before rotation fusion is imposed. -/
@[ext] structure QuantumGrade where
  inversion : ZMod 2
  z4 : ZMod 4
  u1 : ℤ
  ghost : ℤ
  grassmann : ZMod 2
  deriving DecidableEq, Repr

/-- Neutral scalar-action grade. -/
def zeroGrade : QuantumGrade :=
  { inversion := 0
    z4 := 0
    u1 := 0
    ghost := 0
    grassmann := 0 }

/-- Tensor-product grade. -/
def tensorGrade
    (first second : QuantumGrade) : QuantumGrade :=
  { inversion := first.inversion + second.inversion
    z4 := first.z4 + second.z4
    u1 := first.u1 + second.u1
    ghost := first.ghost + second.ghost
    grassmann := first.grassmann + second.grassmann }

/-- Dual/conjugate grade. -/
def dualGrade (grade : QuantumGrade) : QuantumGrade :=
  { inversion := -grade.inversion
    z4 := -grade.z4
    u1 := -grade.u1
    ghost := -grade.ghost
    grassmann := -grade.grassmann }

/-- Neutrality of a tensor monomial. -/
def GradeNeutral (grade : QuantumGrade) : Prop :=
  grade = zeroGrade

instance gradeNeutralDecidable (grade : QuantumGrade) :
    Decidable (GradeNeutral grade) := by
  unfold GradeNeutral
  infer_instance

@[simp] theorem tensor_grade_zero_left
    (grade : QuantumGrade) :
    tensorGrade zeroGrade grade = grade := by
  ext <;> simp [tensorGrade, zeroGrade]

@[simp] theorem tensor_grade_zero_right
    (grade : QuantumGrade) :
    tensorGrade grade zeroGrade = grade := by
  ext <;> simp [tensorGrade, zeroGrade]

@[simp] theorem tensor_grade_assoc
    (first second third : QuantumGrade) :
    tensorGrade (tensorGrade first second) third =
      tensorGrade first (tensorGrade second third) := by
  ext <;> simp [tensorGrade, add_assoc]

@[simp] theorem tensor_grade_comm
    (first second : QuantumGrade) :
    tensorGrade first second = tensorGrade second first := by
  ext <;> simp [tensorGrade, add_comm]

@[simp] theorem dual_grade_involutive
    (grade : QuantumGrade) :
    dualGrade (dualGrade grade) = grade := by
  ext <;> simp [dualGrade]

@[simp] theorem grade_pairs_with_dual
    (grade : QuantumGrade) :
    GradeNeutral (tensorGrade grade (dualGrade grade)) := by
  ext <;> simp [GradeNeutral, tensorGrade, dualGrade, zeroGrade]

/-- Grades of the core sectors. -/
def periodicEvenGrade : QuantumGrade := zeroGrade

/-- The real normal mode is the order-two element inside the normal-root `Z4`. -/
def normalModeGrade : QuantumGrade :=
  { inversion := 0
    z4 := 2
    u1 := 0
    ghost := 0
    grassmann := 0 }

/-- Positive-quarter charged spinor. -/
def positiveQuarterSpinorGrade : QuantumGrade :=
  { inversion := 0
    z4 := 1
    u1 := 1
    ghost := 0
    grassmann := 1 }

/-- Negative-quarter conjugate spinor. -/
def negativeQuarterSpinorGrade : QuantumGrade :=
  { inversion := 0
    z4 := 3
    u1 := -1
    ghost := 0
    grassmann := 1 }

/-- Abelian ghost and antighost. -/
def ghostGrade : QuantumGrade :=
  { inversion := 0
    z4 := 0
    u1 := 0
    ghost := 1
    grassmann := 1 }


def antighostGrade : QuantumGrade :=
  { inversion := 0
    z4 := 0
    u1 := 0
    ghost := -1
    grassmann := 1 }

@[simp] theorem normal_pair_neutral :
    GradeNeutral (tensorGrade normalModeGrade normalModeGrade) := by
  native_decide

@[simp] theorem normal_periodic_mixing_not_neutral :
    Not (GradeNeutral
      (tensorGrade normalModeGrade periodicEvenGrade)) := by
  native_decide

@[simp] theorem quarter_conjugate_pair_neutral :
    GradeNeutral
      (tensorGrade positiveQuarterSpinorGrade
        negativeQuarterSpinorGrade) := by
  native_decide

@[simp] theorem same_positive_quarter_pair_not_neutral :
    Not (GradeNeutral
      (tensorGrade positiveQuarterSpinorGrade
        positiveQuarterSpinorGrade)) := by
  native_decide

@[simp] theorem ghost_antighost_pair_neutral :
    GradeNeutral (tensorGrade ghostGrade antighostGrade) := by
  native_decide

/-- Arithmetic neutrality condition for a monomial with normal modes and charged spinors. -/
def CountNeutral
    (normalCount positiveCount negativeCount : ℕ) : Prop :=
  4 ∣ (2 * normalCount + positiveCount + 3 * negativeCount) /\
  positiveCount = negativeCount

/-- Gauge neutrality plus `Z4` neutrality force an even number of normal modes. -/
theorem neutral_spinor_dressed_normal_count_even
    (normalCount positiveCount negativeCount : ℕ)
    (hNeutral : CountNeutral
      normalCount positiveCount negativeCount) :
    Even normalCount := by
  rcases hNeutral with ⟨hZ4, hGauge⟩
  subst negativeCount
  rcases hZ4 with ⟨winding, hWinding⟩
  refine ⟨winding - positiveCount, ?_⟩
  omega

/-- Pure-normal `Z4` neutrality is equivalent to even degree. -/
theorem pure_normal_neutral_iff_even
    (normalCount : ℕ) :
    4 ∣ 2 * normalCount ↔ Even normalCount := by
  constructor
  · intro hNeutral
    rcases hNeutral with ⟨winding, hWinding⟩
    refine ⟨winding, ?_⟩
    omega
  · rintro ⟨half, hHalf⟩
    refine ⟨half, ?_⟩
    omega

@[simp] theorem normal_linear_term_forbidden :
    Not (4 ∣ 2 * 1) := by
  norm_num

@[simp] theorem normal_quadratic_term_allowed :
    4 ∣ 2 * 2 := by
  norm_num

@[simp] theorem normal_cubic_term_forbidden :
    Not (4 ∣ 2 * 3) := by
  norm_num

@[simp] theorem normal_quartic_term_allowed :
    4 ∣ 2 * 4 := by
  norm_num

/-- One normal mode cannot dress a neutral conjugate spinor bilinear. -/
@[simp] theorem normal_times_conjugate_spinor_bilinear_forbidden :
    Not (CountNeutral 1 1 1) := by
  norm_num [CountNeutral]

/-- Two normal modes may dress a neutral conjugate spinor bilinear. -/
@[simp] theorem normal_squared_times_conjugate_spinor_bilinear_allowed :
    CountNeutral 2 1 1 := by
  norm_num [CountNeutral]

/-- A normal mode repairs the `Z4` phase of two positive spinors but not their `U(1)` charge. -/
@[simp] theorem normal_times_same_positive_spinors_still_forbidden :
    Not (CountNeutral 1 2 0) := by
  norm_num [CountNeutral]

/-- Raw singlet-channel count for four identical `Spin(3)` irreducibles. -/
def IdenticalFourPointChannelCount
    (twiceSpin : TwiceSpin) : ℕ :=
  twiceSpin + 1

@[simp] theorem spinor_four_point_has_two_raw_channels :
    IdenticalFourPointChannelCount fundamentalSpinorSpin = 2 := by
  rfl

@[simp] theorem vector_four_point_has_three_raw_channels :
    IdenticalFourPointChannelCount vectorSpin = 3 := by
  rfl

@[simp] theorem spin_two_four_point_has_five_raw_channels :
    IdenticalFourPointChannelCount spinTwoSpin = 5 := by
  rfl

/--
P.E fusion verdict: bilinear multiplicity-one does not imply nonlinear
uniqueness.  Four identical vectors already have three raw recoupling channels,
and four spin-two fields have five.  Statistics and permutation/crossing
symmetry may reduce these numbers, but that is an additional theorem.
-/
structure GradedFusionPhysicalStatus where
  actualSpin3RepresentationsConstructed : Prop
  clebschGordanRuleProved : Prop
  inversionParityDerived : Prop
  z4AndGaugeGradesDerived : Prop
  ghostAndGrassmannGradesDerived : Prop
  bilinearSelectionRulesApplied : Prop
  trilinearSelectionRulesApplied : Prop
  quarticChannelMultiplicitiesComputed : Prop
  permutationSymmetryReductionComputed : Prop
  survivingCouplingsNormalized : Prop


def gradedFusionPhysicalClosure
    (s : GradedFusionPhysicalStatus) : Prop :=
  s.actualSpin3RepresentationsConstructed /\
  s.clebschGordanRuleProved /\
  s.inversionParityDerived /\
  s.z4AndGaugeGradesDerived /\
  s.ghostAndGrassmannGradesDerived /\
  s.bilinearSelectionRulesApplied /\
  s.trilinearSelectionRulesApplied /\
  s.quarticChannelMultiplicitiesComputed /\
  s.permutationSymmetryReductionComputed /\
  s.survivingCouplingsNormalized

end P0EFTJanusGradedFusionRules
end JanusFormal
