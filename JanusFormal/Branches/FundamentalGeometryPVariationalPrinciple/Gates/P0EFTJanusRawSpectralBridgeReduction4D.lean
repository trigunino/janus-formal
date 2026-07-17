import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUnifiedSpectralSquareRootDomain4D
import Mathlib.Analysis.Matrix.Order

/-!
# Raw spectral bridge reduction in dimension four

Two sizeable raw loci can be closed without a Jordan presentation:

* positive-semidefinite real matrices, using Mathlib's continuous functional
  calculus square root;
* matrices satisfying one irreducible real quadratic relation, using an
  affine polynomial in the matrix itself.

The original presentation bridges are therefore stronger than root
existence requires.  This gate states exact residual root obligations after
removing those unconditional loci.  It does not claim that Mathlib currently
constructs the missing real Jordan presentations.
-/

namespace JanusFormal
namespace P0EFTJanusRawSpectralBridgeReduction4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusComplexConjugatePairRoot4D
open P0EFTJanusUnifiedSpectralSquareRootDomain4D

abbrev Matrix4 := P0EFTJanusUnifiedSpectralSquareRootDomain4D.Matrix4

/-- Mathlib's canonical nonnegative functional-calculus root. -/
def cfcNonnegativeRoot4 (target : Matrix4) : Matrix4 :=
  CFC.sqrt target

theorem cfcNonnegativeRoot4_square
    {target : Matrix4} (hTarget : target.PosSemidef) :
    cfcNonnegativeRoot4 target * cfcNonnegativeRoot4 target = target := by
  have hSquare := CFC.sq_sqrt target hTarget.nonneg
  simpa [cfcNonnegativeRoot4, pow_two] using hSquare

theorem posSemidef_hasRealSquareRoot
    {target : Matrix4} (hTarget : target.PosSemidef) :
    HasRealSquareRoot target :=
  ⟨cfcNonnegativeRoot4 target, cfcNonnegativeRoot4_square hTarget⟩

/-- Root-level closure requested by the positive raw spectral condition. -/
def PositiveRawRootClosure4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    HasRealSquareRoot target

/-- Exact residual after removing the positive-semidefinite locus already
handled by continuous functional calculus. -/
def PositiveNonPosSemidefRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → HasRealSquareRoot target

theorem positiveRawRootClosure_iff_nonPosSemidefResidual :
    PositiveRawRootClosure4 ↔ PositiveNonPosSemidefRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotPosSemidef
    exact closure target hSpectrum
  · intro residual target hSpectrum
    by_cases hPosSemidef : target.PosSemidef
    · exact posSemidef_hasRealSquareRoot hPosSemidef
    · exact residual target hSpectrum hPosSemidef

/-- A raw irreducible-quadratic relation, requiring no eigenbasis or real
canonical presentation. -/
def HasSingleComplexQuadraticRelation4 (target : Matrix4) : Prop :=
  ∃ realPart imaginaryPart : Real,
    imaginaryPart ≠ 0 ∧
      let shifted := target - realPart • (1 : Matrix4)
      shifted * shifted = -(imaginaryPart ^ 2) • (1 : Matrix4)

/-- Affine polynomial root on a supplied quadratic relation. -/
def singleComplexQuadraticRoot4
    (target : Matrix4) (realPart imaginaryPart : Real) : Matrix4 :=
  let rootReal := complexPairPrincipalRootReal realPart imaginaryPart
  let rootImag := complexPairRootImag realPart imaginaryPart
  rootReal • (1 : Matrix4) +
    (rootImag / imaginaryPart) •
      (target - realPart • (1 : Matrix4))

theorem singleComplexQuadraticRoot4_square
    {target : Matrix4} {realPart imaginaryPart : Real}
    (hImaginary : imaginaryPart ≠ 0)
    (hRelation :
      let shifted := target - realPart • (1 : Matrix4)
      shifted * shifted = -(imaginaryPart ^ 2) • (1 : Matrix4)) :
    singleComplexQuadraticRoot4 target realPart imaginaryPart *
        singleComplexQuadraticRoot4 target realPart imaginaryPart = target := by
  let rootReal := complexPairPrincipalRootReal realPart imaginaryPart
  let rootImag := complexPairRootImag realPart imaginaryPart
  let coefficient := rootImag / imaginaryPart
  let shifted := target - realPart • (1 : Matrix4)
  have hRelation' :
      shifted * shifted = -(imaginaryPart ^ 2) • (1 : Matrix4) :=
    hRelation
  obtain ⟨hReal, hImag⟩ :=
    complexPairRoot_coefficients realPart imaginaryPart
  have hRealCoefficient :
      rootReal * rootReal -
          coefficient * coefficient * imaginaryPart ^ 2 = realPart := by
    dsimp [rootReal, rootImag, coefficient]
    field_simp [hImaginary]
    nlinarith
  have hShiftedCoefficient :
      rootReal * coefficient + coefficient * rootReal = 1 := by
    dsimp [rootReal, rootImag, coefficient]
    field_simp [hImaginary]
    nlinarith
  change
    (rootReal • (1 : Matrix4) + coefficient • shifted) *
        (rootReal • (1 : Matrix4) + coefficient • shifted) = target
  calc
    (rootReal • (1 : Matrix4) + coefficient • shifted) *
        (rootReal • (1 : Matrix4) + coefficient • shifted) =
      (rootReal * rootReal -
          coefficient * coefficient * imaginaryPart ^ 2) •
            (1 : Matrix4) +
        (rootReal * coefficient + coefficient * rootReal) • shifted := by
      rw [add_mul, mul_add, mul_add]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_smul]
      rw [hRelation']
      simp only [smul_smul]
      module
    _ = realPart • (1 : Matrix4) + shifted := by
      rw [hRealCoefficient, hShiftedCoefficient]
      simp
    _ = target := by
      dsimp [shifted]
      abel

theorem singleComplexQuadraticRelation_hasRealSquareRoot
    {target : Matrix4} (hTarget : HasSingleComplexQuadraticRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨realPart, imaginaryPart, hImaginary, hRelation⟩ := hTarget
  exact ⟨singleComplexQuadraticRoot4 target realPart imaginaryPart,
    singleComplexQuadraticRoot4_square hImaginary hRelation⟩

/-- The canonical repeated conjugate-pair block satisfies the raw quadratic
relation, showing that the new theorem genuinely avoids presentation data. -/
theorem repeatedComplexPairSum_hasSingleQuadraticRelation
    (realPart imaginaryPart : Real) (hImaginary : imaginaryPart ≠ 0) :
    HasSingleComplexQuadraticRelation4
      (complexPairSumTarget4
        realPart imaginaryPart realPart imaginaryPart) := by
  refine ⟨realPart, imaginaryPart, hImaginary, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPairSumTarget4, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- Root-level closure requested by the purely nonreal raw charpoly sector. -/
def PureNonrealRawRootClosure4 : Prop :=
  ∀ target : Matrix4, PureNonrealConjugatePairCharpoly4 target →
    HasRealSquareRoot target

/-- Exact residual after removing all targets already satisfying one raw
irreducible quadratic relation. -/
def PureNonrealOutsideSingleQuadraticResidual4 : Prop :=
  ∀ target : Matrix4, PureNonrealConjugatePairCharpoly4 target →
    ¬ HasSingleComplexQuadraticRelation4 target →
      HasRealSquareRoot target

theorem pureNonrealRawRootClosure_iff_outsideSingleQuadraticResidual :
    PureNonrealRawRootClosure4 ↔
      PureNonrealOutsideSingleQuadraticResidual4 := by
  constructor
  · intro closure target hSpectrum _hOutside
    exact closure target hSpectrum
  · intro residual target hSpectrum
    by_cases hQuadratic : HasSingleComplexQuadraticRelation4 target
    · exact singleComplexQuadraticRelation_hasRealSquareRoot hQuadratic
    · exact residual target hSpectrum hQuadratic

/-- Union of the two raw loci closed in this gate. -/
def UnconditionalRawSquareRootLocus4 (target : Matrix4) : Prop :=
  target.PosSemidef ∨ HasSingleComplexQuadraticRelation4 target

theorem unconditionalRawLocus_hasRealSquareRoot
    {target : Matrix4} (hTarget : UnconditionalRawSquareRootLocus4 target) :
    HasRealSquareRoot target := by
  rcases hTarget with hPosSemidef | hQuadratic
  · exact posSemidef_hasRealSquareRoot hPosSemidef
  · exact singleComplexQuadraticRelation_hasRealSquareRoot hQuadratic

/-- Necessity half of the exact real Jordan criterion.  It remains a raw
classification obligation because generalized-kernel counts are not yet
connected to a Jordan-chain basis in Mathlib. -/
def JordanCriterionNecessityResidual4 : Prop :=
  ∀ target : Matrix4, HasRealSquareRoot target →
    RealSquareRootJordanCriterion4 target

/-- Sufficiency residual only on matrices outside the two unconditional raw
loci above. -/
def JordanCriterionOutsideUnconditionalSufficiencyResidual4 : Prop :=
  ∀ target : Matrix4, RealSquareRootJordanCriterion4 target →
    ¬ UnconditionalRawSquareRootLocus4 target →
      HasRealSquareRoot target

/-- Exact reconstruction of the former full Jordan-classification bridge
from its necessity half and the strictly smaller sufficiency residual. -/
def rebuildJordanClassificationBridge4
    (necessity : JordanCriterionNecessityResidual4)
    (sufficiency :
      JordanCriterionOutsideUnconditionalSufficiencyResidual4) :
    RealSquareRootJordanClassificationBridge4 := by
  intro target
  constructor
  · exact necessity target
  · intro hCriterion
    by_cases hUnconditional : UnconditionalRawSquareRootLocus4 target
    · exact unconditionalRawLocus_hasRealSquareRoot hUnconditional
    · exact sufficiency target hCriterion hUnconditional

theorem jordanClassificationBridge4_iff_reducedResiduals :
    RealSquareRootJordanClassificationBridge4 ↔
      JordanCriterionNecessityResidual4 ∧
        JordanCriterionOutsideUnconditionalSufficiencyResidual4 := by
  constructor
  · intro bridge
    constructor
    · intro target hRoot
      exact (bridge target).1 hRoot
    · intro target hCriterion _hOutside
      exact (bridge target).2 hCriterion
  · rintro ⟨necessity, sufficiency⟩
    exact rebuildJordanClassificationBridge4 necessity sufficiency

/-- Reduced root-level obligations replacing the stronger presentation
bundle whenever only square-root existence is consumed. -/
structure ReducedRawRootResiduals4 where
  positiveOutsideCFC : PositiveNonPosSemidefRootResidual4
  pureNonrealOutsideQuadratic :
    PureNonrealOutsideSingleQuadraticResidual4
  jordanNecessity : JordanCriterionNecessityResidual4
  jordanOutsideUnconditional :
    JordanCriterionOutsideUnconditionalSufficiencyResidual4

def ReducedRawRootResiduals4.positiveClosure
    (residuals : ReducedRawRootResiduals4) : PositiveRawRootClosure4 :=
  positiveRawRootClosure_iff_nonPosSemidefResidual.2
    residuals.positiveOutsideCFC

def ReducedRawRootResiduals4.pureNonrealClosure
    (residuals : ReducedRawRootResiduals4) : PureNonrealRawRootClosure4 :=
  pureNonrealRawRootClosure_iff_outsideSingleQuadraticResidual.2
    residuals.pureNonrealOutsideQuadratic

def ReducedRawRootResiduals4.jordanClassification
    (residuals : ReducedRawRootResiduals4) :
    RealSquareRootJordanClassificationBridge4 :=
  rebuildJordanClassificationBridge4 residuals.jordanNecessity
    residuals.jordanOutsideUnconditional

/-- Every former presentation/classification bundle implies the reduced
root-level obligations.  The converse is deliberately not asserted because
a root does not manufacture a Jordan presentation. -/
def RawMatrixSpectralBridges4.toReducedRawRootResiduals
    (bridges : RawMatrixSpectralBridges4) : ReducedRawRootResiduals4 where
  positiveOutsideCFC := by
    intro target hSpectrum _hOutside
    exact ⟨rawSpectralRoot bridges (.positive hSpectrum),
      rawSpectralRoot_square bridges (.positive hSpectrum)⟩
  pureNonrealOutsideQuadratic := by
    intro target hSpectrum _hOutside
    exact ⟨rawSpectralRoot bridges (.pureNonreal hSpectrum),
      rawSpectralRoot_square bridges (.pureNonreal hSpectrum)⟩
  jordanNecessity := by
    intro target hRoot
    exact (bridges.jordanClassification target).1 hRoot
  jordanOutsideUnconditional := by
    intro target hCriterion _hOutside
    exact (bridges.jordanClassification target).2 hCriterion

/-- Raw selector using only the reduced root obligations, bypassing both
presentation bridges. -/
noncomputable def reducedRawSpectralRoot
    (residuals : ReducedRawRootResiduals4)
    {target : Matrix4} : RawSpectralCertificate4 target → Matrix4
  | .positive hSpectrum =>
      Classical.choose (residuals.positiveClosure target hSpectrum)
  | .jordanCriterion hCriterion =>
      Classical.choose
        ((residuals.jordanClassification target).2 hCriterion)
  | .pureNonreal hSpectrum =>
      Classical.choose (residuals.pureNonrealClosure target hSpectrum)

theorem reducedRawSpectralRoot_square
    (residuals : ReducedRawRootResiduals4)
    {target : Matrix4} (certificate : RawSpectralCertificate4 target) :
    reducedRawSpectralRoot residuals certificate *
        reducedRawSpectralRoot residuals certificate = target := by
  cases certificate with
  | positive hSpectrum =>
      exact Classical.choose_spec
        (residuals.positiveClosure target hSpectrum)
  | jordanCriterion hCriterion =>
      exact Classical.choose_spec
        ((residuals.jordanClassification target).2 hCriterion)
  | pureNonreal hSpectrum =>
      exact Classical.choose_spec
        (residuals.pureNonrealClosure target hSpectrum)

end

end P0EFTJanusRawSpectralBridgeReduction4D
end JanusFormal
