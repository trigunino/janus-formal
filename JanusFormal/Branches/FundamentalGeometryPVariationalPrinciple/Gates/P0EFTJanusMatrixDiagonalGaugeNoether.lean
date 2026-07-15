import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootInteractionDensity

/-!
Pointwise diagonal frame symmetry of the explicit matrix interaction.

Both metric matrices transform by the same congruence and the relative root
by the induced similarity.  The elementary-symmetric interaction scalar is
invariant.  Its coordinate density is invariant for a volume-preserving
frame; for a general frame the missing Jacobian is deliberately not hidden.

The final theorem differentiates an actual one-parameter similarity orbit and
gives its finite-matrix Noether pairing.  This is not a spacetime
diffeomorphism, a covariant Bianchi identity, or a constraint-algebra result.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixDiagonalGaugeNoether

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixSquareRootInteractionDensity

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- Shared change of frame for a covariant metric matrix. -/
def metricCongruence (frame metric : Matrix4) : Matrix4 :=
  frame.transpose * metric * frame

/-- Induced change of frame for the inverse metric matrix. -/
def inverseMetricCongruence (inverse inverseMetric : Matrix4) : Matrix4 :=
  inverse * inverseMetric * inverse.transpose

/-- The relative square root transforms by similarity. -/
def rootSimilarity (frame inverse root : Matrix4) : Matrix4 :=
  conjugate inverse frame root

theorem reverseFrameInverseWitness
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    FrameInverseWitness inverse frame := by
  exact ⟨hFrame.mul_inverse, hFrame.inverse_mul⟩

theorem conjugate_mul
    (frame inverse left right : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    conjugate inverse frame left * conjugate inverse frame right =
      conjugate inverse frame (left * right) := by
  have hCancel : ∀ x : Matrix4, frame * (inverse * x) = x := by
    intro x
    rw [← Matrix.mul_assoc, hFrame.mul_inverse, Matrix.one_mul]
  unfold conjugate
  noncomm_ring [hCancel]

theorem congruence_symmetric
    (frame metric : Matrix4) (hMetric : metric.transpose = metric) :
    (metricCongruence frame metric).transpose =
      metricCongruence frame metric := by
  simp [metricCongruence, Matrix.transpose_mul, hMetric, Matrix.mul_assoc]

theorem inverseMetricCongruence_is_inverse
    (frame inverse metric inverseMetric : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (hMetric : FrameInverseWitness metric inverseMetric) :
    FrameInverseWitness (metricCongruence frame metric)
      (inverseMetricCongruence inverse inverseMetric) := by
  have hTransposeLeft :
      inverse.transpose * frame.transpose = (1 : Matrix4) := by
    calc
      inverse.transpose * frame.transpose =
          (frame * inverse).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hFrame.mul_inverse, Matrix.transpose_one]
  have hTransposeRight :
      frame.transpose * inverse.transpose = (1 : Matrix4) := by
    calc
      frame.transpose * inverse.transpose =
          (inverse * frame).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hFrame.inverse_mul, Matrix.transpose_one]
  constructor
  · unfold metricCongruence inverseMetricCongruence
    calc
      (inverse * inverseMetric * inverse.transpose) *
          (frame.transpose * metric * frame) =
        inverse *
            (inverseMetric *
              ((inverse.transpose * frame.transpose) * metric)) * frame := by
          simp only [Matrix.mul_assoc]
      _ = inverse * (inverseMetric * metric) * frame := by
        rw [hTransposeLeft, Matrix.one_mul]
      _ = inverse * frame := by
        rw [hMetric.inverse_mul, Matrix.mul_one]
      _ = 1 := hFrame.inverse_mul
  · unfold metricCongruence inverseMetricCongruence
    calc
      (frame.transpose * metric * frame) *
          (inverse * inverseMetric * inverse.transpose) =
        frame.transpose *
            (metric * ((frame * inverse) * inverseMetric)) *
              inverse.transpose := by
          simp only [Matrix.mul_assoc]
      _ = frame.transpose * (metric * inverseMetric) * inverse.transpose := by
        rw [hFrame.mul_inverse, Matrix.one_mul]
      _ = frame.transpose * inverse.transpose := by
        rw [hMetric.mul_inverse, Matrix.mul_one]
      _ = 1 := hTransposeRight

theorem transformedRelativeTarget
    (frame inverse plusInverse minusMetric : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    inverseMetricCongruence inverse plusInverse *
        metricCongruence frame minusMetric =
      conjugate inverse frame (plusInverse * minusMetric) := by
  have hTranspose :
      inverse.transpose * frame.transpose = (1 : Matrix4) := by
    calc
      inverse.transpose * frame.transpose =
          (frame * inverse).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hFrame.mul_inverse, Matrix.transpose_one]
  unfold inverseMetricCongruence metricCongruence conjugate
  calc
    (inverse * plusInverse * inverse.transpose) *
        (frame.transpose * minusMetric * frame) =
      inverse *
          (plusInverse *
            ((inverse.transpose * frame.transpose) * minusMetric)) * frame := by
        simp only [Matrix.mul_assoc]
    _ = inverse * (plusInverse * minusMetric) * frame := by
      rw [hTranspose, Matrix.one_mul]
    _ = inverse * (plusInverse * minusMetric) * frame := rfl

/-- Branch-independent point data on which the diagonal frame action closes.
It is obtained from the committed square-root data by forgetting only the
branch predicate, not any metric inverse or square-root equation. -/
structure PointwiseBimetricRootData where
  plusMetric : Matrix4
  plusInverse : Matrix4
  minusMetric : Matrix4
  minusInverse : Matrix4
  root : Matrix4
  rootInverse : Matrix4
  plusInverseWitness : FrameInverseWitness plusMetric plusInverse
  minusInverseWitness : FrameInverseWitness minusMetric minusInverse
  rootInverseWitness : FrameInverseWitness root rootInverse
  plusMetricSymmetric : plusMetric.transpose = plusMetric
  minusMetricSymmetric : minusMetric.transpose = minusMetric
  rootDeterminantPositive : 0 < Matrix.det root
  squareRootEquation : root * root = plusInverse * minusMetric

def forgetBranch (data : SquareRootPointData) : PointwiseBimetricRootData where
  plusMetric := data.plusMetric
  plusInverse := data.plusInverse
  minusMetric := data.minusMetric
  minusInverse := data.minusInverse
  root := data.root
  rootInverse := data.rootInverse
  plusInverseWitness := data.plusInverseWitness
  minusInverseWitness := data.minusInverseWitness
  rootInverseWitness := data.rootInverseWitness
  plusMetricSymmetric := data.plusMetricSymmetric
  minusMetricSymmetric := data.minusMetricSymmetric
  rootDeterminantPositive := data.rootDeterminantPositive
  squareRootEquation := data.squareRootEquation

/-- Concrete simultaneous frame action on both metric sectors and the
relative square-root data. -/
def diagonalFrameAction
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (data : PointwiseBimetricRootData) : PointwiseBimetricRootData where
  plusMetric := metricCongruence frame data.plusMetric
  plusInverse := inverseMetricCongruence inverse data.plusInverse
  minusMetric := metricCongruence frame data.minusMetric
  minusInverse := inverseMetricCongruence inverse data.minusInverse
  root := rootSimilarity frame inverse data.root
  rootInverse := rootSimilarity frame inverse data.rootInverse
  plusInverseWitness := inverseMetricCongruence_is_inverse frame inverse
    data.plusMetric data.plusInverse hFrame data.plusInverseWitness
  minusInverseWitness := inverseMetricCongruence_is_inverse frame inverse
    data.minusMetric data.minusInverse hFrame data.minusInverseWitness
  rootInverseWitness := by
    constructor
    · rw [rootSimilarity, rootSimilarity,
        conjugate_mul frame inverse data.rootInverse data.root hFrame,
        data.rootInverseWitness.inverse_mul]
      simp [conjugate, hFrame.inverse_mul]
    · rw [rootSimilarity, rootSimilarity,
        conjugate_mul frame inverse data.root data.rootInverse hFrame,
        data.rootInverseWitness.mul_inverse]
      simp [conjugate, hFrame.inverse_mul]
  plusMetricSymmetric := congruence_symmetric frame data.plusMetric
    data.plusMetricSymmetric
  minusMetricSymmetric := congruence_symmetric frame data.minusMetric
    data.minusMetricSymmetric
  rootDeterminantPositive := by
    rw [rootSimilarity,
      conjugate_det frame inverse data.root hFrame]
    exact data.rootDeterminantPositive
  squareRootEquation := by
    calc
      rootSimilarity frame inverse data.root *
          rootSimilarity frame inverse data.root =
        conjugate inverse frame (data.root * data.root) :=
          conjugate_square frame inverse data.root hFrame
      _ = conjugate inverse frame
          (data.plusInverse * data.minusMetric) := by
            rw [data.squareRootEquation]
      _ = inverseMetricCongruence inverse data.plusInverse *
          metricCongruence frame data.minusMetric :=
            (transformedRelativeTarget frame inverse data.plusInverse
              data.minusMetric hFrame).symm

/-- The interaction scalar carried by the relative root. -/
def pointwiseInteractionScalar
    (coefficients : PotentialCoefficients)
    (data : PointwiseBimetricRootData) : ℝ :=
  matrixSpectralPotential coefficients data.root

/-- Coordinate-density representative of the committed candidate. -/
def pointwiseInteractionDensity
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (data : PointwiseBimetricRootData) : ℝ :=
  -interactionScale * Real.sqrt |Matrix.det data.plusMetric| *
    pointwiseInteractionScalar coefficients data

theorem pointwiseInteractionDensity_forgetBranch
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (data : SquareRootPointData) :
    pointwiseInteractionDensity interactionScale coefficients
        (forgetBranch data) =
      matrixCommonInteractionDensity interactionScale coefficients data := by
  rfl

/-- The shared/diagonal frame action preserves the full interaction scalar. -/
theorem pointwiseInteractionScalar_diagonal_invariant
    (coefficients : PotentialCoefficients)
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (data : PointwiseBimetricRootData) :
    pointwiseInteractionScalar coefficients
        (diagonalFrameAction frame inverse hFrame data) =
      pointwiseInteractionScalar coefficients data := by
  exact matrixSpectralPotential_conjugate coefficients frame inverse
    data.root hFrame

theorem det_metricCongruence (frame metric : Matrix4) :
    Matrix.det (metricCongruence frame metric) =
      (Matrix.det frame) ^ 2 * Matrix.det metric := by
  simp [metricCongruence, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem metricVolume_diagonal_invariant
    (frame metric : Matrix4)
    (hVolume : |Matrix.det frame| = 1) :
    Real.sqrt |Matrix.det (metricCongruence frame metric)| =
      Real.sqrt |Matrix.det metric| := by
  rw [det_metricCongruence, abs_mul, abs_pow, hVolume]
  norm_num

/-- A coordinate density is numerically invariant under a shared
volume-preserving frame.  General frames require the coordinate Jacobian. -/
theorem pointwiseInteractionDensity_diagonal_invariant
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (hVolume : |Matrix.det frame| = 1)
    (data : PointwiseBimetricRootData) :
    pointwiseInteractionDensity interactionScale coefficients
        (diagonalFrameAction frame inverse hFrame data) =
      pointwiseInteractionDensity interactionScale coefficients data := by
  unfold pointwiseInteractionDensity
  change -interactionScale *
      Real.sqrt |Matrix.det (metricCongruence frame data.plusMetric)| *
        pointwiseInteractionScalar coefficients
          (diagonalFrameAction frame inverse hFrame data) =
    -interactionScale * Real.sqrt |Matrix.det data.plusMetric| *
      pointwiseInteractionScalar coefficients data
  rw [metricVolume_diagonal_invariant frame data.plusMetric hVolume,
    pointwiseInteractionScalar_diagonal_invariant coefficients frame inverse
      hFrame data]

/-- An independent left/right frame action is not a similarity unless the
two frames coincide in the diagonal way. -/
def independentRootAction
    (leftInverse rightFrame root : Matrix4) : Matrix4 :=
  leftInverse * root * rightFrame

def traceOnlyCoefficients : PotentialCoefficients where
  beta0 := 0
  beta1 := 1
  beta2 := 0
  beta3 := 0
  beta4 := 0

def doubledFrame : Matrix4 := (2 : ℝ) • (1 : Matrix4)

/-- Concrete failure of interaction invariance for independent frames. -/
theorem independent_frame_interaction_counterexample :
    matrixSpectralPotential traceOnlyCoefficients
        (independentRootAction 1 doubledFrame 1) ≠
      matrixSpectralPotential traceOnlyCoefficients (1 : Matrix4) := by
  simp [matrixSpectralPotential, traceOnlyCoefficients,
    matrixElementary0, matrixElementary1, independentRootAction,
    doubledFrame, Matrix.trace_smul, Matrix.trace_one]

/-- Differentiable family of genuinely invertible frames through the
identity.  The inverse derivative is derived below from the inverse law. -/
structure OneParameterDiagonalFrame where
  frame : ℝ → Matrix4
  inverse : ℝ → Matrix4
  generator : Matrix4
  inverseWitness : ∀ t, FrameInverseWitness (frame t) (inverse t)
  frame_zero : frame 0 = 1
  inverse_zero : inverse 0 = 1
  frame_hasDerivAt : HasDerivAt frame generator 0
  inverseDerivative : Matrix4
  inverse_hasDerivAt : HasDerivAt inverse inverseDerivative 0

theorem inverseCurve_hasDerivAt
    (curve : OneParameterDiagonalFrame) :
    HasDerivAt curve.inverse (-curve.generator) 0 := by
  have hProduct := curve.frame_hasDerivAt.mul curve.inverse_hasDerivAt
  have hConstant : HasDerivAt (fun _ : ℝ => (1 : Matrix4)) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) (c := (1 : Matrix4))
  have hConstantProduct :
      HasDerivAt (fun t => curve.frame t * curve.inverse t) 0 0 :=
    hConstant.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t =>
        (curve.inverseWitness t).mul_inverse)
  have hZero := hProduct.unique hConstantProduct
  have hAdd : curve.generator + curve.inverseDerivative = 0 := by
    simpa [curve.frame_zero, curve.inverse_zero] using hZero
  exact curve.inverse_hasDerivAt.congr_deriv
    (eq_neg_of_add_eq_zero_right hAdd)

def conjugationCurve
    (curve : OneParameterDiagonalFrame) (root : Matrix4) (t : ℝ) :
    Matrix4 :=
  rootSimilarity (curve.frame t) (curve.inverse t) root

def commutatorGenerator (generator root : Matrix4) : Matrix4 :=
  root * generator - generator * root

/-- Actual tangent of a differentiable similarity orbit. -/
theorem conjugationCurve_hasDerivAt
    (curve : OneParameterDiagonalFrame) (root : Matrix4) :
    HasDerivAt (conjugationCurve curve root)
      (commutatorGenerator curve.generator root) 0 := by
  have hLeft := (inverseCurve_hasDerivAt curve).mul_const root
  have hProduct := hLeft.mul curve.frame_hasDerivAt
  refine (show HasDerivAt
      (fun t => (curve.inverse t * root) * curve.frame t)
      ((-curve.generator * root) * curve.frame 0 +
        (curve.inverse 0 * root) * curve.generator) 0 from hProduct).congr_deriv ?_
  simp [curve.frame_zero, curve.inverse_zero, commutatorGenerator]
  noncomm_ring

theorem conjugationCurve_zero
    (curve : OneParameterDiagonalFrame) (root : Matrix4) :
    conjugationCurve curve root 0 = root := by
  simp [conjugationCurve, rootSimilarity, conjugate,
    curve.frame_zero, curve.inverse_zero]

theorem interaction_along_conjugationCurve
    (coefficients : PotentialCoefficients)
    (curve : OneParameterDiagonalFrame) (root : Matrix4) (t : ℝ) :
    matrixSpectralPotential coefficients (conjugationCurve curve root t) =
      matrixSpectralPotential coefficients root := by
  exact matrixSpectralPotential_conjugate coefficients
    (curve.frame t) (curve.inverse t) root (curve.inverseWitness t)

/-- Pointwise Noether pairing: the actual derivative covector of the
interaction annihilates every commutator tangent generated by a shared frame
curve. -/
theorem matrixInteraction_noether_pairing
    (coefficients : PotentialCoefficients)
    (curve : OneParameterDiagonalFrame) (root : Matrix4)
    (gradient : Matrix4 →L[ℝ] ℝ)
    (hGradient : HasFDerivAt
      (matrixSpectralPotential coefficients) gradient root) :
    gradient (commutatorGenerator curve.generator root) = 0 := by
  have hComposite := hGradient.comp_hasDerivAt_of_eq 0
    (conjugationCurve_hasDerivAt curve root)
    (conjugationCurve_zero curve root).symm
  have hConstant :
      HasDerivAt (fun _ : ℝ => matrixSpectralPotential coefficients root)
        0 0 :=
    hasDerivAt_const (x := (0 : ℝ))
      (c := matrixSpectralPotential coefficients root)
  have hInvariant : HasDerivAt
      (fun t => matrixSpectralPotential coefficients
        (conjugationCurve curve root t)) 0 0 :=
    hConstant.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t =>
        interaction_along_conjugationCurve coefficients curve root t)
  exact hComposite.unique hInvariant

/- The action above is finite-dimensional and pointwise.  In particular,
`matrixInteraction_noether_pairing` does not assert a covariant divergence,
the differential Bianchi identity, or closure of Hamiltonian constraints. -/

end

end P0EFTJanusMatrixDiagonalGaugeNoether
end JanusFormal
