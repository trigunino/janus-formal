import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiRelativeRootBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-!
# Local Candidate-A interaction variation at the Minkowski diagonal

This gate differentiates the actual finite-dimensional Candidate-A density
`-m² sqrt |det gPlus| V(sqrt (gPlus⁻¹ gMinus))` along an affine pair of
symmetric metric variations.  The determinant measure, the unconditional
local Minkowski root branch, and the full spectral potential are composed by
the Frechet chain and product rules; no interaction covector or root tangent
is assumed.

The result is local to the four-dimensional Minkowski diagonal.  It does not
assert a global Lorentzian root branch, a spacetime integral, or field
stationarity.
-/

namespace JanusFormal
namespace P0EFTJanusMinkowskiInteractionDensityVariation4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusFlatFieldBranch4D
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMetricInverseRelativeRootFrechet
open P0EFTJanusMinkowskiRelativeRootBranch4D

abbrev Matrix4 := P0EFTJanusMinkowskiRelativeRootBranch4D.Matrix4
abbrev MetricPair := P0EFTJanusMinkowskiRelativeRootBranch4D.MetricPair

attribute [local instance]
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4AddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4TopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4Module
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairTopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairModule

/-- Scalar-valued Frechet derivative with exactly the pair topology used by
the local Minkowski root theorem. -/
abbrev PairScalarHasFDerivAt
    (function : MetricPair → Real)
    (derivative : MetricPair →L[Real] Real)
    (point : MetricPair) : Prop :=
  @HasFDerivAt Real _ MetricPair
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toAddCommGroup
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace.toModule
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Real Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function derivative point

/-- Vector-valued one-parameter derivative in the same pair topology. -/
abbrev PairHasDerivAt
    (function : Real → MetricPair) (derivative : MetricPair)
    (point : Real) : Prop :=
  @HasDerivAt Real _ MetricPair
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toAddCommGroup
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace.toModule
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    _
    function derivative point

/-- Two independent symmetric covariant metric directions. -/
structure SymmetricMetricPairVariation4 where
  plus : Matrix4
  minus : Matrix4
  plus_symmetric : plus.transpose = plus
  minus_symmetric : minus.transpose = minus

/-- The pair tangent underlying the two symmetric directions. -/
def SymmetricMetricPairVariation4.asPair
    (variation : SymmetricMetricPairVariation4) : MetricPair :=
  (variation.plus, variation.minus)

/-- Genuine affine two-metric curve based at the Minkowski diagonal. -/
def minkowskiMetricPairCurve
    (variation : SymmetricMetricPairVariation4) (t : Real) : MetricPair :=
  letI : AddCommGroup MetricPair :=
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toAddCommGroup
  letI : Module Real MetricPair :=
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace.toModule
  t • variation.asPair + minkowskiMetricPair

@[simp] theorem minkowskiMetricPairCurve_zero
    (variation : SymmetricMetricPairVariation4) :
    minkowskiMetricPairCurve variation 0 = minkowskiMetricPair := by
  simp [minkowskiMetricPairCurve]

theorem minkowskiMetricPairCurve_hasDerivAt
    (variation : SymmetricMetricPairVariation4) :
    PairHasDerivAt (minkowskiMetricPairCurve variation) variation.asPair 0 := by
  unfold PairHasDerivAt minkowskiMetricPairCurve
  simpa only [Function.id_def, one_smul] using
    (HasDerivAt.add_const minkowskiMetricPair
      ((hasDerivAt_id (x := (0 : Real))).smul_const variation.asPair))

/-- The actual plus-sector determinant volume. -/
def minkowskiPlusVolume (input : MetricPair) : Real :=
  Real.sqrt |Matrix.det input.1|

/-- Determinant differential pulled back through the plus projection. -/
def minkowskiPlusDeterminantDerivative : MetricPair →L[Real] Real :=
  (determinantDerivative minkowskiMetric4).comp
    (ContinuousLinearMap.fst Real Matrix4 Matrix4)

/-- Explicit differential of `sqrt |det gPlus|` at the Minkowski metric. -/
def minkowskiPlusVolumeDerivative : MetricPair →L[Real] Real :=
  (1 / (2 * Real.sqrt |Matrix.det minkowskiMetric4|)) •
    ((SignType.sign (Matrix.det minkowskiMetric4) : Real) •
      minkowskiPlusDeterminantDerivative)

theorem minkowskiPlusVolume_hasFDerivAt :
    PairScalarHasFDerivAt minkowskiPlusVolume minkowskiPlusVolumeDerivative
      minkowskiMetricPair := by
  have hProjection : HasFDerivAt (fun input : MetricPair => input.1)
      (ContinuousLinearMap.fst Real Matrix4 Matrix4) minkowskiMetricPair :=
    (ContinuousLinearMap.fst Real Matrix4 Matrix4).hasFDerivAt
  have hDeterminant := determinant_hasFDerivAt minkowskiMetric4
  unfold FrobeniusHasFDerivAt at hDeterminant
  have hDeterminantPair := hDeterminant.comp minkowskiMetricPair hProjection
  have hNonzero := minkowskiLorentzMetricPoint4.det_ne_zero
  have hAbsolute := hDeterminantPair.abs hNonzero
  have hSquareRoot := hAbsolute.sqrt (abs_ne_zero.mpr hNonzero)
  exact hSquareRoot

@[simp] theorem minkowskiPlusVolumeDerivative_apply
    (variation : SymmetricMetricPairVariation4) :
    minkowskiPlusVolumeDerivative variation.asPair =
      (1 / (2 * Real.sqrt |Matrix.det minkowskiMetric4|)) *
        ((SignType.sign (Matrix.det minkowskiMetric4) : Real) *
          determinantDerivative minkowskiMetric4 variation.plus) := by
  simp only [minkowskiPlusVolumeDerivative, smul_apply,
    smul_eq_mul]
  congr 2

/-- Frechet differential of the unconditional local root selection. -/
def minkowskiRootDerivative : MetricPair →L[Real] Matrix4 :=
  (twiceEquiv.symm : Matrix4 →L[Real] Matrix4).comp
    (frobeniusRelativeMetricDerivative minkowskiMetricPair)

theorem minkowskiRoot_hasFDerivAt :
    HasFDerivAt minkowskiRelativeRootBranch minkowskiRootDerivative
      minkowskiMetricPair := by
  exact minkowskiRelativeRootBranch_hasFDerivAt

@[simp] theorem minkowskiRootDerivative_apply
    (variation : SymmetricMetricPairVariation4) :
    minkowskiRootDerivative variation.asPair =
      (1 / 2 : Real) •
        frobeniusRelativeMetricDerivative minkowskiMetricPair variation.asPair := by
  change twiceEquiv.symm
      (frobeniusRelativeMetricDerivative minkowskiMetricPair variation.asPair) =
    (1 / 2 : Real) •
      frobeniusRelativeMetricDerivative minkowskiMetricPair variation.asPair
  exact twiceEquiv_symm_apply _

/-- The full matrix spectral potential evaluated on the actual local root. -/
def minkowskiRootPotential
    (coefficients : PotentialCoefficients) (input : MetricPair) : Real :=
  matrixSpectralPotential coefficients (minkowskiRelativeRootBranch input)

/-- Potential covector composed with the actual root derivative. -/
def minkowskiRootPotentialDerivative
    (coefficients : PotentialCoefficients) : MetricPair →L[Real] Real :=
  (matrixSpectralPotentialDerivative coefficients (1 : Matrix4)).comp
    minkowskiRootDerivative

theorem minkowskiRootPotential_hasFDerivAt
    (coefficients : PotentialCoefficients) :
    PairScalarHasFDerivAt (minkowskiRootPotential coefficients)
      (minkowskiRootPotentialDerivative coefficients) minkowskiMetricPair := by
  have hPotential := matrixSpectralPotential_hasFDerivAt
    coefficients (minkowskiRelativeRootBranch minkowskiMetricPair)
  unfold FrobeniusHasFDerivAt at hPotential
  have hComposite := hPotential.comp minkowskiMetricPair
    minkowskiRoot_hasFDerivAt
  rw [minkowskiRelativeRootBranch_at_base] at hComposite
  change PairScalarHasFDerivAt
    (matrixSpectralPotential coefficients ∘ minkowskiRelativeRootBranch)
    ((matrixSpectralPotentialDerivative coefficients (1 : Matrix4)).comp
      minkowskiRootDerivative) minkowskiMetricPair at hComposite
  unfold minkowskiRootPotential minkowskiRootPotentialDerivative
  exact hComposite

@[simp] theorem minkowskiRootPotentialDerivative_apply
    (coefficients : PotentialCoefficients)
    (variation : SymmetricMetricPairVariation4) :
    minkowskiRootPotentialDerivative coefficients variation.asPair =
      matrixSpectralPotentialDerivative coefficients (1 : Matrix4)
        ((1 / 2 : Real) •
          frobeniusRelativeMetricDerivative minkowskiMetricPair
            variation.asPair) := by
  exact congrArg (matrixSpectralPotentialDerivative coefficients (1 : Matrix4))
    (minkowskiRootDerivative_apply variation)

/-- Candidate A with the plus measure and relative root both induced by the
same independent metric pair. -/
def minkowskiCandidateAInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) : Real :=
  -interactionScale * minkowskiPlusVolume input *
    minkowskiRootPotential coefficients input

/-- Complete product-and-chain differential at the Minkowski diagonal. -/
def minkowskiCandidateAInteractionDensityDerivative
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    MetricPair →L[Real] Real :=
  (-interactionScale * minkowskiPlusVolume minkowskiMetricPair) •
      minkowskiRootPotentialDerivative coefficients +
    minkowskiRootPotential coefficients minkowskiMetricPair •
      ((-interactionScale) • minkowskiPlusVolumeDerivative)

theorem minkowskiCandidateAInteractionDensity_hasFDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    PairScalarHasFDerivAt
      (minkowskiCandidateAInteractionDensity interactionScale coefficients)
      (minkowskiCandidateAInteractionDensityDerivative interactionScale
        coefficients) minkowskiMetricPair := by
  exact (minkowskiPlusVolume_hasFDerivAt.const_mul (-interactionScale)).mul
    (minkowskiRootPotential_hasFDerivAt coefficients)

@[simp] theorem minkowskiCandidateAInteractionDensityDerivative_apply
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : SymmetricMetricPairVariation4) :
    minkowskiCandidateAInteractionDensityDerivative interactionScale
        coefficients variation.asPair =
      (-interactionScale * minkowskiPlusVolume minkowskiMetricPair) *
          matrixSpectralPotentialDerivative coefficients (1 : Matrix4)
            ((1 / 2 : Real) •
              frobeniusRelativeMetricDerivative minkowskiMetricPair
                variation.asPair) +
        minkowskiRootPotential coefficients minkowskiMetricPair *
          (-interactionScale *
            minkowskiPlusVolumeDerivative variation.asPair) := by
  simp [minkowskiCandidateAInteractionDensityDerivative]

/-- Fully expanded two-metric chain formula at the diagonal. -/
theorem minkowskiCandidateAInteractionDensityDerivative_apply_explicit
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : SymmetricMetricPairVariation4) :
    minkowskiCandidateAInteractionDensityDerivative interactionScale
        coefficients variation.asPair =
      (-interactionScale * Real.sqrt |Matrix.det minkowskiMetric4|) *
          matrixSpectralPotentialDerivative coefficients (1 : Matrix4)
            ((1 / 2 : Real) •
              (-(minkowskiMetric4⁻¹ * variation.plus *
                    minkowskiMetric4⁻¹) * minkowskiMetric4 +
                minkowskiMetric4⁻¹ * variation.minus)) +
        matrixSpectralPotential coefficients (1 : Matrix4) *
          (-interactionScale *
            ((1 / (2 * Real.sqrt |Matrix.det minkowskiMetric4|)) *
              ((SignType.sign (Matrix.det minkowskiMetric4) : Real) *
                determinantDerivative minkowskiMetric4 variation.plus))) := by
  rw [minkowskiCandidateAInteractionDensityDerivative_apply,
    minkowskiPlusVolumeDerivative_apply]
  rw [show minkowskiRootPotential coefficients minkowskiMetricPair =
      matrixSpectralPotential coefficients (1 : Matrix4) by
    simp only [minkowskiRootPotential, minkowskiRelativeRootBranch_at_base]]
  simp only [minkowskiPlusVolume, minkowskiMetricPair,
    frobeniusRelativeMetricDerivative_apply,
    SymmetricMetricPairVariation4.asPair]

/-- Directional chain formula along the affine pair of symmetric metric
variations, with every tangent forced by the displayed curve. -/
theorem minkowskiCandidateAInteractionDensity_curve_hasDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : SymmetricMetricPairVariation4) :
    HasDerivAt
      (fun t => minkowskiCandidateAInteractionDensity interactionScale
        coefficients (minkowskiMetricPairCurve variation t))
      (minkowskiCandidateAInteractionDensityDerivative interactionScale
        coefficients variation.asPair) 0 := by
  have hDensity :=
    minkowskiCandidateAInteractionDensity_hasFDerivAt interactionScale
      coefficients
  unfold PairScalarHasFDerivAt at hDensity
  exact hDensity.comp_hasDerivAt_of_eq 0
    (minkowskiMetricPairCurve_hasDerivAt variation)
    (minkowskiMetricPairCurve_zero variation).symm

/-- Along the same affine curve, the selected matrix is genuinely a relative
square root for all sufficiently small parameters. -/
theorem eventually_minkowskiMetricPairCurve_root_square
    (variation : SymmetricMetricPairVariation4) :
    ∀ᶠ t in 𝓝 (0 : Real),
      matrixSquare
          (minkowskiRelativeRootBranch
            (minkowskiMetricPairCurve variation t)) =
        relativeMetricTarget (minkowskiMetricPairCurve variation t) := by
  have hContinuous :=
    (minkowskiMetricPairCurve_hasDerivAt variation).continuousAt
  change Tendsto (minkowskiMetricPairCurve variation) (𝓝 (0 : Real))
    (𝓝 (minkowskiMetricPairCurve variation 0)) at hContinuous
  rw [minkowskiMetricPairCurve_zero] at hContinuous
  exact hContinuous.eventually eventually_minkowskiRelativeRootBranch_square

end

end P0EFTJanusMinkowskiInteractionDensityVariation4D
end JanusFormal
