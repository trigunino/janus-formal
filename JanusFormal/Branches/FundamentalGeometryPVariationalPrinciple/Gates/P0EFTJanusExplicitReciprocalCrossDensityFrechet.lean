import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensities
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge

/-!
Actual Frechet variation of the explicit reciprocal cross-density candidate on
the real diagonalizable four-eigenvalue branch.  Every derivative below is
proved from the displayed coordinate polynomial.  No matrix square-root,
metric variation, spacetime covariance, or bimetric constraint claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitReciprocalCrossDensityFrechet

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusPTFlatBimetricVariationalBridge

/-- Coordinate projection on the ordered square-root spectrum. -/
def spectrumCoordinate (i : Fin 4) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

/-- One partial derivative after omitting a selected eigenvalue. -/
def complementaryGradientValue
    (coefficients : PotentialCoefficients) (x y z : ℝ) : ℝ :=
  coefficients.beta1 + coefficients.beta2 * (x + y + z) +
    coefficients.beta3 * (x * y + x * z + y * z) +
    coefficients.beta4 * x * y * z

/-- Mixed second derivative after omitting the differentiated eigenvalue pair. -/
def mixedSecondCoefficient
    (coefficients : PotentialCoefficients) (x y : ℝ) : ℝ :=
  coefficients.beta2 + coefficients.beta3 * (x + y) +
    coefficients.beta4 * x * y

def spectralPartial0
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) : ℝ :=
  complementaryGradientValue coefficients (spectrum 1) (spectrum 2) (spectrum 3)

def spectralPartial1
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) : ℝ :=
  complementaryGradientValue coefficients (spectrum 0) (spectrum 2) (spectrum 3)

def spectralPartial2
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) : ℝ :=
  complementaryGradientValue coefficients (spectrum 0) (spectrum 1) (spectrum 3)

def spectralPartial3
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) : ℝ :=
  complementaryGradientValue coefficients (spectrum 0) (spectrum 1) (spectrum 2)

/-- Displayed coordinate Frechet gradient of the spectral potential. -/
def spectralGradient
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  spectralPartial0 coefficients spectrum • spectrumCoordinate 0 +
    spectralPartial1 coefficients spectrum • spectrumCoordinate 1 +
    spectralPartial2 coefficients spectrum • spectrumCoordinate 2 +
    spectralPartial3 coefficients spectrum • spectrumCoordinate 3

@[simp]
theorem spectralGradient_apply
    (coefficients : PotentialCoefficients)
    (spectrum direction : SquareRootSpectrum) :
    spectralGradient coefficients spectrum direction =
      spectralPartial0 coefficients spectrum * direction 0 +
        spectralPartial1 coefficients spectrum * direction 1 +
        spectralPartial2 coefficients spectrum * direction 2 +
        spectralPartial3 coefficients spectrum * direction 3 := by
  simp [spectralGradient, spectrumCoordinate, smul_eq_mul]

/-- The displayed coordinate functional is the genuine Frechet derivative. -/
theorem spectralPotential_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralPotential coefficients)
      (spectralGradient coefficients spectrum) spectrum := by
  let p0 : SquareRootSpectrum →L[ℝ] ℝ := spectrumCoordinate 0
  let p1 : SquareRootSpectrum →L[ℝ] ℝ := spectrumCoordinate 1
  let p2 : SquareRootSpectrum →L[ℝ] ℝ := spectrumCoordinate 2
  let p3 : SquareRootSpectrum →L[ℝ] ℝ := spectrumCoordinate 3
  have h0 : HasFDerivAt (fun x : SquareRootSpectrum => x 0) p0 spectrum := by
    exact p0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : SquareRootSpectrum => x 1) p1 spectrum := by
    exact p1.hasFDerivAt
  have h2 : HasFDerivAt (fun x : SquareRootSpectrum => x 2) p2 spectrum := by
    exact p2.hasFDerivAt
  have h3 : HasFDerivAt (fun x : SquareRootSpectrum => x 3) p3 spectrum := by
    exact p3.hasFDerivAt
  have hLinear := (((h0.add h1).add h2).add h3).const_mul coefficients.beta1
  have hQuadratic :=
    ((((((h0.mul h1).add (h0.mul h2)).add (h0.mul h3)).add
      (h1.mul h2)).add (h1.mul h3)).add (h2.mul h3)).const_mul
        coefficients.beta2
  have hCubic :=
    ((((h0.mul h1).mul h2).add ((h0.mul h1).mul h3)).add
      ((h0.mul h2).mul h3)).add ((h1.mul h2).mul h3) |>.const_mul
        coefficients.beta3
  have hQuartic :=
    (((h0.mul h1).mul h2).mul h3).const_mul coefficients.beta4
  have hCandidate :=
    (((hLinear.add hQuadratic).add hCubic).add hQuartic).const_add
      coefficients.beta0
  refine (hCandidate.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · ext direction
    simp [spectralGradient, spectralPartial0, spectralPartial1,
      spectralPartial2, spectralPartial3, complementaryGradientValue,
      spectrumCoordinate, p0, p1, p2, p3, smul_eq_mul]
    ring
  · intro x
    simp [spectralPotential, elementary0, elementary1, elementary2,
      elementary3, elementary4]
    ring

theorem spectralPotential_fderiv
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    fderiv ℝ (spectralPotential coefficients) spectrum =
      spectralGradient coefficients spectrum :=
  (spectralPotential_hasFDerivAt coefficients spectrum).fderiv

/-- Derivative of the common, unsplit interaction density. -/
def commonInteractionGradient
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) : SquareRootSpectrum →L[ℝ] ℝ :=
  (-interactionScale) • spectralGradient coefficients spectrum

theorem commonInteractionPotential_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    HasFDerivAt (commonInteractionPotential interactionScale coefficients)
      (commonInteractionGradient interactionScale coefficients spectrum)
      spectrum := by
  have hDerivative :=
    (spectralPotential_hasFDerivAt coefficients spectrum).const_mul
      (-interactionScale)
  refine (hDerivative.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · ext direction
    simp [commonInteractionGradient]
  · intro x
    simp [commonInteractionPotential]

theorem commonInteractionPotential_fderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    fderiv ℝ (commonInteractionPotential interactionScale coefficients) spectrum =
      commonInteractionGradient interactionScale coefficients spectrum :=
  (commonInteractionPotential_hasFDerivAt interactionScale coefficients spectrum).fderiv

/-- Generic derivative of one complementary cubic partial. -/
theorem complementaryGradientValue_hasFDerivAt
    (coefficients : PotentialCoefficients)
    (p q r : SquareRootSpectrum →L[ℝ] ℝ)
    (spectrum : SquareRootSpectrum) :
    HasFDerivAt
      (fun x => complementaryGradientValue coefficients (p x) (q x) (r x))
      (mixedSecondCoefficient coefficients (q spectrum) (r spectrum) • p +
        mixedSecondCoefficient coefficients (p spectrum) (r spectrum) • q +
        mixedSecondCoefficient coefficients (p spectrum) (q spectrum) • r)
      spectrum := by
  have hp : HasFDerivAt (fun x : SquareRootSpectrum => p x) p spectrum :=
    p.hasFDerivAt
  have hq : HasFDerivAt (fun x : SquareRootSpectrum => q x) q spectrum :=
    q.hasFDerivAt
  have hr : HasFDerivAt (fun x : SquareRootSpectrum => r x) r spectrum :=
    r.hasFDerivAt
  have hLinear := ((hp.add hq).add hr).const_mul coefficients.beta2
  have hQuadratic :=
    (((hp.mul hq).add (hp.mul hr)).add (hq.mul hr)).const_mul
      coefficients.beta3
  have hCubic := ((hp.mul hq).mul hr).const_mul coefficients.beta4
  have hCandidate := ((hLinear.add hQuadratic).add hCubic).const_add
    coefficients.beta1
  refine (hCandidate.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · ext direction
    simp [mixedSecondCoefficient, smul_eq_mul]
    ring
  · intro x
    simp [complementaryGradientValue]
    ring

def spectralHessianRow0
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) •
      spectrumCoordinate 1 +
    mixedSecondCoefficient coefficients (spectrum 1) (spectrum 3) •
      spectrumCoordinate 2 +
    mixedSecondCoefficient coefficients (spectrum 1) (spectrum 2) •
      spectrumCoordinate 3

def spectralHessianRow1
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) •
      spectrumCoordinate 0 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 3) •
      spectrumCoordinate 2 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 2) •
      spectrumCoordinate 3

def spectralHessianRow2
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  mixedSecondCoefficient coefficients (spectrum 1) (spectrum 3) •
      spectrumCoordinate 0 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 3) •
      spectrumCoordinate 1 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 1) •
      spectrumCoordinate 3

def spectralHessianRow3
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] ℝ :=
  mixedSecondCoefficient coefficients (spectrum 1) (spectrum 2) •
      spectrumCoordinate 0 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 2) •
      spectrumCoordinate 1 +
    mixedSecondCoefficient coefficients (spectrum 0) (spectrum 1) •
      spectrumCoordinate 2

/-- Displayed Jacobian of the spectral gradient, equivalently its Hessian. -/
def spectralHessian
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] SquareRootSpectrum →L[ℝ] ℝ :=
  (spectralHessianRow0 coefficients spectrum).smulRight (spectrumCoordinate 0) +
    (spectralHessianRow1 coefficients spectrum).smulRight (spectrumCoordinate 1) +
    (spectralHessianRow2 coefficients spectrum).smulRight (spectrumCoordinate 2) +
    (spectralHessianRow3 coefficients spectrum).smulRight (spectrumCoordinate 3)

@[simp]
theorem spectralHessian_apply
    (coefficients : PotentialCoefficients)
    (spectrum first second : SquareRootSpectrum) :
    spectralHessian coefficients spectrum first second =
      spectralHessianRow0 coefficients spectrum first * second 0 +
        spectralHessianRow1 coefficients spectrum first * second 1 +
        spectralHessianRow2 coefficients spectrum first * second 2 +
        spectralHessianRow3 coefficients spectrum first * second 3 := by
  simp [spectralHessian, spectrumCoordinate, smul_eq_mul]

theorem spectralPartial0_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralPartial0 coefficients)
      (spectralHessianRow0 coefficients spectrum) spectrum := by
  change HasFDerivAt
    (fun x : SquareRootSpectrum =>
      complementaryGradientValue coefficients (x 1) (x 2) (x 3))
    (spectralHessianRow0 coefficients spectrum) spectrum
  simpa [spectralPartial0, spectralHessianRow0, spectrumCoordinate] using
    complementaryGradientValue_hasFDerivAt coefficients
      (spectrumCoordinate 1) (spectrumCoordinate 2) (spectrumCoordinate 3)
      spectrum

theorem spectralPartial1_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralPartial1 coefficients)
      (spectralHessianRow1 coefficients spectrum) spectrum := by
  change HasFDerivAt
    (fun x : SquareRootSpectrum =>
      complementaryGradientValue coefficients (x 0) (x 2) (x 3))
    (spectralHessianRow1 coefficients spectrum) spectrum
  simpa [spectralPartial1, spectralHessianRow1, spectrumCoordinate] using
    complementaryGradientValue_hasFDerivAt coefficients
      (spectrumCoordinate 0) (spectrumCoordinate 2) (spectrumCoordinate 3)
      spectrum

theorem spectralPartial2_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralPartial2 coefficients)
      (spectralHessianRow2 coefficients spectrum) spectrum := by
  change HasFDerivAt
    (fun x : SquareRootSpectrum =>
      complementaryGradientValue coefficients (x 0) (x 1) (x 3))
    (spectralHessianRow2 coefficients spectrum) spectrum
  simpa [spectralPartial2, spectralHessianRow2, spectrumCoordinate] using
    complementaryGradientValue_hasFDerivAt coefficients
      (spectrumCoordinate 0) (spectrumCoordinate 1) (spectrumCoordinate 3)
      spectrum

theorem spectralPartial3_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralPartial3 coefficients)
      (spectralHessianRow3 coefficients spectrum) spectrum := by
  change HasFDerivAt
    (fun x : SquareRootSpectrum =>
      complementaryGradientValue coefficients (x 0) (x 1) (x 2))
    (spectralHessianRow3 coefficients spectrum) spectrum
  simpa [spectralPartial3, spectralHessianRow3, spectrumCoordinate] using
    complementaryGradientValue_hasFDerivAt coefficients
      (spectrumCoordinate 0) (spectrumCoordinate 1) (spectrumCoordinate 2)
      spectrum

/-- The displayed spectral Hessian is the genuine derivative of the gradient. -/
theorem spectralGradient_hasFDerivAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HasFDerivAt (spectralGradient coefficients)
      (spectralHessian coefficients spectrum) spectrum := by
  have h0 := (spectralPartial0_hasFDerivAt coefficients spectrum).smul_const
    (spectrumCoordinate 0)
  have h1 := (spectralPartial1_hasFDerivAt coefficients spectrum).smul_const
    (spectrumCoordinate 1)
  have h2 := (spectralPartial2_hasFDerivAt coefficients spectrum).smul_const
    (spectrumCoordinate 2)
  have h3 := (spectralPartial3_hasFDerivAt coefficients spectrum).smul_const
    (spectrumCoordinate 3)
  refine (((h0.add h1).add h2).add h3).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro x
  rfl

theorem spectralGradient_fderiv
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    fderiv ℝ (spectralGradient coefficients) spectrum =
      spectralHessian coefficients spectrum :=
  (spectralGradient_hasFDerivAt coefficients spectrum).fderiv

/-- Exact second Frechet derivative of the spectral potential. -/
theorem spectralPotential_second_fderiv
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    fderiv ℝ (fun x => fderiv ℝ (spectralPotential coefficients) x)
        spectrum =
      spectralHessian coefficients spectrum := by
  have hGradient :
      (fun x => fderiv ℝ (spectralPotential coefficients) x) =
        spectralGradient coefficients := by
    funext x
    exact spectralPotential_fderiv coefficients x
  rw [hGradient]
  exact spectralGradient_fderiv coefficients spectrum

/-- Coordinate Hessian symmetry, proved directly from the displayed rows. -/
theorem spectralHessian_symmetric
    (coefficients : PotentialCoefficients)
    (spectrum first second : SquareRootSpectrum) :
    spectralHessian coefficients spectrum first second =
      spectralHessian coefficients spectrum second first := by
  simp [spectralHessian, spectralHessianRow0, spectralHessianRow1,
    spectralHessianRow2, spectralHessianRow3, mixedSecondCoefficient,
    spectrumCoordinate, smul_eq_mul]
  ring

/-- The actual spectral Euler one-form satisfies the nonlinear Helmholtz test. -/
theorem spectralGradient_helmholtzJacobianAt
    (coefficients : PotentialCoefficients) (spectrum : SquareRootSpectrum) :
    HelmholtzJacobianAt (spectralGradient coefficients) spectrum := by
  intro first second
  rw [spectralGradient_fderiv coefficients spectrum]
  exact spectralHessian_symmetric coefficients spectrum first second

/-- Hessian and Helmholtz statements for the common interaction density. -/
def commonInteractionHessian
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    SquareRootSpectrum →L[ℝ] SquareRootSpectrum →L[ℝ] ℝ :=
  (-interactionScale) • spectralHessian coefficients spectrum

theorem commonInteractionGradient_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    HasFDerivAt (commonInteractionGradient interactionScale coefficients)
      (commonInteractionHessian interactionScale coefficients spectrum)
      spectrum := by
  have hDerivative :=
    (spectralGradient_hasFDerivAt coefficients spectrum).const_smul
      (-interactionScale)
  refine (hDerivative.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · ext first second
    simp [commonInteractionHessian]
  · intro x
    rfl

theorem commonInteractionPotential_second_fderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    fderiv ℝ
        (fun x => fderiv ℝ
          (commonInteractionPotential interactionScale coefficients) x)
        spectrum =
      commonInteractionHessian interactionScale coefficients spectrum := by
  have hGradient :
      (fun x => fderiv ℝ
          (commonInteractionPotential interactionScale coefficients) x) =
        commonInteractionGradient interactionScale coefficients := by
    funext x
    exact commonInteractionPotential_fderiv interactionScale coefficients x
  rw [hGradient]
  exact (commonInteractionGradient_hasFDerivAt
    interactionScale coefficients spectrum).fderiv

theorem commonInteractionGradient_helmholtzJacobianAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    HelmholtzJacobianAt
      (commonInteractionGradient interactionScale coefficients) spectrum := by
  intro first second
  rw [(commonInteractionGradient_hasFDerivAt
    interactionScale coefficients spectrum).fderiv]
  change (-interactionScale) *
      spectralHessian coefficients spectrum first second =
    (-interactionScale) *
      spectralHessian coefficients spectrum second first
  exact congrArg (fun value => (-interactionScale) * value)
    (spectralHessian_symmetric coefficients spectrum first second)

/-- Uniform direction tangent to the proportional spectrum slice. -/
def uniformSpectrumDirection : SquareRootSpectrum :=
  fun _ => 1

/-- Linear embedding of the proportional eigenvalue into the full spectrum. -/
def proportionalSpectrumEmbedding : ℝ →L[ℝ] SquareRootSpectrum :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

@[simp]
theorem proportionalSpectrumEmbedding_apply (c : ℝ) :
    proportionalSpectrumEmbedding c = proportionalSpectrum c := by
  ext i
  rfl

/-- The full Frechet gradient restricts to the genuine proportional derivative. -/
theorem spectralPotential_proportionalSpectrum_hasDerivAt
    (coefficients : PotentialCoefficients) (c : ℝ) :
    HasDerivAt
      (fun t => spectralPotential coefficients (proportionalSpectrum t))
      (spectralGradient coefficients (proportionalSpectrum c)
        uniformSpectrumDirection)
      c := by
  have hEmbedding :
      HasFDerivAt proportionalSpectrum proportionalSpectrumEmbedding c := by
    simpa [proportionalSpectrumEmbedding, proportionalSpectrum] using
      proportionalSpectrumEmbedding.hasFDerivAt (x := c)
  have hComposition :=
    (spectralPotential_hasFDerivAt coefficients (proportionalSpectrum c)).comp
      c hEmbedding
  simpa [Function.comp_def, proportionalSpectrumEmbedding,
    uniformSpectrumDirection] using hComposition.hasDerivAt

/-- On the PT-flat family, the full spectral derivative agrees with the
already audited proportional interaction force. -/
theorem commonInteractionGradient_ptFlat_proportionalSpectrum
    (interactionScale beta1 beta2 c : ℝ) :
    commonInteractionGradient interactionScale
        (ptFlatCoefficients beta1 beta2) (proportionalSpectrum c)
        uniformSpectrumDirection =
      interactionScale * proportionalInteractionForce beta1 beta2 c := by
  have hSpectral :
      HasDerivAt
        (fun t => commonInteractionPotential interactionScale
          (ptFlatCoefficients beta1 beta2) (proportionalSpectrum t))
        (commonInteractionGradient interactionScale
          (ptFlatCoefficients beta1 beta2) (proportionalSpectrum c)
          uniformSpectrumDirection)
        c := by
    have hEmbedding :
        HasFDerivAt proportionalSpectrum proportionalSpectrumEmbedding c := by
      simpa [proportionalSpectrumEmbedding, proportionalSpectrum] using
        proportionalSpectrumEmbedding.hasFDerivAt (x := c)
    have hComposition :=
      (commonInteractionPotential_hasFDerivAt interactionScale
        (ptFlatCoefficients beta1 beta2) (proportionalSpectrum c)).comp
        c hEmbedding
    change HasDerivAt
      (fun t => commonInteractionPotential interactionScale
        (ptFlatCoefficients beta1 beta2) (proportionalSpectrum t))
      ((commonInteractionGradient interactionScale
        (ptFlatCoefficients beta1 beta2) (proportionalSpectrum c))
        (fun _ => 1)) c
    simpa [Function.comp_def, proportionalSpectrumEmbedding,
      uniformSpectrumDirection] using hComposition.hasDerivAt
  have hExisting :
      HasDerivAt
        (fun t => commonInteractionPotential interactionScale
          (ptFlatCoefficients beta1 beta2) (proportionalSpectrum t))
        (interactionScale * proportionalInteractionForce beta1 beta2 c)
        c := by
    refine ((proportionalInteractionEnergy_hasDerivAt beta1 beta2 c).const_mul
      interactionScale).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    intro t
    simp [commonInteractionPotential, proportionalInteractionEnergy,
      spectralPotential_on_proportionalSpectrum]
  exact hSpectral.unique hExisting

end

end P0EFTJanusExplicitReciprocalCrossDensityFrechet
end JanusFormal
