import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensityFrechet

/-!
Exact Euler equations of Candidate A on its current spectral point chart, with
two independent quadratic matter slots.  The cross interaction depends only
on the square-root spectrum; the matter equations therefore form separate
blocks of the actual derivative.

This gate is pointwise and finite-dimensional.  It is not the metric
Einstein--Hilbert Euler operator, a spacetime matter PDE, or a covariant
Bianchi identity.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitCandidatePointwiseEuler

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusExplicitReciprocalCrossDensityFrechet
open P0EFTJanusConvexHelmholtzReconstruction

/-- Spectrum together with two independent scalar matter coordinates. -/
abbrev CandidateConfiguration := SquareRootSpectrum × (ℝ × ℝ)

/-- Independent pointwise quadratic matter data for the two sheets. -/
structure MatterCoefficients where
  plusMass : ℝ
  plusSource : ℝ
  minusMass : ℝ
  minusSource : ℝ

def spectrumProjection : CandidateConfiguration →L[ℝ] SquareRootSpectrum :=
  ContinuousLinearMap.fst ℝ SquareRootSpectrum (ℝ × ℝ)

def matterPairProjection : CandidateConfiguration →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.snd ℝ SquareRootSpectrum (ℝ × ℝ)

def plusMatterProjection : CandidateConfiguration →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp matterPairProjection

def minusMatterProjection : CandidateConfiguration →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp matterPairProjection

@[simp]
theorem spectrumProjection_apply (configuration : CandidateConfiguration) :
    spectrumProjection configuration = configuration.1 := by
  rfl

@[simp]
theorem plusMatterProjection_apply (configuration : CandidateConfiguration) :
    plusMatterProjection configuration = configuration.2.1 := by
  rfl

@[simp]
theorem minusMatterProjection_apply (configuration : CandidateConfiguration) :
    minusMatterProjection configuration = configuration.2.2 := by
  rfl

def plusMatterPotential
    (matter : MatterCoefficients) (field : ℝ) : ℝ :=
  matter.plusMass / 2 * field ^ 2 + matter.plusSource * field

def minusMatterPotential
    (matter : MatterCoefficients) (field : ℝ) : ℝ :=
  matter.minusMass / 2 * field ^ 2 + matter.minusSource * field

/-- One explicit pointwise action: common spectral interaction plus two
independent matter potentials. -/
def candidatePointwiseAction
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) : ℝ :=
  commonInteractionPotential interactionScale coefficients configuration.1 +
    plusMatterPotential matter configuration.2.1 +
    minusMatterPotential matter configuration.2.2

/-- The displayed three-block Euler one-form. -/
def candidatePointwiseEuler
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    CandidateConfiguration →L[ℝ] ℝ :=
  (commonInteractionGradient interactionScale coefficients configuration.1).comp
      spectrumProjection +
    (matter.plusMass * configuration.2.1 + matter.plusSource) •
      plusMatterProjection +
    (matter.minusMass * configuration.2.2 + matter.minusSource) •
      minusMatterProjection

@[simp]
theorem candidatePointwiseEuler_apply
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients)
    (configuration variation : CandidateConfiguration) :
    candidatePointwiseEuler interactionScale coefficients matter configuration
        variation =
      commonInteractionGradient interactionScale coefficients configuration.1
          variation.1 +
        (matter.plusMass * configuration.2.1 + matter.plusSource) *
          variation.2.1 +
        (matter.minusMass * configuration.2.2 + matter.minusSource) *
          variation.2.2 := by
  simp [candidatePointwiseEuler, smul_eq_mul]

/-- The three displayed components are the genuine derivative of the action. -/
theorem candidatePointwiseAction_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    HasFDerivAt
      (candidatePointwiseAction interactionScale coefficients matter)
      (candidatePointwiseEuler interactionScale coefficients matter configuration)
      configuration := by
  have hSpectrum : HasFDerivAt
      (fun point : CandidateConfiguration => point.1)
      spectrumProjection configuration := by
    simpa [spectrumProjection] using spectrumProjection.hasFDerivAt
  have hMatterPair : HasFDerivAt
      (fun point : CandidateConfiguration => point.2)
      matterPairProjection configuration := by
    simpa [matterPairProjection] using matterPairProjection.hasFDerivAt
  have hPlus : HasFDerivAt
      (fun point : CandidateConfiguration => point.2.1)
      plusMatterProjection configuration := by
    have hCoordinate : HasFDerivAt (fun point : ℝ × ℝ => point.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) configuration.2 :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    exact (hCoordinate.comp configuration hMatterPair).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hMinus : HasFDerivAt
      (fun point : CandidateConfiguration => point.2.2)
      minusMatterProjection configuration := by
    have hCoordinate : HasFDerivAt (fun point : ℝ × ℝ => point.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) configuration.2 :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    exact (hCoordinate.comp configuration hMatterPair).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hInteraction :=
    (commonInteractionPotential_hasFDerivAt interactionScale coefficients
      configuration.1).comp configuration hSpectrum
  have hPlusPotential :=
    ((hPlus.mul hPlus).const_mul (matter.plusMass / 2)).add
      (hPlus.const_mul matter.plusSource)
  have hMinusPotential :=
    ((hMinus.mul hMinus).const_mul (matter.minusMass / 2)).add
      (hMinus.const_mul matter.minusSource)
  have hTotal := (hInteraction.add hPlusPotential).add hMinusPotential
  refine (hTotal.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · apply ContinuousLinearMap.ext
    intro variation
    simp [candidatePointwiseEuler, smul_eq_mul]
    ring
  · intro point
    simp [candidatePointwiseAction, plusMatterPotential, minusMatterPotential,
      pow_two]

theorem candidatePointwiseAction_fderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    fderiv ℝ (candidatePointwiseAction interactionScale coefficients matter)
        configuration =
      candidatePointwiseEuler interactionScale coefficients matter configuration :=
  (candidatePointwiseAction_hasFDerivAt interactionScale coefficients matter
    configuration).fderiv

/-- Precomposition of a spectral covector with the spectrum projection. -/
def spectrumCovectorLift :
    (SquareRootSpectrum →L[ℝ] ℝ) →L[ℝ]
      (CandidateConfiguration →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ CandidateConfiguration SquareRootSpectrum ℝ).flip
    spectrumProjection

@[simp]
theorem spectrumCovectorLift_apply
    (covector : SquareRootSpectrum →L[ℝ] ℝ) :
    spectrumCovectorLift covector = covector.comp spectrumProjection := by
  rfl

/-- Exact block Hessian of the explicit pointwise candidate. -/
def candidatePointwiseHessian
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    CandidateConfiguration →L[ℝ]
      CandidateConfiguration →L[ℝ] ℝ :=
  spectrumCovectorLift.comp
      ((commonInteractionHessian interactionScale coefficients configuration.1).comp
        spectrumProjection) +
    (matter.plusMass • plusMatterProjection).smulRight plusMatterProjection +
    (matter.minusMass • minusMatterProjection).smulRight minusMatterProjection

@[simp]
theorem candidatePointwiseHessian_apply
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients)
    (configuration first second : CandidateConfiguration) :
    candidatePointwiseHessian interactionScale coefficients matter configuration
        first second =
      commonInteractionHessian interactionScale coefficients configuration.1
          first.1 second.1 +
        matter.plusMass * first.2.1 * second.2.1 +
        matter.minusMass * first.2.2 * second.2.2 := by
  simp [candidatePointwiseHessian, smul_eq_mul]

/-- The displayed Hessian is the genuine Frechet derivative of the full Euler
one-form, including both independent matter blocks. -/
theorem candidatePointwiseEuler_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    HasFDerivAt
      (candidatePointwiseEuler interactionScale coefficients matter)
      (candidatePointwiseHessian interactionScale coefficients matter configuration)
      configuration := by
  have hSpectrum : HasFDerivAt
      (fun point : CandidateConfiguration => point.1)
      spectrumProjection configuration := by
    simpa [spectrumProjection] using spectrumProjection.hasFDerivAt
  have hMatterPair : HasFDerivAt
      (fun point : CandidateConfiguration => point.2)
      matterPairProjection configuration := by
    simpa [matterPairProjection] using matterPairProjection.hasFDerivAt
  have hPlus : HasFDerivAt
      (fun point : CandidateConfiguration => point.2.1)
      plusMatterProjection configuration := by
    have hCoordinate : HasFDerivAt (fun point : ℝ × ℝ => point.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) configuration.2 :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    exact (hCoordinate.comp configuration hMatterPair).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hMinus : HasFDerivAt
      (fun point : CandidateConfiguration => point.2.2)
      minusMatterProjection configuration := by
    have hCoordinate : HasFDerivAt (fun point : ℝ × ℝ => point.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) configuration.2 :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    exact (hCoordinate.comp configuration hMatterPair).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hInteractionBase :=
    (commonInteractionGradient_hasFDerivAt interactionScale coefficients
      configuration.1).comp configuration hSpectrum
  have hInteractionLift : HasFDerivAt
      (fun covector : SquareRootSpectrum →L[ℝ] ℝ =>
        spectrumCovectorLift covector)
      spectrumCovectorLift
      (commonInteractionGradient interactionScale coefficients
        configuration.1) := by
    exact spectrumCovectorLift.hasFDerivAt
  have hInteraction :=
    hInteractionLift.comp configuration hInteractionBase
  have hPlusCoefficient :=
    (hPlus.const_mul matter.plusMass).const_add matter.plusSource
  have hMinusCoefficient :=
    (hMinus.const_mul matter.minusMass).const_add matter.minusSource
  have hPlusEuler := hPlusCoefficient.smul_const plusMatterProjection
  have hMinusEuler := hMinusCoefficient.smul_const minusMatterProjection
  have hTotal := (hInteraction.add hPlusEuler).add hMinusEuler
  refine hTotal.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro point
  apply ContinuousLinearMap.ext
  intro variation
  simp [candidatePointwiseEuler, spectrumCovectorLift, smul_eq_mul]
  ring

theorem candidatePointwiseEuler_fderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    fderiv ℝ (candidatePointwiseEuler interactionScale coefficients matter)
        configuration =
      candidatePointwiseHessian interactionScale coefficients matter
        configuration :=
  (candidatePointwiseEuler_hasFDerivAt interactionScale coefficients matter
    configuration).fderiv

theorem candidatePointwiseHessian_symmetric
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients)
    (configuration first second : CandidateConfiguration) :
    candidatePointwiseHessian interactionScale coefficients matter configuration
        first second =
      candidatePointwiseHessian interactionScale coefficients matter configuration
        second first := by
  rw [candidatePointwiseHessian_apply, candidatePointwiseHessian_apply]
  have hInteraction :
      commonInteractionHessian interactionScale coefficients configuration.1
          first.1 second.1 =
        commonInteractionHessian interactionScale coefficients configuration.1
          second.1 first.1 := by
    change (-interactionScale) *
        spectralHessian coefficients configuration.1 first.1 second.1 =
      (-interactionScale) *
        spectralHessian coefficients configuration.1 second.1 first.1
    rw [spectralHessian_symmetric coefficients configuration.1 first.1 second.1]
  rw [hInteraction]
  ring

/-- The full pointwise Euler family passes the nonlinear Helmholtz symmetry
test on this product chart. -/
theorem candidatePointwiseEuler_helmholtzJacobianAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    HelmholtzJacobianAt
      (candidatePointwiseEuler interactionScale coefficients matter)
      configuration := by
  intro first second
  rw [candidatePointwiseEuler_fderiv]
  exact candidatePointwiseHessian_symmetric interactionScale coefficients matter
    configuration first second

def spectrumVariation (direction : SquareRootSpectrum) :
    CandidateConfiguration :=
  (direction, (0, 0))

def plusMatterVariation (direction : ℝ) : CandidateConfiguration :=
  (0, (direction, 0))

def minusMatterVariation (direction : ℝ) : CandidateConfiguration :=
  (0, (0, direction))

/-- Both interaction--matter mixed Hessian blocks vanish exactly. -/
theorem interaction_matter_cross_hessian_vanishes
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration)
    (spectrumDirection : SquareRootSpectrum)
    (plusDirection minusDirection : ℝ) :
    candidatePointwiseHessian interactionScale coefficients matter configuration
        (spectrumVariation spectrumDirection)
        (plusMatterVariation plusDirection) = 0 ∧
      candidatePointwiseHessian interactionScale coefficients matter configuration
        (spectrumVariation spectrumDirection)
        (minusMatterVariation minusDirection) = 0 := by
  simp [spectrumVariation, plusMatterVariation, minusMatterVariation]

/-- Vanishing of the full derivative, with no component split assumed. -/
def CandidatePointwiseStationary
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) : Prop :=
  candidatePointwiseEuler interactionScale coefficients matter configuration = 0

/-- The explicit independent Euler components. -/
def CandidateEulerComponentsVanish
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) : Prop :=
  commonInteractionGradient interactionScale coefficients configuration.1 = 0 ∧
    matter.plusMass * configuration.2.1 + matter.plusSource = 0 ∧
    matter.minusMass * configuration.2.2 + matter.minusSource = 0

/-- Stationarity is exactly the spectral equation and the two independent
matter equations. -/
theorem candidatePointwiseStationary_iff_euler_components
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (matter : MatterCoefficients) (configuration : CandidateConfiguration) :
    CandidatePointwiseStationary interactionScale coefficients matter
        configuration ↔
      CandidateEulerComponentsVanish interactionScale coefficients matter
        configuration := by
  constructor
  · intro hStationary
    have hSpectrum :
        commonInteractionGradient interactionScale coefficients
            configuration.1 = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      have hEvaluate := congrArg
        (fun linear : CandidateConfiguration →L[ℝ] ℝ =>
          linear (direction, (0, 0))) hStationary
      simpa [CandidatePointwiseStationary] using hEvaluate
    have hPlus :
        matter.plusMass * configuration.2.1 + matter.plusSource = 0 := by
      have hEvaluate := congrArg
        (fun linear : CandidateConfiguration →L[ℝ] ℝ =>
          linear (0, (1, 0))) hStationary
      simpa [CandidatePointwiseStationary] using hEvaluate
    have hMinus :
        matter.minusMass * configuration.2.2 + matter.minusSource = 0 := by
      have hEvaluate := congrArg
        (fun linear : CandidateConfiguration →L[ℝ] ℝ =>
          linear (0, (0, 1))) hStationary
      simpa [CandidatePointwiseStationary] using hEvaluate
    exact ⟨hSpectrum, hPlus, hMinus⟩
  · rintro ⟨hSpectrum, hPlus, hMinus⟩
    apply ContinuousLinearMap.ext
    intro variation
    simp [candidatePointwiseEuler_apply, hSpectrum, hPlus, hMinus]

/-- Changing either matter coordinate leaves the interaction Euler block
unchanged: matter independence is exact in this candidate. -/
theorem interactionEuler_matter_independent
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum)
    (plusMatter minusMatter plusMatter' minusMatter' : ℝ) :
    commonInteractionGradient interactionScale coefficients
        (spectrum, (plusMatter, minusMatter)).1 =
      commonInteractionGradient interactionScale coefficients
        (spectrum, (plusMatter', minusMatter')).1 := by
  rfl

end

end P0EFTJanusExplicitCandidatePointwiseEuler
end JanusFormal
