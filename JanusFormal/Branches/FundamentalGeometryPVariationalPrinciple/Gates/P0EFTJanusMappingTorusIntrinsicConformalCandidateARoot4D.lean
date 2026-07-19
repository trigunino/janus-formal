import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootInteractionDensity

/-!
# Intrinsic conformal Candidate-A root on the effective D8 quotient

For two positive smooth conformal factors `a,b`, this gate constructs the
genuine metrics `a g₀,b g₀`, their relative endomorphism, its positive
scalar square root, and the corresponding Candidate-A density.  The result is
global on D8 but restricted to the conformal sector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

/-- Intrinsic conformal rescaling of the certified D8 Lorentz tensor. -/
def conformalLorentzTensor
    (scale : SmoothScalarField period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := fun point => scale point •
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
      contMDiff_toFun := scale.contMDiff_toFun.smul_section
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor.contMDiff }
  symmetric := by
    intro point first second
    change scale point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          first second =
      scale point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          second first
    rw [(intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.symmetric]

private def conformalMusical
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      CotangentFiber period hPeriod point :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point |>.trans
    (ContinuousLinearEquiv.smulLeft
      (Units.mk0 (scale point) (ne_of_gt (hScale point))))

/-- The positive conformal rescaling is a genuine smooth general Lorentz
metric; its inverse is tied to this same rescaled tensor. -/
def conformalSmoothGeneralLorentzMetric
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor := conformalLorentzTensor period hPeriod scale
  musical := conformalMusical period hPeriod scale hScale
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change scale point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point
          first second =
      scale point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          first second
    congr 1
    exact DFunLike.congr_fun
      (DFunLike.congr_fun
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor point)
        first) second
  lorentzian := by
    intro point
    rcases (intrinsicSmoothGeneralLorentzMetric period hPeriod).lorentzian point with
      ⟨frame, hFrame⟩
    have hSqrt : Real.sqrt (scale point) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hScale point))
    let scaledFrame := frame.trans
      (ContinuousLinearEquiv.smulLeft
        (Units.mk0 (Real.sqrt (scale point)) hSqrt))
    refine ⟨scaledFrame, ?_⟩
    intro first second
    change scale point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          first second =
      modelMinkowskiPair (scaledFrame first) (scaledFrame second)
    rw [hFrame]
    simp only [scaledFrame, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply]
    simp only [Units.smul_def, Units.val_mk0]
    unfold modelMinkowskiPair
    rw [show (Real.sqrt (scale point) • frame first).1 =
        Real.sqrt (scale point) • (frame first).1 from rfl,
      show (Real.sqrt (scale point) • frame second).1 =
        Real.sqrt (scale point) • (frame second).1 from rfl,
      show (Real.sqrt (scale point) • frame first).2 =
        Real.sqrt (scale point) • (frame first).2 from rfl,
      show (Real.sqrt (scale point) • frame second).2 =
        Real.sqrt (scale point) • (frame second).2 from rfl]
    simp only [real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
    have hs : Real.sqrt (scale point) * Real.sqrt (scale point) = scale point :=
      Real.mul_self_sqrt (le_of_lt (hScale point))
    calc
      scale point *
          (inner Real (frame first).1 (frame second).1 -
            (frame first).2 * (frame second).2) =
        (Real.sqrt (scale point) * Real.sqrt (scale point)) *
          (inner Real (frame first).1 (frame second).1 -
            (frame first).2 * (frame second).2) := by rw [hs]
      _ = _ := by ring

/-- The genuine relative endomorphism `g₊⁻¹ g₋` on the same tangent fiber. -/
def conformalRelativeEndomorphismAt
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  (inverseMetricSharp period hPeriod
      (conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus) point).comp
    (((conformalSmoothGeneralLorentzMetric period hPeriod minus hMinus).musical point :
      TangentFiber period hPeriod point →L[Real]
        CotangentFiber period hPeriod point))

theorem conformalRelativeEndomorphismAt_apply
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    conformalRelativeEndomorphismAt period hPeriod plus minus hPlus hMinus
        point vector =
      (minus point / plus point) • vector := by
  change
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point).symm
      (((ContinuousLinearEquiv.smulLeft
          (Units.mk0 (plus point) (ne_of_gt (hPlus point))) :
        CotangentFiber period hPeriod point ≃L[Real]
          CotangentFiber period hPeriod point)).symm
        ((ContinuousLinearEquiv.smulLeft
          (Units.mk0 (minus point) (ne_of_gt (hMinus point))) :
        CotangentFiber period hPeriod point ≃L[Real]
          CotangentFiber period hPeriod point)
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector))) = _
  have hScaled :
      ((ContinuousLinearEquiv.smulLeft
          (Units.mk0 (plus point) (ne_of_gt (hPlus point))) :
        CotangentFiber period hPeriod point ≃L[Real]
          CotangentFiber period hPeriod point)).symm
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector) =
        (plus point)⁻¹ •
          (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector := by
    let scaleEquiv : CotangentFiber period hPeriod point ≃L[Real]
        CotangentFiber period hPeriod point :=
      ContinuousLinearEquiv.smulLeft
        (Units.mk0 (plus point) (ne_of_gt (hPlus point)))
    apply scaleEquiv.injective
    change scaleEquiv
        (scaleEquiv.symm
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector)) =
      scaleEquiv ((plus point)⁻¹ •
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simp only [scaleEquiv, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_def, Units.val_mk0]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hPlus point)), one_smul]
  have hMinusScaled :
      (ContinuousLinearEquiv.smulLeft
          (Units.mk0 (minus point) (ne_of_gt (hMinus point))) :
        CotangentFiber period hPeriod point ≃L[Real]
          CotangentFiber period hPeriod point)
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector) =
        minus point •
          (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point vector := by
    simp only [ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_def, Units.val_mk0]
  rw [hMinusScaled, map_smul, hScaled, map_smul, map_smul,
    ContinuousLinearEquiv.symm_apply_apply, smul_smul]
  congr 1

/-- Positive intrinsic Candidate-A root `sqrt(b/a) id`. -/
def conformalCandidateARootAt
    (plus minus : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  Real.sqrt (minus point / plus point) • ContinuousLinearMap.id Real _

theorem conformalCandidateARootAt_apply
    (plus minus : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    conformalCandidateARootAt period hPeriod plus minus point vector =
      Real.sqrt (minus point / plus point) • vector := by
  rfl

theorem conformalCandidateARootAt_square
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (point : EffectiveQuotient period hPeriod) :
    (conformalCandidateARootAt period hPeriod plus minus point).comp
        (conformalCandidateARootAt period hPeriod plus minus point) =
      conformalRelativeEndomorphismAt period hPeriod plus minus hPlus hMinus
        point := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [ContinuousLinearMap.comp_apply, conformalCandidateARootAt_apply,
    conformalCandidateARootAt_apply,
    conformalRelativeEndomorphismAt_apply]
  rw [← mul_smul, Real.mul_self_sqrt
    (div_nonneg (le_of_lt (hMinus point)) (le_of_lt (hPlus point)))]

/-- The intrinsic plus-measure Candidate-A density in an arbitrary tangent
frame. -/
def intrinsicConformalCandidateADensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  -interactionScale *
    metricVolumeDensity period hPeriod
      (conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus) point frame *
    proportionalPotential coefficients (Real.sqrt (minus point / plus point))

/-- Every tangent frame reads the same scalar root eigenvalue. -/
theorem conformalCandidateARootAt_in_every_frame
    (plus minus : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point)
    (index : Fin 4) :
    conformalCandidateARootAt period hPeriod plus minus point (frame index) =
      Real.sqrt (minus point / plus point) • frame index :=
  conformalCandidateARootAt_apply period hPeriod plus minus point (frame index)

/-- In every tangent frame, the intrinsic density uses exactly the isotropic
`Matrix4` Candidate-A potential. -/
theorem intrinsicConformalCandidateADensity_eq_isotropicMatrix4
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    intrinsicConformalCandidateADensity period hPeriod interactionScale
        coefficients plus minus hPlus point frame =
      -interactionScale *
        metricVolumeDensity period hPeriod
          (conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus)
          point frame *
        matrixSpectralPotential coefficients
          (Matrix.diagonal (proportionalSpectrum
            (Real.sqrt (minus point / plus point)))) := by
  unfold intrinsicConformalCandidateADensity
  rw [matrixSpectralPotential_diagonal,
    spectralPotential_on_proportionalSpectrum]

end
end P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
end JanusFormal
