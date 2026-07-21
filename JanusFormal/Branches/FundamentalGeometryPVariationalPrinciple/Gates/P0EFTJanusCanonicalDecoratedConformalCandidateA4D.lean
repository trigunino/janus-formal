import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D

/-! # Conformal Candidate A on the canonical decorated mapping torus -/

namespace JanusFormal
namespace P0EFTJanusCanonicalDecoratedConformalCandidateA4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Ambient := EffectiveAmbient period hPeriod

local instance : ChartedSpace CoverModel (Ambient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω (Ambient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : Ambient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Actual conformal Candidate-A data attached to the already assembled
canonical geometric decorations. -/
structure CanonicalDecoratedConformalCandidateA
    (plus minus : SmoothScalarField period hPeriod) where
  decorations : CanonicalEffectiveDecoratedMappingTorus period hPeriod
  plusMetric : SmoothGeneralLorentzMetric period hPeriod
  minusMetric : SmoothGeneralLorentzMetric period hPeriod
  rootScale : SmoothScalarField period hPeriod
  rootOperator : SmoothAmbientTangentSection period hPeriod →ₗ[Real]
    SmoothAmbientTangentSection period hPeriod
  relativeOperator : SmoothAmbientTangentSection period hPeriod →ₗ[Real]
    SmoothAmbientTangentSection period hPeriod
  rootAt : ∀ point : Ambient period hPeriod,
    TangentFiber period hPeriod point →L[Real] TangentFiber period hPeriod point
  density : Real → PotentialCoefficients → ∀ point : Ambient period hPeriod,
    (Fin 4 → TangentFiber period hPeriod point) → Real

/-- Canonical extension by two positive conformal metrics on the same D8
base, with their intrinsic root and Candidate-A density. -/
def canonicalDecoratedConformalCandidateA
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    CanonicalDecoratedConformalCandidateA period hPeriod plus minus where
  decorations := canonicalEffectiveDecoratedMappingTorus period hPeriod
  plusMetric := conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus
  minusMetric := conformalSmoothGeneralLorentzMetric period hPeriod minus hMinus
  rootScale := smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
  rootOperator := smoothConformalCandidateARootOperator period hPeriod plus minus
    hPlus hMinus
  relativeOperator := smoothConformalRelativeOperator period hPeriod plus minus
    hPlus
  rootAt := conformalCandidateARootAt period hPeriod plus minus
  density := fun interactionScale coefficients =>
    intrinsicConformalCandidateADensity period hPeriod interactionScale
      coefficients plus minus hPlus

@[simp] theorem canonicalDecoratedConformalCandidateA_plusMetric
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    (canonicalDecoratedConformalCandidateA period hPeriod plus minus hPlus
      hMinus).plusMetric =
      conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus := rfl

@[simp] theorem canonicalDecoratedConformalCandidateA_minusMetric
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    (canonicalDecoratedConformalCandidateA period hPeriod plus minus hPlus
      hMinus).minusMetric =
      conformalSmoothGeneralLorentzMetric period hPeriod minus hMinus := rfl

@[simp] theorem canonicalDecoratedConformalCandidateA_rootScale_apply
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    (canonicalDecoratedConformalCandidateA period hPeriod plus minus hPlus
      hMinus).rootScale point = Real.sqrt (minus point / plus point) := rfl

@[simp] theorem canonicalDecoratedConformalCandidateA_rootOperator_apply
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (vector : SmoothAmbientTangentSection period hPeriod) (point) :
    ((canonicalDecoratedConformalCandidateA period hPeriod plus minus hPlus
      hMinus).rootOperator vector) point =
      (canonicalDecoratedConformalCandidateA period hPeriod plus minus hPlus
        hMinus).rootAt point (vector point) :=
  smoothConformalCandidateARootAction_apply period hPeriod plus minus hPlus
    hMinus vector point

/-- The stored root squares to the genuine relative endomorphism of the two
stored conformal metrics. -/
theorem canonicalDecoratedConformalCandidateA_root_square
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (point : Ambient period hPeriod) :
    let data := canonicalDecoratedConformalCandidateA period hPeriod plus minus
      hPlus hMinus
    (data.rootAt point).comp (data.rootAt point) =
      conformalRelativeEndomorphismAt period hPeriod plus minus hPlus hMinus
        point :=
  conformalCandidateARootAt_square period hPeriod plus minus hPlus hMinus point

/-- The stored smooth root operator squares globally to the stored relative
endomorphism operator. -/
theorem canonicalDecoratedConformalCandidateA_rootOperator_square
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    let data := canonicalDecoratedConformalCandidateA period hPeriod plus minus
      hPlus hMinus
    data.rootOperator.comp data.rootOperator = data.relativeOperator :=
  smoothConformalCandidateARootOperator_square period hPeriod plus minus hPlus
    hMinus

/-- The stored intrinsic density agrees in every tangent frame with the
isotropic `Matrix4` Candidate-A potential. -/
theorem canonicalDecoratedConformalCandidateA_density_eq_isotropicMatrix4
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (point : Ambient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    let data := canonicalDecoratedConformalCandidateA period hPeriod plus minus
      hPlus hMinus
    data.density interactionScale coefficients point frame =
      -interactionScale *
        metricVolumeDensity period hPeriod data.plusMetric point frame *
        matrixSpectralPotential coefficients
          (Matrix.diagonal (proportionalSpectrum
            (Real.sqrt (minus point / plus point)))) :=
  intrinsicConformalCandidateADensity_eq_isotropicMatrix4 period hPeriod
    interactionScale coefficients plus minus hPlus point frame

end
end P0EFTJanusCanonicalDecoratedConformalCandidateA4D
end JanusFormal
