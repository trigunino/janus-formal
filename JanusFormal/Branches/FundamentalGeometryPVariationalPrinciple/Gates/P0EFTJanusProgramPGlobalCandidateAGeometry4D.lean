import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootInteractionDensity
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Global intrinsic Candidate-A geometry

The physically admissible metric domain is the locus on which the relative
endomorphism admits a smooth real square root.  This is deliberately a
subdomain of all Lorentz-metric pairs: the spectral obstruction gates show
that a universal real root on every pair would be false.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAGeometry4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

abbrev SmoothTangentSection :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentFiber period hPeriod point)

/-- The genuine intrinsic relative endomorphism `g₊⁻¹ g₋`. -/
def relativeEndomorphismAt
    (plus minus : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  (inverseMetricSharp period hPeriod plus point).comp
    (minus.musical point : TangentFiber period hPeriod point →L[Real] _)

/-- Maximal honest global Candidate-A domain used downstream.

Both metrics are genuine smooth sections of the same intrinsic covariant
two-tensor bundle.  Smoothness of the root is recorded by its action on the
actual smooth tangent-section space, not by chartwise matrix coefficients.
-/
structure GlobalCandidateAGeometry where
  plusMetric : SmoothGeneralLorentzMetric period hPeriod
  minusMetric : SmoothGeneralLorentzMetric period hPeriod
  rootAt : ∀ point : EffectiveQuotient period hPeriod,
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point
  rootOperator :
    SmoothTangentSection period hPeriod →ₗ[Real]
      SmoothTangentSection period hPeriod
  rootOperator_apply : ∀ vector point,
    rootOperator vector point = rootAt point (vector point)
  root_square : ∀ point,
    (rootAt point).comp (rootAt point) =
      relativeEndomorphismAt period hPeriod plusMetric minusMetric point

/-- Matrix coefficients of the intrinsic root in an arbitrary tangent basis. -/
def GlobalCandidateAGeometry.rootMatrixAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Module.Basis (Fin 4) Real (TangentFiber period hPeriod point)) :
    Matrix4 :=
  LinearMap.toMatrix frame frame (geometry.rootAt point).toLinearMap

/-- The intrinsic square-root identity in arbitrary matrix coordinates. -/
theorem GlobalCandidateAGeometry.rootMatrixAt_sq
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Module.Basis (Fin 4) Real (TangentFiber period hPeriod point)) :
    GlobalCandidateAGeometry.rootMatrixAt period hPeriod geometry point frame *
        GlobalCandidateAGeometry.rootMatrixAt period hPeriod geometry point frame =
      LinearMap.toMatrix frame frame
        (relativeEndomorphismAt period hPeriod geometry.plusMetric
          geometry.minusMetric point).toLinearMap := by
  unfold GlobalCandidateAGeometry.rootMatrixAt
  rw [← LinearMap.toMatrix_comp]
  apply congrArg (LinearMap.toMatrix frame frame)
  exact congrArg ContinuousLinearMap.toLinearMap (geometry.root_square point)

/-- Candidate-A coordinate density read from the intrinsic metric and root. -/
def GlobalCandidateAGeometry.interactionDensityAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod)
    (frame : Module.Basis (Fin 4) Real
      (TangentFiber period hPeriod point)) : Real :=
  -interactionScale *
    metricVolumeDensity period hPeriod geometry.plusMetric point frame *
    matrixSpectralPotential coefficients
      (GlobalCandidateAGeometry.rootMatrixAt period hPeriod geometry point frame)

/-- Exact identification with the established matrix coefficient model. -/
theorem GlobalCandidateAGeometry.interactionDensity_eq_coefficientModel
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod)
    (frame : Module.Basis (Fin 4) Real
      (TangentFiber period hPeriod point)) :
    GlobalCandidateAGeometry.interactionDensityAt period hPeriod geometry
        interactionScale coefficients point frame =
      -interactionScale *
        metricVolumeDensity period hPeriod geometry.plusMetric point frame *
        matrixSpectralPotential coefficients
          (GlobalCandidateAGeometry.rootMatrixAt period hPeriod geometry
            point frame) :=
  rfl

/-- Every positive conformal pair lies in the global admissible domain. -/
def conformalGlobalCandidateAGeometry
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    GlobalCandidateAGeometry period hPeriod where
  plusMetric :=
    conformalSmoothGeneralLorentzMetric period hPeriod plus hPlus
  minusMetric :=
    conformalSmoothGeneralLorentzMetric period hPeriod minus hMinus
  rootAt :=
    conformalCandidateARootAt period hPeriod plus minus
  rootOperator :=
    smoothConformalCandidateARootOperator period hPeriod plus minus hPlus hMinus
  rootOperator_apply := by
    intro vector point
    exact smoothConformalCandidateARootAction_apply period hPeriod
      plus minus hPlus hMinus vector point
  root_square := by
    intro point
    exact conformalCandidateARootAt_square period hPeriod plus minus
      hPlus hMinus point

theorem conformalGlobalCandidateAGeometry_nonempty
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    Nonempty (GlobalCandidateAGeometry period hPeriod) :=
  ⟨conformalGlobalCandidateAGeometry period hPeriod
    plus minus hPlus hMinus⟩

end
end P0EFTJanusProgramPGlobalCandidateAGeometry4D
end JanusFormal
