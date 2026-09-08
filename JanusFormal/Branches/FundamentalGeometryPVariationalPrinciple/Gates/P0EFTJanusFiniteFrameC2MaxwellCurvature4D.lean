import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2AbelianOperators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCovectorC2Projection4D

/-! # Maxwell curvature on the redundant finite C² frame

The projected potential coefficients determine the genuine Cartan curvature
on smooth lifts.  The construction uses only the fixed finite generating
family, so it does not require a global tangent basis.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MaxwellCurvature4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame

private theorem smoothScalarSum_apply
    (fields : Fin frame.count → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ index, fields index) point = ∑ index, fields index point := by
  let evaluation : SmoothScalarField period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

private theorem smoothScalarSub_apply
    (first second : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (first - second) point = first point - second point := rfl

private theorem smoothToContinuous_apply
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod field point = field point := rfl

/-- Evaluation of one completed potential coefficient. -/
def finiteFrameGaugePotentialCoefficientCLM (component : Fin 2)
    (index : Fin frame.count) :
    GaugeCore →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj index :
      (Fin frame.count → C2Scalar period hPeriod) →L[Real] C2Scalar period hPeriod).comp
    (ContinuousLinearMap.proj component :
      GaugeCore →L[Real]
        (Fin frame.count → C2Scalar period hPeriod))

/-- The smooth potential evaluated on the intrinsic bracket of two generators. -/
def finiteFrameBracketPotentialCoefficient
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) :
    SmoothScalarField period hPeriod where
  toFun := fun point => potential.toFun component point
    (smoothGhostLieBracket period hPeriod
      (smoothFrameVectorSection period hPeriod frame first)
      (smoothFrameVectorSection period hPeriod frame second) point)
  contMDiff_toFun := (potential.contMDiff_eval component).comp
    (smoothGhostLieBracket period hPeriod
      (smoothFrameVectorSection period hPeriod frame first)
      (smoothFrameVectorSection period hPeriod frame second)).contMDiff

/-- Redundant structure coefficients reconstruct the bracket contribution exactly. -/
theorem finiteFrameBracketPotentialCoefficient_eq_sum
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) :
    finiteFrameBracketPotentialCoefficient period hPeriod frame potential
        component first second =
      ∑ upper : Fin frame.count, smoothScalarFieldMul period hPeriod
        (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second upper)
        (finiteFramePotentialCoefficient period hPeriod frame potential component upper) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hBracket := finiteFrameStructureCoefficient_reconstructs period hPeriod
    frame baseMetric first second point
  have hApplied := congrArg
    (fun vector => potential.toFun component point vector) hBracket
  simpa only [finiteFrameBracketPotentialCoefficient,
    finiteFramePotentialCoefficient_apply, smoothScalarFieldMul_apply,
    smoothScalarSum_apply, map_sum, map_smul, smul_eq_mul] using hApplied

/-- Genuine Cartan curvature evaluated on two members of the generating family. -/
def finiteFrameSmoothGaugeCurvatureCoefficient
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) :
    SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod frame
      (finiteFramePotentialCoefficient period hPeriod frame potential component second) first -
    frameDerivativeComponentField period hPeriod frame
      (finiteFramePotentialCoefficient period hPeriod frame potential component first) second -
    finiteFrameBracketPotentialCoefficient period hPeriod frame potential component first second

/-- C⁰ Cartan curvature obtained from an arbitrary completed coefficient packet. -/
def finiteFrameGaugeCurvatureC0Coefficient (potential : GaugeCore)
    (component : Fin 2) (first second : Fin frame.count) : C0Scalar period hPeriod :=
  finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame first
      (potential component second) -
    finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame second
      (potential component first) -
    ∑ upper : Fin frame.count,
      finiteFrameStructureC0Coefficient period hPeriod frame baseMetric first second upper *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (potential component upper)

/-- The completed curvature depends smoothly on all potential coefficients. -/
theorem finiteFrameGaugeCurvatureC0Coefficient_contDiff
    (component : Fin 2) (first second : Fin frame.count) :
    ContDiff Real ∞ (fun potential : GaugeCore =>
      finiteFrameGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        potential component first second) := by
  have hCoefficient (index : Fin frame.count) : ContDiff Real ∞
      (fun potential : GaugeCore => potential component index) :=
    (finiteFrameGaugePotentialCoefficientCLM period hPeriod frame component index).contDiff
  have hFirst :=
    (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame first).contDiff.comp
      (hCoefficient second)
  have hSecond :=
    (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame second).contDiff.comp
      (hCoefficient first)
  have hBracket : ContDiff Real ∞ (fun potential : GaugeCore =>
      ∑ upper : Fin frame.count,
        finiteFrameStructureC0Coefficient period hPeriod frame baseMetric first second upper *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (potential component upper)) := by
    apply ContDiff.sum
    intro upper _
    exact contDiff_const.mul
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp
        (hCoefficient upper))
  exact (hFirst.sub hSecond).sub hBracket

/-- Smooth lifts give exactly the genuine Cartan curvature of the same potential. -/
theorem finiteFrameGaugeCurvatureC0Coefficient_smooth
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) :
    finiteFrameGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential)
        component first second =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
          component first second) := by
  rw [finiteFrameSmoothGaugeCurvatureCoefficient,
    finiteFrameBracketPotentialCoefficient_eq_sum period hPeriod frame baseMetric]
  apply ContinuousMap.ext
  intro point
  simp only [finiteFrameGaugeCurvatureC0Coefficient,
    finiteFrameSmoothAbelianGaugeC2Coefficients, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    smoothToContinuous_apply,
    finiteFrameScalarC2FirstDerivative_smooth,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    smoothScalarSub_apply, smoothScalarSum_apply,
    smoothScalarFieldMul_apply, frameDerivativeComponentField,
    finiteFrameStructureC0Coefficient]

/-- Maxwell uses the canonical covector projection before differentiating redundant coefficients. -/
def finiteFrameProjectedGaugeCurvatureC0Coefficient
    (potential : GaugeCore)
    (component : Fin 2) (first second : Fin frame.count) : C0Scalar period hPeriod :=
  finiteFrameGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
    (finiteFrameGaugeC2Projection period hPeriod frame baseMetric potential)
      component first second

theorem finiteFrameProjectedGaugeCurvatureC0Coefficient_contDiff
    (component : Fin 2) (first second : Fin frame.count) :
    ContDiff Real ∞ (fun potential : GaugeCore =>
      finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        potential component first second) :=
  (finiteFrameGaugeCurvatureC0Coefficient_contDiff period hPeriod frame baseMetric
    component first second).comp
      (finiteFrameGaugeC2Projection period hPeriod frame baseMetric).contDiff

/-- Projection does not change the curvature of an actual smooth potential. -/
theorem finiteFrameProjectedGaugeCurvatureC0Coefficient_smooth
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) :
    finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential)
        component first second =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
          component first second) := by
  unfold finiteFrameProjectedGaugeCurvatureC0Coefficient
  unfold finiteFrameSmoothAbelianGaugeC2Coefficients
  rw [finiteFrameGaugeC2Projection_fixes_potential period hPeriod frame baseMetric]
  exact finiteFrameGaugeCurvatureC0Coefficient_smooth period hPeriod frame baseMetric
    potential component first second

end
end P0EFTJanusFiniteFrameC2MaxwellCurvature4D
end JanusFormal
