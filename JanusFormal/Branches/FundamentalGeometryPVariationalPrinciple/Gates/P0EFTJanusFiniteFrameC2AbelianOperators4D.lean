import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2KoszulConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameLorenzCovariantTrace4D

/-! # Genuine abelian Lorenz and FP operators on finite-frame C² coefficients

The inverse metric and connection vary jointly with the metric. Potential
coefficients are unrestricted; the smooth lift retains the given intrinsic
potential. FP reads only the first and ordered second jets of the same scalar ghost.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2AbelianOperators4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D

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

abbrev FiniteFrameAbelianPotentialC2Core (frame : SmoothD8Frame period hPeriod) :=
  Fin frame.count → C2Scalar period hPeriod

/-- Two Lie-algebra components, each evaluated on the finite generating family. -/
abbrev FiniteFrameAbelianGaugeC2Core (frame : SmoothD8Frame period hPeriod) :=
  Fin 2 → FiniteFrameAbelianPotentialC2Core period hPeriod frame

abbrev FiniteFrameAbelianGhostC2Core := Fin 2 → C2Scalar period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "MetricCore" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "GhostCore" => FiniteFrameAbelianGhostC2Core period hPeriod

def finiteFrameC2AbelianLorenzDomain : Set (MetricCore × GaugeCore) :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ×ˢ Set.univ

def finiteFrameC2AbelianFPDomain : Set (MetricCore × GhostCore) :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2AbelianLorenzDomain_isOpen :
    IsOpen (finiteFrameC2AbelianLorenzDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

theorem finiteFrameC2AbelianFPDomain_isOpen :
    IsOpen (finiteFrameC2AbelianFPDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

def finiteFrameC2AbelianLorenzExpression (variation : MetricCore)
    (potential : FiniteFrameAbelianPotentialC2Core period hPeriod frame) : C0Scalar period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second variation *
      (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame first (potential second) -
        ∑ upper : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second variation *
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (potential upper))

def finiteFrameC2AbelianFPExpression (variation : MetricCore) (ghost : C2Scalar period hPeriod) :
    C0Scalar period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second variation *
      (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame first second ghost -
        ∑ upper : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second variation *
            finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame upper ghost)

def finiteFrameC2AbelianLorenzComponentExpression (variation : MetricCore)
    (potential : GaugeCore) (component : Fin 2) : C0Scalar period hPeriod :=
  finiteFrameC2AbelianLorenzExpression period hPeriod frame baseMetric variation (potential component)

def finiteFrameC2AbelianFPComponentExpression (variation : MetricCore)
    (ghost : GhostCore) (component : Fin 2) : C0Scalar period hPeriod :=
  finiteFrameC2AbelianFPExpression period hPeriod frame baseMetric variation (ghost component)

theorem finiteFrameC2AbelianLorenzComponentExpression_contDiffOn (component : Fin 2) :
    ContDiffOn Real ∞ (fun input : MetricCore × GaugeCore =>
      finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame baseMetric input.1 input.2 component)
      (finiteFrameC2AbelianLorenzDomain period hPeriod frame baseMetric) := by
  have hInverse (first second : Fin frame.count) : ContDiffOn Real ∞
      (fun input : MetricCore × GaugeCore =>
        finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second input.1)
      (finiteFrameC2AbelianLorenzDomain period hPeriod frame baseMetric) :=
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric first second).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGamma (upper first second : Fin frame.count) : ContDiffOn Real ∞
      (fun input : MetricCore × GaugeCore =>
        finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second input.1)
      (finiteFrameC2AbelianLorenzDomain period hPeriod frame baseMetric) :=
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame baseMetric upper first second).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hCoefficient (index : Fin frame.count) : ContDiff Real ∞
      (fun input : MetricCore × GaugeCore => input.2 component index) :=
    (contDiff_apply Real (C2Scalar period hPeriod) index).comp
      ((contDiff_apply Real (FiniteFrameAbelianPotentialC2Core period hPeriod frame) component).comp contDiff_snd)
  unfold finiteFrameC2AbelianLorenzComponentExpression finiteFrameC2AbelianLorenzExpression
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ => (hInverse first second).mul
    (((finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame first).contDiff.comp
      (hCoefficient second)).contDiffOn.sub
        (ContDiffOn.sum fun upper _ => (hGamma upper first second).mul
          (((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp
            (hCoefficient upper)).contDiffOn)))

theorem finiteFrameC2AbelianFPComponentExpression_contDiffOn (component : Fin 2) :
    ContDiffOn Real ∞ (fun input : MetricCore × GhostCore =>
      finiteFrameC2AbelianFPComponentExpression period hPeriod frame baseMetric input.1 input.2 component)
      (finiteFrameC2AbelianFPDomain period hPeriod frame baseMetric) := by
  have hInverse (first second : Fin frame.count) : ContDiffOn Real ∞
      (fun input : MetricCore × GhostCore =>
        finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second input.1)
      (finiteFrameC2AbelianFPDomain period hPeriod frame baseMetric) :=
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric first second).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGamma (upper first second : Fin frame.count) : ContDiffOn Real ∞
      (fun input : MetricCore × GhostCore =>
        finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second input.1)
      (finiteFrameC2AbelianFPDomain period hPeriod frame baseMetric) :=
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame baseMetric upper first second).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGhost : ContDiff Real ∞ (fun input : MetricCore × GhostCore => input.2 component) :=
    (contDiff_apply Real (C2Scalar period hPeriod) component).comp contDiff_snd
  unfold finiteFrameC2AbelianFPComponentExpression finiteFrameC2AbelianFPExpression
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ => (hInverse first second).mul
    (((finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame first second).contDiff.comp
      hGhost).contDiffOn.sub
        (ContDiffOn.sum fun upper _ => (hGamma upper first second).mul
          (((finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame upper).contDiff.comp hGhost).contDiffOn)))

def finiteFrameSmoothAbelianGaugeC2Coefficients (potential : SmoothAbelianGaugePotential period hPeriod) :
    FiniteFrameAbelianGaugeC2Core period hPeriod frame :=
  fun component index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (finiteFramePotentialCoefficient period hPeriod frame potential component index)

def finiteFrameSmoothAbelianGhostC2Coefficients
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) : GhostCore :=
  fun component => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (ghostComponent period hPeriod ghost component)

/-- The exact potential has precisely the first directional ghost coefficient. -/
theorem finiteFramePotentialCoefficient_exact
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) (index : Fin frame.count) :
    finiteFramePotentialCoefficient period hPeriod frame (exactGaugePotential period hPeriod ghost) component index =
      frameDerivativeComponentField period hPeriod frame (ghostComponent period hPeriod ghost component) index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- Whole C⁰ agreement with the intrinsic Lorenz codifferential of the given potential. -/
theorem finiteFrameC2AbelianLorenzComponentExpression_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) component =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (ghostComponent period hPeriod
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential) component) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameC2AbelianLorenzExpression period hPeriod frame baseMetric
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
    (fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame potential component index)) point =
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential point component
  rw [globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace
    period hPeriod frame baseMetric metric potential component point]
  simp only [finiteFrameC2AbelianLorenzExpression, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.sub_apply, finiteFrameScalarC2FirstDerivative_smooth,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric hVariation]
  rfl

/-- Whole C⁰ agreement with the actual `δ_g d` of the same two-component ghost. -/
theorem finiteFrameC2AbelianFPComponentExpression_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    finiteFrameC2AbelianFPComponentExpression period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
      (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod ghost) component =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (ghostComponent period hPeriod (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost) component) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameC2AbelianFPExpression period hPeriod frame baseMetric
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (ghostComponent period hPeriod ghost component)) point =
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric (exactGaugePotential period hPeriod ghost)
      point component
  rw [globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace
    period hPeriod frame baseMetric metric (exactGaugePotential period hPeriod ghost) component point]
  simp only [finiteFrameC2AbelianFPExpression, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.sub_apply, finiteFrameScalarC2SecondDerivative_smooth, finiteFrameScalarC2FirstDerivative_smooth,
    finiteFramePotentialCoefficient_exact,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric hVariation]
  rfl

end
end P0EFTJanusFiniteFrameC2AbelianOperators4D
end JanusFormal
