import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameC2LorenzFeature4D

/-! # Joint smoothness of variable-metric Lorenz and FP coefficient expressions

The regular frame is fixed, while the inverse metric and Christoffel
coefficients vary on the existing admissible C² domain. The FP expression
uses the actual ordered second-jet projection, including the frame-change
chain rule. Identification with the intrinsic operators is a separate step.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2LorenzFPFeatures4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
private abbrev MetricC2Core (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod metric

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- The two scalar ghost components retain their own completed second jets. -/
abbrev AbelianGhostC2Core := Fin 2 → CanonicalPhysicalScalarC2JetCore period hPeriod

def variableMetricC2LorenzDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod metric ×ˢ univ

def variableMetricC2FPDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod metric ×ˢ univ

/-- Regular-frame expression `gⁱʲ (Eᵢ Aⱼ − Γᵏᵢⱼ Aₖ)` for one component. -/
def variableMetricC2LorenzComponentExpression
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) (component : Fin 2) :
    C0Scalar period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
      (regularFrameC2FirstDerivative period hPeriod metric first (coefficients second component) -
        ∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first second *
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
              (coefficients upper component))

theorem variableMetricC2LorenzComponentExpression_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        variableMetricC2LorenzComponentExpression period hPeriod metric
          input.1 input.2 component)
      (variableMetricC2LorenzDomain period hPeriod metric) := by
  have hInverse (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          input.1 first second)
      (variableMetricC2LorenzDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn
      period hPeriod metric first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hChristoffel (upper first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        regularGeneralMetricC0Christoffel period hPeriod metric input.1 upper first second)
      (variableMetricC2LorenzDomain period hPeriod metric) :=
    (regularGeneralMetricC0Christoffel_contDiffOn
      period hPeriod metric upper first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hCoefficient (index : Fin 4) : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        input.2 index component) :=
    (gaugeCoefficientC2CoreComponentCLM period hPeriod index component).contDiff.comp
      contDiff_snd
  unfold variableMetricC2LorenzComponentExpression
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  apply (hInverse first second).mul
  apply ((regularFrameC2FirstDerivative_contDiff period hPeriod metric first).comp
    (hCoefficient second)).contDiffOn.sub
  apply ContDiffOn.sum
  intro upper _
  exact (hChristoffel upper first second).mul
    (((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp
      (hCoefficient upper)).contDiffOn)

/-- Regular-frame expression `gⁱʲ (Eᵢ Eⱼ c − Γᵏᵢⱼ Eₖ c)`.
The second derivative is read directly from the existing C² jet. -/
def variableMetricC2FPComponentExpression
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (ghost : AbelianGhostC2Core period hPeriod) (component : Fin 2) :
    C0Scalar period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
      (regularFrameC2SecondDerivative period hPeriod metric first second (ghost component) -
        ∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first second *
            regularFrameC2FirstDerivative period hPeriod metric upper (ghost component))

theorem variableMetricC2FPComponentExpression_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        variableMetricC2FPComponentExpression period hPeriod metric
          input.1 input.2 component)
      (variableMetricC2FPDomain period hPeriod metric) := by
  have hInverse (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          input.1 first second)
      (variableMetricC2FPDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn
      period hPeriod metric first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hChristoffel (upper first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        regularGeneralMetricC0Christoffel period hPeriod metric input.1 upper first second)
      (variableMetricC2FPDomain period hPeriod metric) :=
    (regularGeneralMetricC0Christoffel_contDiffOn
      period hPeriod metric upper first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGhost : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        input.2 component) :=
    (ContinuousLinearMap.proj component : AbelianGhostC2Core period hPeriod →L[Real]
      C2Scalar period hPeriod).contDiff.comp contDiff_snd
  unfold variableMetricC2FPComponentExpression
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  apply (hInverse first second).mul
  apply ((regularFrameC2SecondDerivative_contDiff period hPeriod metric first second).comp
    hGhost).contDiffOn.sub
  apply ContDiffOn.sum
  intro upper _
  exact (hChristoffel upper first second).mul
    (((regularFrameC2FirstDerivative_contDiff period hPeriod metric upper).comp hGhost).contDiffOn)

end
end P0EFTJanusVariableMetricC2LorenzFPFeatures4D
end JanusFormal
