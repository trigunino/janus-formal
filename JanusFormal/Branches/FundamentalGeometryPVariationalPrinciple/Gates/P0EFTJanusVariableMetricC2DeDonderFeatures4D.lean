import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2LorenzFPFeatures4D

/-!
# Variable-metric De Donder coefficients on the completed C² tensor domain

The metric varies on its admissible open chart. The independent tensor has
sixteen unrestricted C² coefficients in the fixed reference frame. Its
covariant divergence and differentiated metric trace give the De Donder
expression. Intrinsic smooth agreement is a separate step.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2DeDonderFeatures4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
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

/-- Independent completed coefficients; no metric admissibility condition is imposed on them. -/
abbrev TensorC2Coefficients := Fin 4 → Fin 4 → CanonicalPhysicalScalarC2JetCore period hPeriod

def tensorC2CoefficientCLM (first second : Fin 4) :
    TensorC2Coefficients period hPeriod →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj second :
    (Fin 4 → C2Scalar period hPeriod) →L[Real] C2Scalar period hPeriod).comp
    (ContinuousLinearMap.proj first : TensorC2Coefficients period hPeriod →L[Real]
      (Fin 4 → C2Scalar period hPeriod))

def variableMetricC2DeDonderDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod metric ×ˢ univ

/-- `gⁱʲ ∇ᵢ Hⱼₐ − (1/2) Eₐ(gⁱʲ Hᵢⱼ)`, including the inverse-metric derivative. -/
def variableMetricC2DeDonderComponentExpression
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC2Coefficients period hPeriod) (component : Fin 4) :
    C0Scalar period hPeriod :=
  (∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
      (regularFrameC2FirstDerivative period hPeriod metric first (tensor second component) -
        (∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first second *
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (tensor upper component)) -
        (∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first component *
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (tensor second upper)))) -
    (1 / 2 : Real) • (∑ first : Fin 4, ∑ second : Fin 4,
      (regularGeneralMetricC0InverseMetricDerivative period hPeriod metric variation
          component first second *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (tensor first second) +
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
        regularFrameC2FirstDerivative period hPeriod metric component (tensor first second)))

theorem variableMetricC2DeDonderComponentExpression_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        variableMetricC2DeDonderComponentExpression period hPeriod metric
          input.1 input.2 component)
      (variableMetricC2DeDonderDomain period hPeriod metric) := by
  have hInverse (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          input.1 first second)
      (variableMetricC2DeDonderDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod metric
      first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hInverseDerivative (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
          input.1 component first second)
      (variableMetricC2DeDonderDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricDerivative_contDiffOn period hPeriod metric
      component first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hChristoffel (upper first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        regularGeneralMetricC0Christoffel period hPeriod metric input.1 upper first second)
      (variableMetricC2DeDonderDomain period hPeriod metric) :=
    (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
      upper first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hCoefficient (first second : Fin 4) : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        input.2 first second) :=
    (tensorC2CoefficientCLM period hPeriod first second).contDiff.comp contDiff_snd
  have hValue (first second : Fin 4) : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (input.2 first second)) :=
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp
      (hCoefficient first second)
  have hDerivative (direction first second : Fin 4) : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        regularFrameC2FirstDerivative period hPeriod metric direction (input.2 first second)) :=
    (regularFrameC2FirstDerivative_contDiff period hPeriod metric direction).comp
      (hCoefficient first second)
  unfold variableMetricC2DeDonderComponentExpression
  apply ContDiffOn.sub
  · apply ContDiffOn.sum
    intro first _
    apply ContDiffOn.sum
    intro second _
    apply (hInverse first second).mul
    apply ContDiffOn.sub
    · apply (hDerivative first second component).contDiffOn.sub
      apply ContDiffOn.sum
      intro upper _
      exact (hChristoffel upper first second).mul (hValue upper component).contDiffOn
    · apply ContDiffOn.sum
      intro upper _
      exact (hChristoffel upper first component).mul (hValue second upper).contDiffOn
  · apply ContDiffOn.const_smul
    apply ContDiffOn.sum
    intro first _
    apply ContDiffOn.sum
    intro second _
    exact ((hInverseDerivative first second).mul (hValue first second).contDiffOn).add
      ((hInverse first second).mul (hDerivative component first second).contDiffOn)

def variableMetricC2DeDonderComponentL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC2Coefficients period hPeriod) (component : Fin 4) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  continuousToCanonicalPhysicalBulkL2 period hPeriod
    (variableMetricC2DeDonderComponentExpression period hPeriod metric variation tensor component)

theorem variableMetricC2DeDonderComponentL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        variableMetricC2DeDonderComponentL2 period hPeriod metric input.1 input.2 component)
      (variableMetricC2DeDonderDomain period hPeriod metric) := by
  have h := (continuousToCanonicalPhysicalBulkL2 period hPeriod).contDiff.comp_contDiffOn
    (variableMetricC2DeDonderComponentExpression_contDiffOn period hPeriod metric component)
  exact h

def variableMetricC2DeDonderL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC2Coefficients period hPeriod) :
    Fin 4 → CanonicalPhysicalBulkL2 period hPeriod :=
  variableMetricC2DeDonderComponentL2 period hPeriod metric variation tensor

theorem variableMetricC2DeDonderL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC2Coefficients period hPeriod =>
        variableMetricC2DeDonderL2 period hPeriod metric input.1 input.2)
      (variableMetricC2DeDonderDomain period hPeriod metric) :=
  contDiffOn_pi.mpr (variableMetricC2DeDonderComponentL2_contDiffOn period hPeriod metric)

end
end P0EFTJanusVariableMetricC2DeDonderFeatures4D
end JanusFormal
