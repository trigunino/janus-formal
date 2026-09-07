import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DeDonderFeatures4D

/-! # De Donder depends only on the tensor's first spatial jet

The independent tensor input consists of its continuous values and ordered
first frame derivatives. The metric retains its admissible C² chart.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricDeDonderFirstJet4D

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
open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
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

/-- Slots are `Hᵢⱼ` and `Eₖ Hᵢⱼ`; the derivative index comes first. -/
abbrev TensorC0FirstJet :=
  (Fin 4 → Fin 4 → C0Scalar period hPeriod) ×
    (Fin 4 → Fin 4 → Fin 4 → C0Scalar period hPeriod)

/-- Extract only the tensor values and first reference-frame derivatives. -/
def tensorC2ToC0FirstJetCLM
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    TensorC2Coefficients period hPeriod →L[Real] TensorC0FirstJet period hPeriod :=
  (ContinuousLinearMap.pi (fun first => ContinuousLinearMap.pi (fun second =>
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
      (tensorC2CoefficientCLM period hPeriod first second)))).prod
    (ContinuousLinearMap.pi (fun direction => ContinuousLinearMap.pi (fun first =>
      ContinuousLinearMap.pi (fun second =>
        (regularFrameC2FirstDerivativeCLM period hPeriod metric direction).comp
          (tensorC2CoefficientCLM period hPeriod first second)))))

@[simp] theorem tensorC2ToC0FirstJetCLM_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : TensorC2Coefficients period hPeriod) :
    tensorC2ToC0FirstJetCLM period hPeriod metric tensor =
      ((fun first second =>
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (tensor first second)),
        (fun direction first second =>
          regularFrameC2FirstDerivative period hPeriod metric direction (tensor first second))) := rfl

def variableMetricDeDonderFirstJetDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod metric ×ˢ univ

theorem variableMetricDeDonderFirstJetDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (variableMetricDeDonderFirstJetDomain period hPeriod metric) :=
  (regularGeneralMetricC2Domain_isOpen period hPeriod metric).prod isOpen_univ

/-- Full divergence minus half the differentiated metric trace, on first-jet inputs. -/
def variableMetricDeDonderFirstJetComponentExpression
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC0FirstJet period hPeriod) (component : Fin 4) :
    C0Scalar period hPeriod :=
  (∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
      (tensor.2 first second component -
        (∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first second *
            tensor.1 upper component) -
        (∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric variation upper first component *
            tensor.1 second upper))) -
    (1 / 2 : Real) • (∑ first : Fin 4, ∑ second : Fin 4,
      (regularGeneralMetricC0InverseMetricDerivative period hPeriod metric variation
          component first second * tensor.1 first second +
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation first second *
          tensor.2 component first second))

theorem variableMetricDeDonderFirstJetComponentExpression_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        variableMetricDeDonderFirstJetComponentExpression period hPeriod metric
          input.1 input.2 component)
      (variableMetricDeDonderFirstJetDomain period hPeriod metric) := by
  have hInverse (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric input.1 first second)
      (variableMetricDeDonderFirstJetDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod metric
      first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hInverseDerivative (first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
          input.1 component first second)
      (variableMetricDeDonderFirstJetDomain period hPeriod metric) :=
    (regularGeneralMetricC0InverseMetricDerivative_contDiffOn period hPeriod metric
      component first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hChristoffel (upper first second : Fin 4) : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        regularGeneralMetricC0Christoffel period hPeriod metric input.1 upper first second)
      (variableMetricDeDonderFirstJetDomain period hPeriod metric) :=
    (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
      upper first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hValues : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        input.2.1) := contDiff_fst.comp contDiff_snd
  have hDerivatives : ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        input.2.2) := contDiff_snd.comp contDiff_snd
  have hValue (first second : Fin 4) :=
    contDiff_pi.mp (contDiff_pi.mp hValues first) second
  have hDerivative (direction first second : Fin 4) :=
    contDiff_pi.mp (contDiff_pi.mp (contDiff_pi.mp hDerivatives direction) first) second
  unfold variableMetricDeDonderFirstJetComponentExpression
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

/-- Gate 652: the previous completed expression factors exactly through the bounded first jet. -/
theorem variableMetricC2DeDonderComponentExpression_eq_firstJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC2Coefficients period hPeriod) (component : Fin 4) :
    variableMetricC2DeDonderComponentExpression period hPeriod metric variation tensor component =
      variableMetricDeDonderFirstJetComponentExpression period hPeriod metric variation
        (tensorC2ToC0FirstJetCLM period hPeriod metric tensor) component := rfl

def variableMetricDeDonderFirstJetComponentL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC0FirstJet period hPeriod) (component : Fin 4) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  continuousToCanonicalPhysicalBulkL2 period hPeriod
    (variableMetricDeDonderFirstJetComponentExpression period hPeriod metric
      variation tensor component)

theorem variableMetricDeDonderFirstJetComponentL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × TensorC0FirstJet period hPeriod =>
        variableMetricDeDonderFirstJetComponentL2 period hPeriod metric input.1 input.2 component)
      (variableMetricDeDonderFirstJetDomain period hPeriod metric) := by
  have h := (continuousToCanonicalPhysicalBulkL2 period hPeriod).contDiff.comp_contDiffOn
    (variableMetricDeDonderFirstJetComponentExpression_contDiffOn period hPeriod metric component)
  exact h

theorem variableMetricC2DeDonderComponentL2_eq_firstJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (tensor : TensorC2Coefficients period hPeriod) (component : Fin 4) :
    variableMetricC2DeDonderComponentL2 period hPeriod metric variation tensor component =
      variableMetricDeDonderFirstJetComponentL2 period hPeriod metric variation
        (tensorC2ToC0FirstJetCLM period hPeriod metric tensor) component := rfl

end
end P0EFTJanusVariableMetricDeDonderFirstJet4D
end JanusFormal
