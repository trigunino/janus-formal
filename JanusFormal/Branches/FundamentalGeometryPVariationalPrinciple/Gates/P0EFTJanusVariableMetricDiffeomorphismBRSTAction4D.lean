import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DeDonderFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricCanonicalVolumeRatio4D

/-! # The diffeomorphism BRST action with a variable metric

Metric variation, tensor perturbation, auxiliary vector, antighost, and ghost
are independent coordinates. Both nonminimal vectors have unrestricted
continuous frame coefficients. The genuine moving volume, metric lowering,
De Donder operator, and negative ghost term all remain in the action.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

abbrev DiffeomorphismVectorC0Coefficients := Fin 4 → C0Scalar period hPeriod

/-- Slots are metric variation, tensor perturbation, B, antighost, and ghost. -/
abbrev VariableMetricDiffeomorphismBRSTCore
    (reference : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod reference ×
    (TensorC2Coefficients period hPeriod ×
      (DiffeomorphismVectorC0Coefficients period hPeriod ×
        (DiffeomorphismVectorC0Coefficients period hPeriod ×
          DiffeomorphismGhostC2Coefficients period hPeriod)))

@[implicit_reducible]
def variableMetricDiffeomorphismBRSTCoreCompleteSpace
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace (VariableMetricDiffeomorphismBRSTCore period hPeriod reference) := by
  letI : CompleteSpace (C2Scalar period hPeriod) :=
    canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
  letI : CompleteSpace (RegularGeneralMetricC2Core period hPeriod reference) :=
    generalMetricRelativeC2CoreCompleteSpace period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric
  infer_instance

def variableMetricDiffeomorphismBRSTDomain
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    Set (VariableMetricDiffeomorphismBRSTCore period hPeriod reference) :=
  regularGeneralMetricC2Domain period hPeriod reference ×ˢ univ

theorem variableMetricDiffeomorphismBRSTDomain_isOpen
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) :=
  (regularGeneralMetricC2Domain_isOpen period hPeriod reference).prod isOpen_univ

/-- Canonical density `rho_g ((D_g H)(B) - g(B,B)/2 - (FP_g c)(cbar))`. -/
def variableMetricDiffeomorphismBRSTDensity
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference) :
    C0Scalar period hPeriod :=
  variableMetricCanonicalVolumeRatio period hPeriod reference input.1 *
    ((∑ component : Fin 4,
        variableMetricC2DeDonderComponentExpression period hPeriod reference
          input.1 input.2.1 component * input.2.2.1 component) -
      (1 / 2 : Real) • (∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricC0MetricCoefficient period hPeriod reference input.1 first second *
          input.2.2.1 first * input.2.2.1 second) -
      (∑ component : Fin 4,
        variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
          input.1 input.2.2.2.2 component * input.2.2.2.1 component))

theorem variableMetricDiffeomorphismBRSTDensity_contDiffOn_two
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2 (variableMetricDiffeomorphismBRSTDensity period hPeriod reference)
      (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) := by
  have hDD (component : Fin 4) : ContDiffOn Real ∞
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        variableMetricC2DeDonderComponentExpression period hPeriod reference
          input.1 input.2.1 component)
      (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) := by
    have hProjection : ContDiffOn Real ∞
        (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
          (input.1, input.2.1))
        (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) :=
      (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
    have h := (variableMetricC2DeDonderComponentExpression_contDiffOn period hPeriod
      reference component).comp hProjection (fun _ hInput => ⟨hInput.1, mem_univ _⟩)
    simp only [Function.comp_def] at h
    exact h
  have hFP (component : Fin 4) : ContDiffOn Real ∞
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
          input.1 input.2.2.2.2 component)
      (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) := by
    have hProjection : ContDiffOn Real ∞
        (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
          (input.1, input.2.2.2.2))
        (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) :=
      (contDiff_fst.prodMk contDiff_snd.snd.snd.snd).contDiffOn
    have h := (variableMetricC2DiffeomorphismFPComponentExpression_contDiffOn period hPeriod
      reference component).comp hProjection (fun _ hInput => ⟨hInput.1, mem_univ _⟩)
    simp only [Function.comp_def] at h
    exact h
  have hMetric (first second : Fin 4) : ContDiff Real ∞
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        regularGeneralMetricC0MetricCoefficient period hPeriod reference input.1 first second) :=
    (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod reference
      first second).comp contDiff_fst
  have hB (component : Fin 4) : ContDiff Real ∞
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        input.2.2.1 component) :=
    (contDiff_apply Real (C0Scalar period hPeriod) component).comp contDiff_snd.snd.fst
  have hAntighost (component : Fin 4) : ContDiff Real ∞
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        input.2.2.2.1 component) :=
    (contDiff_apply Real (C0Scalar period hPeriod) component).comp contDiff_snd.snd.snd.fst
  have hVolume : ContDiffOn Real 2
      (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference =>
        variableMetricCanonicalVolumeRatio period hPeriod reference input.1)
      (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) := by
    have hProjection : ContDiffOn Real 2
        (fun input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference => input.1)
        (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) :=
      contDiff_fst.contDiffOn
    have h := (variableMetricCanonicalVolumeRatio_contDiffOn_two period hPeriod reference).comp
      hProjection (fun _ hInput => hInput.1)
    simp only [Function.comp_def] at h
    exact h
  unfold variableMetricDiffeomorphismBRSTDensity
  apply hVolume.mul
  apply ContDiffOn.of_le (n := ∞) _ (by exact WithTop.coe_le_coe.mpr le_top)
  apply ContDiffOn.sub
  · apply ContDiffOn.sub
    · apply ContDiffOn.sum
      intro component _
      exact (hDD component).mul (hB component).contDiffOn
    · apply ContDiffOn.const_smul
      apply ContDiffOn.sum
      intro first _
      apply ContDiffOn.sum
      intro second _
      exact (((hMetric first second).mul (hB first)).mul (hB second)).contDiffOn
  · apply ContDiffOn.sum
    intro component _
    exact (hFP component).mul (hAntighost component).contDiffOn

def variableMetricDiffeomorphismBRSTAction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference) : Real :=
  regularGeneralMetricC0IntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (variableMetricDiffeomorphismBRSTDensity period hPeriod reference input)

theorem variableMetricDiffeomorphismBRSTAction_eq_integral
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference) :
    variableMetricDiffeomorphismBRSTAction period hPeriod reference input =
      ∫ point, variableMetricDiffeomorphismBRSTDensity period hPeriod reference input point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
  regularGeneralMetricC0IntegralCLM_apply period hPeriod _ _

theorem variableMetricDiffeomorphismBRSTAction_contDiffOn_two
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2 (variableMetricDiffeomorphismBRSTAction period hPeriod reference)
      (variableMetricDiffeomorphismBRSTDomain period hPeriod reference) := by
  have h := (regularGeneralMetricC0IntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).contDiff.comp_contDiffOn
      (variableMetricDiffeomorphismBRSTDensity_contDiffOn_two period hPeriod reference)
  simp only [Function.comp_def] at h
  exact h

theorem variableMetricDiffeomorphismBRSTAction_hasFDerivAt
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricDiffeomorphismBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricDiffeomorphismBRSTDomain period hPeriod reference) :
    HasFDerivAt (variableMetricDiffeomorphismBRSTAction period hPeriod reference)
      (fderiv Real (variableMetricDiffeomorphismBRSTAction period hPeriod reference) input) input :=
  ((variableMetricDiffeomorphismBRSTAction_contDiffOn_two period hPeriod reference input
    hInput).contDiffAt
      ((variableMetricDiffeomorphismBRSTDomain_isOpen period hPeriod reference).mem_nhds
        hInput)).differentiableAt (by simp) |>.hasFDerivAt

end
end P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D
end JanusFormal
