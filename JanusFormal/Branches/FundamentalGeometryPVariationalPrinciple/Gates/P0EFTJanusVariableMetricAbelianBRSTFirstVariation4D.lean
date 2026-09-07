import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricAbelianBRSTAction4D

/-! # First variation of the variable-metric Abelian BRST action

The Euler covector has five explicit terms.  Both feature derivatives act
on the full input direction: metric/potential for Lorenz and metric/ghost
for Faddeev--Popov.  The metric is not held fixed in either derivative.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricAbelianBRSTFirstVariation4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D
open P0EFTJanusVariableMetricC2LorenzFPL2Features4D
open P0EFTJanusVariableMetricAbelianBRSTAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev ScalarL2 := CanonicalPhysicalBulkL2 period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (reference : RegularGeneralLorentzMetric period hPeriod)

private def bProjection (component : Fin 2) :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real]
      ScalarL2 period hPeriod where
  toFun input := input.2.2.1 component
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply component).comp continuous_snd.snd.fst

private def antighostProjection (component : Fin 2) :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real]
      ScalarL2 period hPeriod where
  toFun input := input.2.2.2.1 component
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply component).comp continuous_snd.snd.snd.fst

private def metricGaugeProjection :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real]
      (RegularGeneralMetricC2Core period hPeriod reference ×
        RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) where
  toFun input := (input.1, input.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk continuous_snd.fst

private def metricGhostProjection :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real]
      (RegularGeneralMetricC2Core period hPeriod reference ×
        AbelianGhostC2Core period hPeriod) where
  toFun input := (input.1, input.2.2.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk continuous_snd.snd.snd.snd

/-- The Lorenz derivative retains both metric and potential directions. -/
theorem variableMetricAbelianLorenzFeature_fderiv_apply
    (component : Fin 2)
    (input direction : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
        input direction =
      fderiv Real
        (fun state : RegularGeneralMetricC2Core period hPeriod reference ×
            RegularGeneralMetricC2GaugeCoefficientCore period hPeriod =>
          variableMetricC2LorenzComponentL2 period hPeriod reference state.1 state.2 component)
        (input.1, input.2.1) (direction.1, direction.2.1) := by
  have hOpen : IsOpen (variableMetricC2LorenzDomain period hPeriod reference) :=
    (regularGeneralMetricC2Domain_isOpen period hPeriod reference).prod isOpen_univ
  have hSmooth :=
    (variableMetricC2LorenzComponentL2_contDiffOn period hPeriod reference component
      (input.1, input.2.1) ⟨hInput.1, Set.mem_univ _⟩).contDiffAt
        (hOpen.mem_nhds ⟨hInput.1, Set.mem_univ _⟩)
  have hDerivative := ((hSmooth.differentiableAt (by simp)).hasFDerivAt).comp
    input (metricGaugeProjection period hPeriod reference).hasFDerivAt
  exact congrArg (fun derivative => derivative direction) hDerivative.fderiv

/-- The FP derivative retains both metric and ghost directions. -/
theorem variableMetricAbelianFPFeature_fderiv_apply
    (component : Fin 2)
    (input direction : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
        input direction =
      fderiv Real
        (fun state : RegularGeneralMetricC2Core period hPeriod reference ×
            AbelianGhostC2Core period hPeriod =>
          variableMetricC2FPComponentL2 period hPeriod reference state.1 state.2 component)
        (input.1, input.2.2.2.2) (direction.1, direction.2.2.2.2) := by
  have hOpen : IsOpen (variableMetricC2FPDomain period hPeriod reference) :=
    (regularGeneralMetricC2Domain_isOpen period hPeriod reference).prod isOpen_univ
  have hSmooth :=
    (variableMetricC2FPComponentL2_contDiffOn period hPeriod reference component
      (input.1, input.2.2.2.2) ⟨hInput.1, Set.mem_univ _⟩).contDiffAt
        (hOpen.mem_nhds ⟨hInput.1, Set.mem_univ _⟩)
  have hDerivative := ((hSmooth.differentiableAt (by simp)).hasFDerivAt).comp
    input (metricGhostProjection period hPeriod reference).hasFDerivAt
  exact congrArg (fun derivative => derivative direction) hDerivative.fderiv

private def eulerComponent
    (component : Fin 2)
    (input : VariableMetricAbelianBRSTCore period hPeriod reference) :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real] Real :=
  (innerSL Real (variableMetricAbelianLorenzFeature period hPeriod reference component input)).comp
      (bProjection period hPeriod reference component) +
    (innerSL Real (input.2.2.1 component)).comp
      (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component) input) -
    (innerSL Real (input.2.2.1 component)).comp
      (bProjection period hPeriod reference component) +
    (innerSL Real (variableMetricAbelianFPFeature period hPeriod reference component input)).comp
      (antighostProjection period hPeriod reference component) +
    (innerSL Real (input.2.2.2.1 component)).comp
      (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component) input)

private theorem eulerComponent_apply
    (component : Fin 2)
    (input direction : VariableMetricAbelianBRSTCore period hPeriod reference) :
    eulerComponent period hPeriod reference component input direction =
      inner Real (direction.2.2.1 component)
          (variableMetricAbelianLorenzFeature period hPeriod reference component input) +
        inner Real (input.2.2.1 component)
          (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
            input direction) -
        inner Real (input.2.2.1 component) (direction.2.2.1 component) +
        inner Real (direction.2.2.2.1 component)
          (variableMetricAbelianFPFeature period hPeriod reference component input) +
        inner Real (input.2.2.2.1 component)
          (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
            input direction) := by
  change inner Real
      (variableMetricAbelianLorenzFeature period hPeriod reference component input)
      (direction.2.2.1 component) + _ - _ +
        inner Real (variableMetricAbelianFPFeature period hPeriod reference component input)
          (direction.2.2.2.1 component) + _ = _
  rw [real_inner_comm
      (variableMetricAbelianLorenzFeature period hPeriod reference component input)
      (direction.2.2.1 component),
    real_inner_comm
      (variableMetricAbelianFPFeature period hPeriod reference component input)
      (direction.2.2.2.1 component)]
  rfl

/-- The actual continuous Euler covector with both variable-metric contributions. -/
def variableMetricAbelianBRSTEulerOperator
    (input : VariableMetricAbelianBRSTCore period hPeriod reference) :
    VariableMetricAbelianBRSTCore period hPeriod reference →L[Real] Real :=
  ∑ component : Fin 2, eulerComponent period hPeriod reference component input

/-- Explicit five-term first variation, including the full Lorenz and FP derivatives. -/
theorem variableMetricAbelianBRSTEulerOperator_apply
    (input direction : VariableMetricAbelianBRSTCore period hPeriod reference) :
    variableMetricAbelianBRSTEulerOperator period hPeriod reference input direction =
      ∑ component : Fin 2,
        (inner Real (direction.2.2.1 component)
            (variableMetricAbelianLorenzFeature period hPeriod reference component input) +
          inner Real (input.2.2.1 component)
            (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
              input direction) -
          inner Real (input.2.2.1 component) (direction.2.2.1 component) +
          inner Real (direction.2.2.2.1 component)
            (variableMetricAbelianFPFeature period hPeriod reference component input) +
          inner Real (input.2.2.2.1 component)
            (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
              input direction)) := by
  simp only [variableMetricAbelianBRSTEulerOperator, sum_apply,
    eulerComponent_apply]

/-- Differentiation of the genuine three-term action gives the five-term Euler covector. -/
theorem variableMetricAbelianBRSTAction_hasFDerivAt_euler
    (input : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    HasFDerivAt (variableMetricAbelianBRSTAction period hPeriod reference)
      (variableMetricAbelianBRSTEulerOperator period hPeriod reference input) input := by
  have hLorenz (component : Fin 2) :=
    ((variableMetricAbelianLorenzFeature_contDiffOn period hPeriod reference component
      input hInput).contDiffAt
      ((variableMetricAbelianBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)
        ).differentiableAt (by simp) |>.hasFDerivAt
  have hFP (component : Fin 2) :=
    ((variableMetricAbelianFPFeature_contDiffOn period hPeriod reference component
      input hInput).contDiffAt
      ((variableMetricAbelianBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)
        ).differentiableAt (by simp) |>.hasFDerivAt
  unfold variableMetricAbelianBRSTAction variableMetricAbelianBRSTEulerOperator
  apply HasFDerivAt.fun_sum
  intro component _
  have hB := (bProjection period hPeriod reference component).hasFDerivAt (x := input)
  have hAntighost :=
    (antighostProjection period hPeriod reference component).hasFDerivAt (x := input)
  have hRaw := ((hB.inner Real (hLorenz component)).sub
      ((hB.inner Real hB).const_mul (1 / 2 : Real))).add
    (hAntighost.inner Real (hFP component))
  apply hRaw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  rw [eulerComponent_apply]
  change
    (inner Real (input.2.2.1 component)
        (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
          input direction) +
      inner Real (direction.2.2.1 component)
        (variableMetricAbelianLorenzFeature period hPeriod reference component input)) -
      (1 / 2 : Real) *
        (inner Real (input.2.2.1 component) (direction.2.2.1 component) +
          inner Real (direction.2.2.1 component) (input.2.2.1 component)) +
      (inner Real (input.2.2.2.1 component)
        (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
          input direction) +
        inner Real (direction.2.2.2.1 component)
          (variableMetricAbelianFPFeature period hPeriod reference component input)) = _
  rw [real_inner_comm (direction.2.2.1 component) (input.2.2.1 component)]
  ring

theorem variableMetricAbelianBRSTAction_fderiv_eq_euler
    (input : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    fderiv Real (variableMetricAbelianBRSTAction period hPeriod reference) input =
      variableMetricAbelianBRSTEulerOperator period hPeriod reference input :=
  (variableMetricAbelianBRSTAction_hasFDerivAt_euler period hPeriod
    reference input hInput).fderiv

/-- The action derivative evaluated on an arbitrary full direction. -/
theorem variableMetricAbelianBRSTAction_fderiv_apply
    (input direction : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    fderiv Real (variableMetricAbelianBRSTAction period hPeriod reference) input direction =
      ∑ component : Fin 2,
        (inner Real (direction.2.2.1 component)
            (variableMetricAbelianLorenzFeature period hPeriod reference component input) +
          inner Real (input.2.2.1 component)
            (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
              input direction) -
          inner Real (input.2.2.1 component) (direction.2.2.1 component) +
          inner Real (direction.2.2.2.1 component)
            (variableMetricAbelianFPFeature period hPeriod reference component input) +
          inner Real (input.2.2.2.1 component)
            (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
              input direction)) := by
  rw [variableMetricAbelianBRSTAction_fderiv_eq_euler period hPeriod reference input hInput]
  exact variableMetricAbelianBRSTEulerOperator_apply period hPeriod reference input direction

/-- Pure metric variation still differentiates both physical features. -/
theorem variableMetricAbelianBRSTEulerOperator_metric_apply
    (input : VariableMetricAbelianBRSTCore period hPeriod reference)
    (metricDirection : RegularGeneralMetricC2Core period hPeriod reference) :
    variableMetricAbelianBRSTEulerOperator period hPeriod reference input (metricDirection, 0) =
      ∑ component : Fin 2,
        (inner Real (input.2.2.1 component)
          (fderiv Real (variableMetricAbelianLorenzFeature period hPeriod reference component)
            input (metricDirection, 0)) +
        inner Real (input.2.2.2.1 component)
          (fderiv Real (variableMetricAbelianFPFeature period hPeriod reference component)
            input (metricDirection, 0))) := by
  rw [variableMetricAbelianBRSTEulerOperator_apply]
  simp

/-- Gate 642: the explicit Euler covector is the genuine action derivative. -/
theorem variable_metric_abelian_BRST_first_variation_gate
    (input : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    HasFDerivAt (variableMetricAbelianBRSTAction period hPeriod reference)
      (variableMetricAbelianBRSTEulerOperator period hPeriod reference input) input :=
  variableMetricAbelianBRSTAction_hasFDerivAt_euler period hPeriod reference input hInput

end
end P0EFTJanusVariableMetricAbelianBRSTFirstVariation4D
end JanusFormal
