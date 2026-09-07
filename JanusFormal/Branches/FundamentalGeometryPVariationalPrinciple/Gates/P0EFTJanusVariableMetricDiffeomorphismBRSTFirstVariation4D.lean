import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D

/-! # Explicit first variation of the mobile diffeomorphism BRST action

The volume and each operator feature are differentiated on the full independent
metric/tensor/B/antighost/ghost core. Product rules retain the moving volume,
metric lowering, both auxiliary-vector variations, and both ghost-pair terms.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricDiffeomorphismBRSTFirstVariation4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (reference : RegularGeneralLorentzMetric period hPeriod)
local notation "Core" => VariableMetricDiffeomorphismBRSTCore period hPeriod reference
local notation "Domain" => variableMetricDiffeomorphismBRSTDomain period hPeriod reference

private theorem deDonderFeature_differentiableAt
    (component : Fin 4) (input : Core) (hInput : input ∈ Domain) :
    DifferentiableAt Real (fun value : Core =>
      variableMetricC2DeDonderComponentExpression period hPeriod reference
        value.1 value.2.1 component) input := by
  have hProjection : ContDiffOn Real ∞
      (fun value : Core => (value.1, value.2.1)) Domain :=
    (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
  have h := (variableMetricC2DeDonderComponentExpression_contDiffOn period hPeriod
    reference component).comp hProjection (fun _ hValue => ⟨hValue.1, mem_univ _⟩)
  simp only [Function.comp_def] at h
  exact ((h input hInput).contDiffAt
    ((variableMetricDiffeomorphismBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)).differentiableAt
      (by simp)

private theorem fpFeature_differentiableAt
    (component : Fin 4) (input : Core) (hInput : input ∈ Domain) :
    DifferentiableAt Real (fun value : Core =>
      variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
        value.1 value.2.2.2.2 component) input := by
  have hProjection : ContDiffOn Real ∞
      (fun value : Core => (value.1, value.2.2.2.2)) Domain :=
    (contDiff_fst.prodMk contDiff_snd.snd.snd.snd).contDiffOn
  have h := (variableMetricC2DiffeomorphismFPComponentExpression_contDiffOn period hPeriod
    reference component).comp hProjection (fun _ hValue => ⟨hValue.1, mem_univ _⟩)
  simp only [Function.comp_def] at h
  exact ((h input hInput).contDiffAt
    ((variableMetricDiffeomorphismBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)).differentiableAt
      (by simp)

private theorem volumeFeature_differentiableAt
    (input : Core) (hInput : input ∈ Domain) :
    DifferentiableAt Real (fun value : Core =>
      variableMetricCanonicalVolumeRatio period hPeriod reference value.1) input := by
  have hProjection : ContDiffOn Real 2 (fun value : Core => value.1) Domain :=
    contDiff_fst.contDiffOn
  have h := (variableMetricCanonicalVolumeRatio_contDiffOn_two period hPeriod reference).comp
    hProjection (fun _ hValue => hValue.1)
  simp only [Function.comp_def] at h
  exact ((h input hInput).contDiffAt
    ((variableMetricDiffeomorphismBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)).differentiableAt
      (by simp)

/-- The full product-rule density. Feature derivatives include every metric and field slot. -/
def variableMetricDiffeomorphismBRSTFirstVariationDensity (input direction : Core) :
    C0Scalar period hPeriod :=
  let rho := fun value : Core => variableMetricCanonicalVolumeRatio period hPeriod reference value.1
  let dd := fun component (value : Core) =>
    variableMetricC2DeDonderComponentExpression period hPeriod reference value.1 value.2.1 component
  let g := fun first second (value : Core) =>
    regularGeneralMetricC0MetricCoefficient period hPeriod reference value.1 first second
  let fp := fun component (value : Core) =>
    variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
      value.1 value.2.2.2.2 component
  let q := (∑ component : Fin 4, dd component input * input.2.2.1 component) -
    (1 / 2 : Real) • (∑ first : Fin 4, ∑ second : Fin 4,
      g first second input * input.2.2.1 first * input.2.2.1 second) -
    (∑ component : Fin 4, fp component input * input.2.2.2.1 component)
  (fderiv Real rho input direction) * q + rho input *
    ((∑ component : Fin 4,
        (fderiv Real (dd component) input direction * input.2.2.1 component +
          dd component input * direction.2.2.1 component)) -
      (1 / 2 : Real) • (∑ first : Fin 4, ∑ second : Fin 4,
        (fderiv Real (g first second) input direction * input.2.2.1 first * input.2.2.1 second +
          g first second input * direction.2.2.1 first * input.2.2.1 second +
          g first second input * input.2.2.1 first * direction.2.2.1 second)) -
      (∑ component : Fin 4,
        (fderiv Real (fp component) input direction * input.2.2.2.1 component +
          fp component input * direction.2.2.2.1 component)))

private theorem finiteDensityProductRule
    (rho dRho : C0Scalar period hPeriod)
    (dd dDD B dB fp dFP antighost dAntighost : Fin 4 → C0Scalar period hPeriod)
    (g dg : Fin 4 → Fin 4 → C0Scalar period hPeriod) :
    rho *
        ((∑ i : Fin 4, (dd i * dB i + B i * dDD i)) -
          (1 / 2 : Real) • (∑ i : Fin 4, ∑ j : Fin 4,
            (g i j * B i * dB j + B j * (g i j * dB i + B i * dg i j))) -
          (∑ i : Fin 4, (fp i * dAntighost i + antighost i * dFP i))) +
      ((∑ i : Fin 4, dd i * B i) -
        (1 / 2 : Real) • (∑ i : Fin 4, ∑ j : Fin 4, g i j * B i * B j) -
        (∑ i : Fin 4, fp i * antighost i)) * dRho =
    dRho * ((∑ i : Fin 4, dd i * B i) -
        (1 / 2 : Real) • (∑ i : Fin 4, ∑ j : Fin 4, g i j * B i * B j) -
        (∑ i : Fin 4, fp i * antighost i)) +
      rho * ((∑ i : Fin 4, (dDD i * B i + dd i * dB i)) -
        (1 / 2 : Real) • (∑ i : Fin 4, ∑ j : Fin 4,
          (dg i j * B i * B j + g i j * dB i * B j + g i j * B i * dB j)) -
        (∑ i : Fin 4, (dFP i * antighost i + fp i * dAntighost i))) := by
  have hPair : (∑ i : Fin 4, (dd i * dB i + B i * dDD i)) =
      ∑ i : Fin 4, (dDD i * B i + dd i * dB i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hMass : (∑ i : Fin 4, ∑ j : Fin 4,
      (g i j * B i * dB j + B j * (g i j * dB i + B i * dg i j))) =
      ∑ i : Fin 4, ∑ j : Fin 4,
        (dg i j * B i * B j + g i j * dB i * B j + g i j * B i * dB j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hGhost : (∑ i : Fin 4, (fp i * dAntighost i + antighost i * dFP i)) =
      ∑ i : Fin 4, (dFP i * antighost i + fp i * dAntighost i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hPair, hMass, hGhost]
  ring

/-- Differentiating the actual density gives the explicit finite product rule. -/
theorem variableMetricDiffeomorphismBRSTDensity_fderiv_apply
    (input : Core) (hInput : input ∈ Domain) (direction : Core) :
    fderiv Real (variableMetricDiffeomorphismBRSTDensity period hPeriod reference)
        input direction =
      variableMetricDiffeomorphismBRSTFirstVariationDensity period hPeriod reference
        input direction := by
  let B : Fin 4 → Core →L[Real] C0Scalar period hPeriod := fun component =>
    (ContinuousLinearMap.proj component).comp
      ((ContinuousLinearMap.fst Real _ _).comp
        ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _)))
  let antighost : Fin 4 → Core →L[Real] C0Scalar period hPeriod := fun component =>
    (ContinuousLinearMap.proj component).comp
      ((ContinuousLinearMap.fst Real _ _).comp
        ((ContinuousLinearMap.snd Real _ _).comp
          ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))))
  have hDD (component : Fin 4) :=
    (deDonderFeature_differentiableAt period hPeriod reference component input hInput).hasFDerivAt
  have hFP (component : Fin 4) :=
    (fpFeature_differentiableAt period hPeriod reference component input hInput).hasFDerivAt
  have hMetric (first second : Fin 4) : DifferentiableAt Real
      (fun value : Core => regularGeneralMetricC0MetricCoefficient period hPeriod reference
        value.1 first second) input :=
    ((regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod reference
      first second).differentiable (by simp) input.1).comp input differentiableAt_fst
  have hPair := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun component (_ : component ∈ (Finset.univ : Finset (Fin 4))) =>
      (hDD component).mul (B component).hasFDerivAt)
  have hMass := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun first (_ : first ∈ (Finset.univ : Finset (Fin 4))) =>
      HasFDerivAt.fun_sum (u := Finset.univ)
        (fun second (_ : second ∈ (Finset.univ : Finset (Fin 4))) =>
          (((hMetric first second).hasFDerivAt.mul (B first).hasFDerivAt).mul
            (B second).hasFDerivAt)))
  have hGhost := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun component (_ : component ∈ (Finset.univ : Finset (Fin 4))) =>
      (hFP component).mul (antighost component).hasFDerivAt)
  have hDensity :=
    (volumeFeature_differentiableAt period hPeriod reference input hInput).hasFDerivAt.mul
      ((hPair.sub (hMass.const_smul (1 / 2 : Real))).sub hGhost)
  change HasFDerivAt (variableMetricDiffeomorphismBRSTDensity period hPeriod reference)
    _ input at hDensity
  rw [hDensity.fderiv]
  simp only [variableMetricDiffeomorphismBRSTFirstVariationDensity,
    add_apply, sub_apply, sum_apply, smul_apply,
    smul_eq_mul, B, antighost, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply]
  exact finiteDensityProductRule period hPeriod _ _ _ _ _ _ _ _ _ _ _ _

/-- Canonical integration of the density derivative is a continuous linear Euler operator. -/
def variableMetricDiffeomorphismBRSTExplicitEulerOperator (input : Core) : Core →L[Real] Real :=
  (regularGeneralMetricC0IntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).comp
      (fderiv Real (variableMetricDiffeomorphismBRSTDensity period hPeriod reference) input)

theorem variableMetricDiffeomorphismBRSTAction_hasFDerivAt_explicit
    (input : Core) (hInput : input ∈ Domain) :
    HasFDerivAt (variableMetricDiffeomorphismBRSTAction period hPeriod reference)
      (variableMetricDiffeomorphismBRSTExplicitEulerOperator period hPeriod reference input) input := by
  have hDensity :=
    ((variableMetricDiffeomorphismBRSTDensity_contDiffOn_two period hPeriod reference
      input hInput).contDiffAt
        ((variableMetricDiffeomorphismBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)).differentiableAt
      (by simp)
  have h := (regularGeneralMetricC0IntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).hasFDerivAt.comp input
      hDensity.hasFDerivAt
  simp only [Function.comp_def] at h
  exact h

theorem variableMetricDiffeomorphismBRSTExplicitEulerOperator_apply
    (input : Core) (hInput : input ∈ Domain) (direction : Core) :
    variableMetricDiffeomorphismBRSTExplicitEulerOperator period hPeriod reference input direction =
      ∫ point, variableMetricDiffeomorphismBRSTFirstVariationDensity period hPeriod reference
        input direction point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [variableMetricDiffeomorphismBRSTExplicitEulerOperator, ContinuousLinearMap.comp_apply,
    variableMetricDiffeomorphismBRSTDensity_fderiv_apply period hPeriod reference input hInput]
  exact regularGeneralMetricC0IntegralCLM_apply period hPeriod _ _

/-- The actual action derivative is the canonical integral of all explicit variation terms. -/
theorem variableMetricDiffeomorphismBRSTAction_fderiv_apply
    (input : Core) (hInput : input ∈ Domain) (direction : Core) :
    fderiv Real (variableMetricDiffeomorphismBRSTAction period hPeriod reference) input direction =
      ∫ point, variableMetricDiffeomorphismBRSTFirstVariationDensity period hPeriod reference
        input direction point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [(variableMetricDiffeomorphismBRSTAction_hasFDerivAt_explicit period hPeriod reference
    input hInput).fderiv]
  exact variableMetricDiffeomorphismBRSTExplicitEulerOperator_apply period hPeriod reference
    input hInput direction

end
end P0EFTJanusVariableMetricDiffeomorphismBRSTFirstVariation4D
end JanusFormal
