import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D

/-!
# Intrinsic Abelian directions inside the corrected global tangent

A regular Candidate-A frame evaluates every intrinsic Abelian one-form into
the existing `GaugeFiber` coefficient packet.  The resulting map is smooth,
linear and injective because the supplied frame is a basis at every point.

This gate only installs that faithful direction.  It does not assert a
smooth inverse from arbitrary coefficient fields: the present regular metric
API supplies a pointwise inverse frame but no smooth global coframe section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Coefficients of one intrinsic potential on a supplied regular frame. -/
def gaugePotentialFrameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm
      (fun index =>
        potential.toFun index.2 point (metric.frame index.1 point))
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact (potential.contMDiff_eval index.2).comp
      (metric.frame index.1).contMDiff

@[simp]
theorem gaugePotentialFrameCoefficients_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) (component : Fin 2) :
    gaugePotentialFrameCoefficients period hPeriod metric potential point
        (index, component) =
      potential.toFun component point (metric.frame index point) :=
  by
    rfl

/-- Frame evaluation is real-linear in the intrinsic potential. -/
def gaugePotentialFrameCoefficientsLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeFiber where
  toFun := gaugePotentialFrameCoefficients period hPeriod metric
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod GaugeFiber
    intro point
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
    funext index
    rfl
  map_smul' scalar potential := by
    apply SmoothQuotientField.ext period hPeriod GaugeFiber
    intro point
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
    funext index
    rfl

private theorem regularMetricFrameEquiv_basisFun
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) :
    metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index) =
      metric.frame index point := by
  exact (metric.frame_eq_basisFun period hPeriod point index).symm

/-- A regular frame reads every intrinsic one-form faithfully. -/
theorem gaugePotentialFrameCoefficientsLinearMap_injective
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric) := by
  intro first second hCoefficients
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  let firstMap : (Fin 4 → Real) →ₗ[Real] Real :=
    (first.toFun component point).toLinearMap.comp
      (metric.frameEquiv point).toLinearEquiv.toLinearMap
  let secondMap : (Fin 4 → Real) →ₗ[Real] Real :=
    (second.toFun component point).toLinearMap.comp
      (metric.frameEquiv point).toLinearEquiv.toLinearMap
  have hMaps : firstMap = secondMap := by
    apply (Pi.basisFun Real (Fin 4)).ext
    intro index
    have hFrame :
        metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index) =
          metric.frame index point := by
      exact regularMetricFrameEquiv_basisFun
        period hPeriod metric point index
    have hCoefficient := congrArg
      (fun field : SmoothQuotientField period hPeriod GaugeFiber =>
        field point (index, component)) hCoefficients
    change first.toFun component point (metric.frame index point) =
      second.toFun component point (metric.frame index point) at hCoefficient
    change
      first.toFun component point
          (metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index)) =
        second.toFun component point
          (metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index))
    rw [hFrame]
    exact hCoefficient
  have hApply := LinearMap.congr_fun hMaps
    ((metric.frameEquiv point).symm tangent)
  simpa [firstMap, secondMap] using hApply

/-- Candidate-A frame evaluation in both physical outer sectors. -/
def globalCandidateAPairedGaugePotentialCoefficientLinearMap
    {configuration : P0EFTJanusProgramPGlobalFieldSpace4D.GlobalFieldConfiguration
      period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    (Sector → SmoothAbelianGaugePotential period hPeriod) →ₗ[Real]
      GaugeVariationPair period hPeriod where
  toFun := fun potential =>
    (gaugePotentialFrameCoefficients period hPeriod
        data.plusGravity.metric (potential .plus),
      gaugePotentialFrameCoefficients period hPeriod
        data.minusGravity.metric (potential .minus))
  map_add' first second := by
    apply Prod.ext
    · exact (gaugePotentialFrameCoefficientsLinearMap period hPeriod
        data.plusGravity.metric).map_add (first .plus) (second .plus)
    · exact (gaugePotentialFrameCoefficientsLinearMap period hPeriod
        data.minusGravity.metric).map_add (first .minus) (second .minus)
  map_smul' scalar potential := by
    apply Prod.ext
    · exact (gaugePotentialFrameCoefficientsLinearMap period hPeriod
        data.plusGravity.metric).map_smul scalar (potential .plus)
    · exact (gaugePotentialFrameCoefficientsLinearMap period hPeriod
        data.minusGravity.metric).map_smul scalar (potential .minus)

/-- The paired Candidate-A coefficient reading remains injective. -/
theorem globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
    {configuration : P0EFTJanusProgramPGlobalFieldSpace4D.GlobalFieldConfiguration
      period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Function.Injective
      (globalCandidateAPairedGaugePotentialCoefficientLinearMap
        period hPeriod data) := by
  intro first second hCoefficients
  funext sector
  cases sector with
  | plus =>
      exact gaugePotentialFrameCoefficientsLinearMap_injective
        period hPeriod data.plusGravity.metric
        (congrArg Prod.fst hCoefficients)
  | minus =>
      exact gaugePotentialFrameCoefficientsLinearMap_injective
        period hPeriod data.minusGravity.metric
        (congrArg Prod.snd hCoefficients)

/-- Insert a coefficient gauge pair into the common independent variation,
with every unrelated direction fixed. -/
def gaugeVariationPairIndependentLinearMap :
    GaugeVariationPair period hPeriod →ₗ[Real]
      IndependentFieldVariation period hPeriod where
  toFun := gaugeOnlyIndependentVariation period hPeriod
  map_add' first second := by
    apply IndependentFieldVariation.ext
    · change zeroSmoothDiagonalMetricVariation period hPeriod =
        zeroSmoothDiagonalMetricVariation period hPeriod +
          zeroSmoothDiagonalMetricVariation period hPeriod
      have hZero :
          zeroSmoothDiagonalMetricVariation period hPeriod =
            (0 : SmoothDiagonalMetricVariation period hPeriod) := by
        apply SmoothDiagonalMetricVariation.ext <;> rfl
      rw [hZero]
      exact (add_zero 0).symm
    · change (0 : _) = 0 + 0
      simp
    · change first + second = first + second
      rfl
    · change (0 : _) = 0 + 0
      simp
    · change (0 : _) = 0 + 0
      simp
    · change (0 : _) = 0 + 0
      simp
    · change (0 : _) = 0 + 0
      simp
    · change (0 : _) = 0 + 0
      simp
  map_smul' scalar direction := by
    apply IndependentFieldVariation.ext
    · change zeroSmoothDiagonalMetricVariation period hPeriod =
        scalar • zeroSmoothDiagonalMetricVariation period hPeriod
      have hZero :
          zeroSmoothDiagonalMetricVariation period hPeriod =
            (0 : SmoothDiagonalMetricVariation period hPeriod) := by
        apply SmoothDiagonalMetricVariation.ext <;> rfl
      rw [hZero]
      exact (smul_zero scalar).symm
    · change (0 : _) = scalar • 0
      simp
    · change scalar • direction = scalar • direction
      rfl
    · change (0 : _) = scalar • 0
      simp
    · change (0 : _) = scalar • 0
      simp
    · change (0 : _) = scalar • 0
      simp
    · change (0 : _) = scalar • 0
      simp
    · change (0 : _) = scalar • 0
      simp

/-- The same gauge pair in the complete variation, with the existing
completion slots fixed to zero. -/
def gaugeVariationPairCompleteLinearMap :
    GaugeVariationPair period hPeriod →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod :=
  (independentCompleteVariationLinearMap period hPeriod).comp
    (gaugeVariationPairIndependentLinearMap period hPeriod)

/-- Gauge-only complete variations are in the legacy-matter-free kernel. -/
def gaugeVariationPairMatterFreeLinearMap :
    GaugeVariationPair period hPeriod →ₗ[Real]
      MatterFreeCompleteVariation period hPeriod where
  toFun := fun direction =>
    ⟨gaugeVariationPairCompleteLinearMap period hPeriod direction, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (gaugeVariationPairCompleteLinearMap period hPeriod).map_add
      first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact (gaugeVariationPairCompleteLinearMap period hPeriod).map_smul
      scalar direction

/-- Gauge-only complete variations also lie in the corrected general-metric
kernel: their obsolete diagonal metric direction is zero. -/
def gaugeVariationPairGeneralMetricLinearMap :
    GaugeVariationPair period hPeriod →ₗ[Real]
      GeneralMetricMatterFreeVariation period hPeriod where
  toFun := fun direction =>
    ⟨gaugeVariationPairMatterFreeLinearMap period hPeriod direction, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (gaugeVariationPairMatterFreeLinearMap period hPeriod).map_add
      first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact (gaugeVariationPairMatterFreeLinearMap period hPeriod).map_smul
      scalar direction

/-- Canonical gauge-only direction in the D10-free physical tangent. -/
def gaugeVariationPairPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GaugeVariationPair period hPeriod →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.inl Real
      (GeneralMetricMatterFreeVariation period hPeriod)
      (Sector →
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)).comp
    (gaugeVariationPairGeneralMetricLinearMap period hPeriod)

@[simp]
theorem gaugeVariationPairPhysicalTangentLinearMap_gauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (direction : GaugeVariationPair period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (gaugeVariationPairPhysicalTangentLinearMap
        period hPeriod configuration direction)).independent.gauge =
      direction :=
  rfl

theorem gaugeVariationPairPhysicalTangentLinearMap_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (gaugeVariationPairPhysicalTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  have hGauge := congrArg
    (fun variation :
        GlobalPhysicalFieldTangent period hPeriod configuration =>
      (GlobalPhysicalFieldTangent.completeVariation
        period hPeriod variation).independent.gauge)
    hEqual
  simpa using hGauge

/-- Gauge-only physical directions lie in the corrected minimal tangent:
the obsolete coefficient ghost and auxiliary slots remain exactly zero. -/
def gaugeVariationPairMinimalPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GaugeVariationPair period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration where
  toFun := fun direction =>
    ⟨gaugeVariationPairPhysicalTangentLinearMap
        period hPeriod configuration direction, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact
      (gaugeVariationPairPhysicalTangentLinearMap
        period hPeriod configuration).map_add first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact
      (gaugeVariationPairPhysicalTangentLinearMap
        period hPeriod configuration).map_smul scalar direction

@[simp]
theorem gaugeVariationPairMinimalPhysicalTangentLinearMap_gauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (direction : GaugeVariationPair period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (gaugeVariationPairMinimalPhysicalTangentLinearMap
        period hPeriod configuration direction).1).independent.gauge =
      direction :=
  rfl

theorem gaugeVariationPairMinimalPhysicalTangentLinearMap_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (gaugeVariationPairMinimalPhysicalTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  apply gaugeVariationPairPhysicalTangentLinearMap_injective
    period hPeriod configuration
  exact congrArg (fun variation => variation.1) hEqual

/-- Faithful Candidate-A intrinsic potentials, evaluated in the supplied
regular frames and inserted into the corrected minimal physical tangent. -/
def globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    (Sector → SmoothAbelianGaugePotential period hPeriod) →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration :=
  (gaugeVariationPairMinimalPhysicalTangentLinearMap
      period hPeriod configuration).comp
    (globalCandidateAPairedGaugePotentialCoefficientLinearMap
      period hPeriod data)

@[simp]
theorem globalCandidateAPairedGaugePotentialMinimalTangentLinearMap_gauge
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        period hPeriod data potential).1).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap
        period hPeriod data potential :=
  rfl

theorem
    globalCandidateAPairedGaugePotentialMinimalTangentLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Function.Injective
      (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        period hPeriod data) := by
  intro first second hEqual
  apply globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
    period hPeriod data
  exact
    (gaugeVariationPairMinimalPhysicalTangentLinearMap_injective
      period hPeriod configuration) hEqual

end
end P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
end JanusFormal
