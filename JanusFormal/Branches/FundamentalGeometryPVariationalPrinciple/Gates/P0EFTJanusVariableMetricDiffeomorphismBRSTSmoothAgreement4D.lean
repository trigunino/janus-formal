import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

/-! # Exact smooth agreement of the mobile diffeomorphism BRST action

The tensor perturbation and all three nonminimal fields remain arbitrary.
The same actual metric supplies de Donder, FP, metric lowering and volume.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricDiffeomorphismBRSTSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D
open P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
open P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D
open P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Continuous coefficients of the given geometric vector field. -/
def smoothDiffeomorphismVectorC0Coefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (field : Ghost period hPeriod) : DiffeomorphismVectorC0Coefficients period hPeriod :=
  fun index => smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (regularFrameCartanGhostCoefficient period hPeriod reference field index)

private theorem smoothDiffeomorphismVectorC0Coefficients_apply
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (field : Ghost period hPeriod) (index : Fin 4) (point : EffectiveQuotient period hPeriod) :
    smoothDiffeomorphismVectorC0Coefficients period hPeriod reference field index point =
      regularFrameCartanGhostCoefficient period hPeriod reference field index point := rfl

private theorem frameGhost_reconstruction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (field : Ghost period hPeriod) (point : EffectiveQuotient period hPeriod) :
    field point = ∑ index : Fin 4,
      regularFrameCartanGhostCoefficient period hPeriod reference field index point •
        reference.frame index point := by
  have h := congrArg (fun ghost : Ghost period hPeriod => ghost point)
    (regularFrameGhostFromCoefficients_reconstructs period hPeriod reference field)
  simpa only [regularFrameGhostFromCoefficients_apply] using h.symm

/-- Covector evaluation is exactly the finite coefficient contraction. -/
theorem regularFrameCovectorVector_contraction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (field : Ghost period hPeriod) (point : EffectiveQuotient period hPeriod)
    (covector : TangentSpace coverModelWithCorners point →L[Real] Real) :
    (∑ index : Fin 4, covector (reference.frame index point) *
      regularFrameCartanGhostCoefficient period hPeriod reference field index point) =
      covector (field point) := by
  have h := congrArg covector (frameGhost_reconstruction period hPeriod reference field point)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- The auxiliary square uses the actual metric, independently of the coefficient frame. -/
theorem regularFrameMetricVector_contraction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : Ghost period hPeriod) (point : EffectiveQuotient period hPeriod) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      metric.tensor.tensor point (reference.frame first point) (reference.frame second point) *
        regularFrameCartanGhostCoefficient period hPeriod reference field first point *
        regularFrameCartanGhostCoefficient period hPeriod reference field second point) =
      metric.tensor.tensor point (field point) (field point) := by
  conv_rhs => simp only [frameGhost_reconstruction period hPeriod reference field point]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [metric.tensor.symmetric point (reference.frame first point) (reference.frame second point)]
  ring

/-- Smooth tensor, B, antighost and ghost in their independent completed slots. -/
def smoothVariableMetricDiffeomorphismBRSTCore
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    VariableMetricDiffeomorphismBRSTCore period hPeriod reference :=
  (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor,
    (smoothTensorC2Coefficients period hPeriod reference state.metricPerturbation,
      (smoothDiffeomorphismVectorC0Coefficients period hPeriod reference
          state.nonminimal.nakanishiLautrup.field,
        (smoothDiffeomorphismVectorC0Coefficients period hPeriod reference state.nonminimal.antighost.field,
          smoothDiffeomorphismGhostC2Coefficients period hPeriod reference state.nonminimal.ghost))))

theorem smoothVariableMetricDiffeomorphismBRSTCore_mem_domain
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
      regularGeneralMetricC2Domain period hPeriod reference) :
    smoothVariableMetricDiffeomorphismBRSTCore period hPeriod reference variationTensor state ∈
      variableMetricDiffeomorphismBRSTDomain period hPeriod reference :=
  ⟨hVariation, mem_univ _⟩

set_option maxRecDepth 2048 in
/-- The completed density is the actual BRST density with its genuine mobile volume ratio. -/
theorem variableMetricDiffeomorphismBRSTDensity_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    variableMetricDiffeomorphismBRSTDensity period hPeriod reference
        (smoothVariableMetricDiffeomorphismBRSTCore period hPeriod reference variationTensor state) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state) := by
  apply ContinuousMap.ext
  intro point
  have hVolume : variableMetricCanonicalVolumeRatio period hPeriod reference
      (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor) point =
      globalMetricVolumeRatio period hPeriod metric point :=
    congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      (variableMetricCanonicalVolumeRatio_smooth period hPeriod reference variationTensor
        metric hMetric hVariation)
  have hCoefficient (first second : Fin 4) :
      regularGeneralMetricC0MetricCoefficient period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          first second point =
        metric.tensor.tensor point (reference.frame first point) (reference.frame second point) :=
    (candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
      period hPeriod reference variationTensor first second point).trans
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
          period hPeriod reference variationTensor metric hMetric first second point)
  have hDeDonder (component : Fin 4) :=
    variableMetricC2DeDonderComponentExpression_smooth_apply period hPeriod reference
      variationTensor metric hMetric hVariation state.metricPerturbation point component
  have hFP (component : Fin 4) :=
    variableMetricC2DiffeomorphismFPComponentExpression_smooth_apply period hPeriod reference
      variationTensor metric hMetric hVariation state.nonminimal.ghost point component
  have hDeDonderPair :
      (∑ component : Fin 4,
        variableMetricC2DeDonderComponentExpression period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          (smoothTensorC2Coefficients period hPeriod reference state.metricPerturbation)
          component point *
        regularFrameCartanGhostCoefficient period hPeriod reference
          state.nonminimal.nakanishiLautrup.field component point) =
      globalGeneralMetricDeDonder period hPeriod metric state.metricPerturbation point
        (state.nonminimal.nakanishiLautrup.field point) := by
    calc
      _ = ∑ component : Fin 4,
          globalGeneralMetricDeDonder period hPeriod metric state.metricPerturbation point
            (reference.frame component point) *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field component point := by
        apply Finset.sum_congr rfl
        intro component _
        have hTerm := congrArg (fun value : Real => value *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field component point) (hDeDonder component)
        exact hTerm
      _ = _ := regularFrameCovectorVector_contraction period hPeriod reference
        state.nonminimal.nakanishiLautrup.field point _
  have hAuxiliaryPair :
      (∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricC0MetricCoefficient period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          first second point *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field first point *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field second point) =
      metric.tensor.tensor point (state.nonminimal.nakanishiLautrup.field point)
        (state.nonminimal.nakanishiLautrup.field point) := by
    calc
      _ = ∑ first : Fin 4, ∑ second : Fin 4,
          metric.tensor.tensor point (reference.frame first point) (reference.frame second point) *
            regularFrameCartanGhostCoefficient period hPeriod reference
              state.nonminimal.nakanishiLautrup.field first point *
            regularFrameCartanGhostCoefficient period hPeriod reference
              state.nonminimal.nakanishiLautrup.field second point := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        have hTerm := congrArg (fun value : Real => value *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field first point *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.nakanishiLautrup.field second point) (hCoefficient first second)
        exact hTerm
      _ = _ := regularFrameMetricVector_contraction period hPeriod reference metric
        state.nonminimal.nakanishiLautrup.field point
  have hGhostPair :
      (∑ component : Fin 4,
        variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          (smoothDiffeomorphismGhostC2Coefficients period hPeriod reference state.nonminimal.ghost)
          component point *
        regularFrameCartanGhostCoefficient period hPeriod reference
          state.nonminimal.antighost.field component point) =
      globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
        state.nonminimal.ghost point (state.nonminimal.antighost.field point) := by
    calc
      _ = ∑ component : Fin 4,
          globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
            state.nonminimal.ghost point (reference.frame component point) *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.antighost.field component point := by
        apply Finset.sum_congr rfl
        intro component _
        have hTerm := congrArg (fun value : Real => value *
          regularFrameCartanGhostCoefficient period hPeriod reference
            state.nonminimal.antighost.field component point) (hFP component)
        exact hTerm
      _ = _ := regularFrameCovectorVector_contraction period hPeriod reference
        state.nonminimal.antighost.field point _
  have hBracket := congrArg₂ (fun first second : Real => first - second)
    (congrArg₂ (fun first second : Real => first - (1 / 2 : Real) * second)
      hDeDonderPair hAuxiliaryPair) hGhostPair
  have hResult := congrArg₂ (fun first second : Real => first * second) hVolume hBracket
  unfold variableMetricDiffeomorphismBRSTDensity
  dsimp only [smoothVariableMetricDiffeomorphismBRSTCore]
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, smoothDiffeomorphismVectorC0Coefficients_apply]
  exact hResult

/-- SAME-ACTION with the actual varied metric and the full independent smooth state. -/
theorem variableMetricDiffeomorphismBRSTAction_smooth_eq_BRST
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    variableMetricDiffeomorphismBRSTAction period hPeriod reference
        (smoothVariableMetricDiffeomorphismBRSTCore period hPeriod reference variationTensor state) =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  rw [variableMetricDiffeomorphismBRSTAction_eq_integral,
    variableMetricDiffeomorphismBRSTDensity_smooth period hPeriod reference variationTensor
      metric hMetric hVariation state]
  exact (globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral
    period hPeriod metric state).symm

end
end P0EFTJanusVariableMetricDiffeomorphismBRSTSmoothAgreement4D
end JanusFormal
