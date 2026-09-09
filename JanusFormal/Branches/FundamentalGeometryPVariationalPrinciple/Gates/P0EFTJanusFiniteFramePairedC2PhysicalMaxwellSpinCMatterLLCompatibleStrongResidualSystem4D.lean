import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D

/-! # Pointwise strong LL system on the compatible completion

Smooth tests separate the two smooth algebraic LL residuals pointwise.  For
the LL-field equation, the proved zero-boundary Stokes theorem for the
canonical divergence-free frame promotes the weak equation to its pointwise
strong form.  Combining these facts with the compatible-completion gate gives
an unconditional strong residual characterization of smooth stationarity.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleStrongResidualSystem4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev AmbientLLPacket :=
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance : Measure.IsOpenPosMeasure
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

local instance : NormedSpace Real (AmbientLLPacket period hPeriod) :=
  Prod.normedSpace

local instance : ContinuousSMul Real (AmbientLLPacket period hPeriod) := by
  apply Prod.continuousSMul

/-- Smooth stationarity of the corrected completion is exactly the two
pointwise algebraic LL equations and the pointwise strong differential LL
equation.  All localization, full-support and Stokes inputs are discharged by
the canonical throat geometry. -/
theorem finite_frame_paired_c2_physical_maxwell_spinC_matter_LL_compatible_strong_residual_system_gate
    (fields : IndependentFields period hPeriod) :
    fderiv Real (compatibleCompletedLLAction period hPeriod)
        (smoothToCompatibleLLCompletion period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) = 0 ↔
      (∀ point : EffectiveThroat period hPeriod,
        ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields point = 0) ∧
      (∀ point : EffectiveThroat period hPeriod,
        llMeasureStrongResidual period hPeriod fields point = 0) ∧
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)) fields := by
  rw [compatibleCompletedLLAction_fderiv_smooth_eq_zero_iff_residualSystem]
  rw [smoothThroatField_pairing_detects_pointwise_zero period hPeriod
    (ptSymmetricLLAuxMetricStrongResidual period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
  rw [smoothThroatField_pairing_detects_pointwise_zero period hPeriod
    (llMeasureStrongResidual period hPeriod fields)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
  constructor
  · rintro ⟨hAuxMetric, hMeasure, hWeakPairing⟩
    refine ⟨hAuxMetric, hMeasure, ?_⟩
    apply (canonicalDivergenceFreeLLFrame_weak_iff_strong period hPeriod fields
      (smoothLLStrongRegularity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod))).mp
    intro test
    simpa only [weakLLEulerOperator_apply] using hWeakPairing test
  · rintro ⟨hAuxMetric, hMeasure, hStrong⟩
    refine ⟨hAuxMetric, hMeasure, ?_⟩
    have hWeak :=
      (canonicalDivergenceFreeLLFrame_weak_iff_strong period hPeriod fields
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod))).mpr hStrong
    intro test
    simpa only [weakLLEulerOperator_apply] using hWeak test

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleStrongResidualSystem4D
end JanusFormal
