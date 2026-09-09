import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYStationaryLLSystem4D

/-! # Smooth LL residual equivalence for the completed packet action

The three smooth LL slots detect the full completed C⁰ packet derivative once
their joint direct/PT first-jet image is dense.  The density statement is kept
as an explicit hypothesis: it is the exact remaining analytic bridge between
the smooth residual system and completed-packet stationarity.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothResidualEquivalence4D

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
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothFirstVariation4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

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

private abbrev SmoothLLInput :=
  GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod

private abbrev LLInput :=
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local instance : NormedSpace Real (LLInput period hPeriod) := Prod.normedSpace

local instance : ContinuousSMul Real (LLInput period hPeriod) := by
  apply Prod.continuousSMul

private abbrev smoothLLEmbedding :
    SmoothLLInput period hPeriod →ₗ[Real] LLInput period hPeriod :=
  smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

private abbrev completedLLAction : LLInput period hPeriod → Real :=
  regularGeneralMetricC0LLPTAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Completed-packet derivative tested in the smooth auxiliary-metric slot. -/
def completedLLSmoothAuxMetricPairing
    (packet : LLInput period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) : Real :=
  fderiv Real (completedLLAction period hPeriod) packet
    (smoothLLEmbedding period hPeriod (test, (0, 0)))

/-- Completed-packet derivative tested in the smooth measure slot. -/
def completedLLSmoothMeasurePairing
    (packet : LLInput period hPeriod)
    (test : SmoothThroatField period hPeriod Real) : Real :=
  fderiv Real (completedLLAction period hPeriod) packet
    (smoothLLEmbedding period hPeriod (0, (test, 0)))

/-- Completed-packet derivative tested in the smooth LL-field slot. -/
def completedLLSmoothFieldPairing
    (packet : LLInput period hPeriod)
    (test : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  fderiv Real (completedLLAction period hPeriod) packet
    (smoothLLEmbedding period hPeriod (0, (0, test)))

private theorem continuousLinearMap_eq_zero_iff_three_smoothLLPairings_of_denseRange
    (functional : LLInput period hPeriod →L[Real] Real)
    (hDense : DenseRange (smoothLLEmbedding period hPeriod)) :
    functional = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        functional (smoothLLEmbedding period hPeriod (test, (0, 0))) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        functional (smoothLLEmbedding period hPeriod (0, (test, 0))) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        functional (smoothLLEmbedding period hPeriod (0, (0, test))) = 0) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    have hSpan : Dense
        (Submodule.span Real (Set.range (smoothLLEmbedding period hPeriod)) :
          Set (LLInput period hPeriod)) :=
      hDense.mono Submodule.subset_span
    apply ContinuousLinearMap.ext_on
      (s := Set.range (smoothLLEmbedding period hPeriod)) hSpan
    rintro _ ⟨direction, rfl⟩
    have hDirection : direction =
        (direction.1, (0, 0)) +
          (0, (direction.2.1, 0)) +
          (0, (0, direction.2.2)) := by
      apply Prod.ext
      · simp
      · apply Prod.ext <;> simp
    calc
      functional (smoothLLEmbedding period hPeriod direction) =
          functional
              (smoothLLEmbedding period hPeriod (direction.1, (0, 0))) +
            functional
              (smoothLLEmbedding period hPeriod (0, (direction.2.1, 0))) +
            functional
              (smoothLLEmbedding period hPeriod (0, (0, direction.2.2))) := by
        nth_rewrite 1 [hDirection]
        rw [
          (smoothLLEmbedding period hPeriod).map_add,
          (smoothLLEmbedding period hPeriod).map_add,
          functional.map_add, functional.map_add]
      _ = 0 := by
        rw [hAuxMetric direction.1, hMeasure direction.2.1,
          hField direction.2.2]
        simp

/-- For an arbitrary completed LL packet, the three smooth slot equations are
equivalent to vanishing of the full Fréchet derivative, conditional exactly on
density of the joint direct/PT smooth first-jet image. -/
theorem regularGeneralMetricC0LLPTAction_fderiv_eq_zero_iff_three_smooth_pairings_of_denseRange
    (packet : LLInput period hPeriod)
    (hDense : DenseRange (smoothLLEmbedding period hPeriod)) :
    fderiv Real (completedLLAction period hPeriod) packet = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        completedLLSmoothAuxMetricPairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        completedLLSmoothMeasurePairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        completedLLSmoothFieldPairing period hPeriod packet test = 0) := by
  simpa [completedLLSmoothAuxMetricPairing,
    completedLLSmoothMeasurePairing, completedLLSmoothFieldPairing] using
    continuousLinearMap_eq_zero_iff_three_smoothLLPairings_of_denseRange
      period hPeriod
      (fderiv Real (completedLLAction period hPeriod) packet) hDense

/-- On a genuine smooth packet, the auxiliary-metric slot is the explicit
strong-residual pairing. -/
theorem completedLLSmoothAuxMetricPairing_smooth_eq_strongResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    completedLLSmoothAuxMetricPairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      ∫ point, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields point)
        (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest
        period hPeriod test)
  calc
    completedLLSmoothAuxMetricPairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      fullLLEuler period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          simpa [completedLLSmoothAuxMetricPairing, direction,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest]
            using
              regularGeneralMetricC0LLPTAction_fderiv_apply_smooth period
                hPeriod fields direction
    _ = _ := by
      simpa [direction] using
        fullLLEuler_pureStrongLLAuxMetric_eq_residualPairing period hPeriod
          fields test

/-- On a genuine smooth packet, the measure slot is the explicit
strong-residual pairing. -/
theorem completedLLSmoothMeasurePairing_smooth_eq_strongResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod Real) :
    completedLLSmoothMeasurePairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      ∫ point, inner Real
        (llMeasureStrongResidual period hPeriod fields point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest
        period hPeriod test)
  calc
    completedLLSmoothMeasurePairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      fullLLEuler period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          simpa [completedLLSmoothMeasurePairing, direction,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest]
            using
              regularGeneralMetricC0LLPTAction_fderiv_apply_smooth period
                hPeriod fields direction
    _ = _ := by
      simpa [direction] using
        fullLLEuler_pureStrongLLMeasure_eq_residualPairing period hPeriod fields
          test

/-- On a genuine smooth packet, the LL-field slot is the existing weak
residual pairing. -/
theorem completedLLSmoothFieldPairing_smooth_eq_weakResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod LLFieldFiber) :
    completedLLSmoothFieldPairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      weakLLEulerOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) test := by
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
        period hPeriod test)
  calc
    completedLLSmoothFieldPairing period hPeriod
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      fullLLEuler period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          simpa [completedLLSmoothFieldPairing, direction,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection,
            regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest]
            using
              regularGeneralMetricC0LLPTAction_fderiv_apply_smooth period
                hPeriod fields direction
    _ = _ := by
      simpa [direction] using
        fullLLEuler_pureStrongLLField_eq_weakLLEulerOperator period hPeriod
          fields test

/-- At a genuine smooth LL packet, completed stationarity is equivalent to
the two explicit strong residual pairings and the weak LL-field residual,
under the single direct/PT smooth-image density hypothesis. -/
theorem regularGeneralMetricC0LLPTAction_fderiv_smooth_eq_zero_iff_residualSystem_of_denseRange
    (fields : IndependentFields period hPeriod)
    (hDense : DenseRange (smoothLLEmbedding period hPeriod)) :
    fderiv Real (completedLLAction period hPeriod)
        (smoothLLEmbedding period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        (∫ point, inner Real
          (ptSymmetricLLAuxMetricStrongResidual period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) fields point)
          (test point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        (∫ point, inner Real
          (llMeasureStrongResidual period hPeriod fields point) (test point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        weakLLEulerOperator period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) test = 0) := by
  rw [regularGeneralMetricC0LLPTAction_fderiv_eq_zero_iff_three_smooth_pairings_of_denseRange
    period hPeriod _ hDense]
  constructor
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    exact ⟨fun test => by
        rw [← completedLLSmoothAuxMetricPairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hAuxMetric test,
      fun test => by
        rw [← completedLLSmoothMeasurePairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hMeasure test,
      fun test => by
        rw [← completedLLSmoothFieldPairing_smooth_eq_weakResidual
          period hPeriod fields test]
        exact hField test⟩
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    exact ⟨fun test => by
        rw [completedLLSmoothAuxMetricPairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hAuxMetric test,
      fun test => by
        rw [completedLLSmoothMeasurePairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hMeasure test,
      fun test => by
        rw [completedLLSmoothFieldPairing_smooth_eq_weakResidual
          period hPeriod fields test]
        exact hField test⟩

/-- Gate 802: at every completed LL packet, the full derivative is separated
by the three smooth slots, with the sole missing density bridge exposed as a
hypothesis. -/
theorem finite_frame_paired_c2_physical_maxwell_spinC_matter_LL_smooth_residual_equivalence_gate
    (packet : LLInput period hPeriod)
    (hDense : DenseRange (smoothLLEmbedding period hPeriod)) :
    fderiv Real (completedLLAction period hPeriod) packet = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        completedLLSmoothAuxMetricPairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        completedLLSmoothMeasurePairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        completedLLSmoothFieldPairing period hPeriod packet test = 0) :=
  regularGeneralMetricC0LLPTAction_fderiv_eq_zero_iff_three_smooth_pairings_of_denseRange
    period hPeriod packet hDense

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothResidualEquivalence4D
end JanusFormal
