import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothDensityObstruction4D

/-! # PT-compatible completed LL packet

The unrestricted direct/PT product contains packets which cannot be limits of
genuine smooth LL coefficients.  The correct completed LL space is the closure
of the smooth direct/PT first-jet image inside that product.  Its smooth lift is
dense by construction, while its subtype map gives a continuous inclusion into
the old packet space.

The polynomial LL action restricts to this closed space.  At a smooth packet,
stationarity of the restricted action is equivalent, without an ambient-density
hypothesis, to the two strong residual pairings and the weak LL-field equation.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D

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
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothResidualEquivalence4D

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

/-- The three genuine smooth LL coefficient fields. -/
abbrev SmoothLLCoefficientInput :=
  GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod

/-- The old unrestricted direct/PT first-jet packet. -/
abbrev AmbientLLPacket :=
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

private abbrev CanonicalLLFieldJetPacket :=
  C(EffectiveThroat period hPeriod, LLFieldFiber) ×
    C(EffectiveThroat period hPeriod,
      Fin (canonicalDivergenceFreeLLFrame period hPeriod).count → LLFieldFiber)

private abbrev CanonicalLLMeasureFieldJetPacket :=
  C(EffectiveThroat period hPeriod, Real) ×
    CanonicalLLFieldJetPacket period hPeriod

private abbrev CanonicalLLSinglePacket :=
  C(EffectiveThroat period hPeriod, LLMetricFiber) ×
    CanonicalLLMeasureFieldJetPacket period hPeriod

local instance : CompleteSpace (CanonicalLLFieldJetPacket period hPeriod) :=
  CompleteSpace.prod

local instance : CompleteSpace (CanonicalLLMeasureFieldJetPacket period hPeriod) :=
  CompleteSpace.prod

local instance : CompleteSpace (CanonicalLLSinglePacket period hPeriod) :=
  CompleteSpace.prod

local instance : CompleteSpace (AmbientLLPacket period hPeriod) :=
  CompleteSpace.prod

local instance : NormedSpace Real (AmbientLLPacket period hPeriod) :=
  Prod.normedSpace

local instance : ContinuousSMul Real (AmbientLLPacket period hPeriod) := by
  apply Prod.continuousSMul

/-- Algebraic smooth direct/PT first-jet map into the old packet. -/
abbrev smoothLLPacketMap :
    SmoothLLCoefficientInput period hPeriod →ₗ[Real]
      AmbientLLPacket period hPeriod :=
  smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

/-- Closed range generated by genuine smooth direct/PT LL packets. -/
def compatibleLLCompletionSubmodule :
    Submodule Real (AmbientLLPacket period hPeriod) :=
  (LinearMap.range (smoothLLPacketMap period hPeriod)).topologicalClosure

/-- The corrected completed LL space.  Its elements obey every closed
compatibility relation forced by the genuine smooth direct/PT lift. -/
abbrev CompatibleLLCompletion :=
  compatibleLLCompletionSubmodule period hPeriod

local instance compatibleLLCompletionNormedAddCommGroup :
    NormedAddCommGroup (CompatibleLLCompletion period hPeriod) :=
  (compatibleLLCompletionSubmodule period hPeriod).normedAddCommGroup

local instance compatibleLLCompletionNormedSpace :
    NormedSpace Real (CompatibleLLCompletion period hPeriod) :=
  Submodule.normedSpace (compatibleLLCompletionSubmodule period hPeriod)

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

theorem compatibleLLCompletion_isClosed :
    IsClosed
      (CompatibleLLCompletion period hPeriod :
        Set (AmbientLLPacket period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def compatibleLLCompletionCompleteSpace :
    CompleteSpace (CompatibleLLCompletion period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range (smoothLLPacketMap period hPeriod))

/-- Genuine smooth coefficients lifted into the compatible completion. -/
def smoothToCompatibleLLCompletion :
    SmoothLLCoefficientInput period hPeriod →ₗ[Real]
      CompatibleLLCompletion period hPeriod where
  toFun fields :=
    ⟨smoothLLPacketMap period hPeriod fields,
      (LinearMap.range (smoothLLPacketMap period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self (smoothLLPacketMap period hPeriod) fields)⟩
  map_add' first second :=
    Subtype.ext ((smoothLLPacketMap period hPeriod).map_add first second)
  map_smul' scalar fields :=
    Subtype.ext ((smoothLLPacketMap period hPeriod).map_smul scalar fields)

/-- Smooth LL lifts are dense in the compatible completion by construction. -/
theorem smoothToCompatibleLLCompletion_denseRange :
    DenseRange (smoothToCompatibleLLCompletion period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothLLPacketMap period hPeriod
  have hRange :
      Subtype.val '' Set.range
          (smoothToCompatibleLLCompletion period hPeriod) =
        (LinearMap.range inclusion : Set (AmbientLLPacket period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨fields, rfl⟩, rfl⟩
      exact ⟨fields, rfl⟩
    · rintro ⟨fields, rfl⟩
      exact ⟨smoothToCompatibleLLCompletion period hPeriod fields,
        ⟨fields, rfl⟩, rfl⟩
  change closure
      (LinearMap.range inclusion : Set (AmbientLLPacket period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToCompatibleLLCompletion period hPeriod))
  rw [hRange]

/-- Continuous inclusion of the corrected completion into the old packet. -/
def compatibleLLCompletionToAmbient :
    CompatibleLLCompletion period hPeriod →L[Real]
      AmbientLLPacket period hPeriod :=
  (compatibleLLCompletionSubmodule period hPeriod).subtypeL

theorem compatibleLLCompletionToAmbient_injective :
    Function.Injective (compatibleLLCompletionToAmbient period hPeriod) :=
  (compatibleLLCompletionSubmodule period hPeriod).subtype_injective

@[simp]
theorem compatibleLLCompletionToAmbient_smoothLift
    (fields : SmoothLLCoefficientInput period hPeriod) :
    compatibleLLCompletionToAmbient period hPeriod
        (smoothToCompatibleLLCompletion period hPeriod fields) =
      smoothLLPacketMap period hPeriod fields :=
  rfl

/-- The existing polynomial LL action restricted to compatible packets. -/
def compatibleCompletedLLAction
    (packet : CompatibleLLCompletion period hPeriod) : Real :=
  regularGeneralMetricC0LLPTAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (compatibleLLCompletionToAmbient period hPeriod packet)

theorem compatibleCompletedLLAction_contDiff :
    ContDiff Real ∞ (compatibleCompletedLLAction period hPeriod) :=
  (regularGeneralMetricC0LLPTAction_contDiff period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
    (compatibleLLCompletionToAmbient period hPeriod).contDiff

/-- The derivative of the restricted action is the ambient derivative
restricted to compatible directions. -/
theorem compatibleCompletedLLAction_hasFDerivAt
    (packet : CompatibleLLCompletion period hPeriod) :
    HasFDerivAt (compatibleCompletedLLAction period hPeriod)
      ((fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
          (compatibleLLCompletionToAmbient period hPeriod packet)).comp
        (compatibleLLCompletionToAmbient period hPeriod)) packet := by
  have hOuter : HasFDerivAt
      (regularGeneralMetricC0LLPTAction period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (fderiv Real
        (regularGeneralMetricC0LLPTAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
        (compatibleLLCompletionToAmbient period hPeriod packet))
      (compatibleLLCompletionToAmbient period hPeriod packet) :=
    ((regularGeneralMetricC0LLPTAction_contDiff period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).differentiable
        (by simp) (compatibleLLCompletionToAmbient period hPeriod packet)).hasFDerivAt
  unfold compatibleCompletedLLAction
  exact hOuter.comp packet
    (ContinuousLinearMap.hasFDerivAt (𝕜 := Real)
      (compatibleLLCompletionToAmbient period hPeriod) (x := packet))

theorem compatibleCompletedLLAction_fderiv
    (packet : CompatibleLLCompletion period hPeriod) :
    fderiv Real (compatibleCompletedLLAction period hPeriod) packet =
      (fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
          (compatibleLLCompletionToAmbient period hPeriod packet)).comp
        (compatibleLLCompletionToAmbient period hPeriod) :=
  (compatibleCompletedLLAction_hasFDerivAt period hPeriod packet).fderiv

/-- Restricted derivative tested in the smooth auxiliary-metric slot. -/
def compatibleLLSmoothAuxMetricPairing
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) : Real :=
  fderiv Real (compatibleCompletedLLAction period hPeriod) packet
    (smoothToCompatibleLLCompletion period hPeriod (test, (0, 0)))

/-- Restricted derivative tested in the smooth measure slot. -/
def compatibleLLSmoothMeasurePairing
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod Real) : Real :=
  fderiv Real (compatibleCompletedLLAction period hPeriod) packet
    (smoothToCompatibleLLCompletion period hPeriod (0, (test, 0)))

/-- Restricted derivative tested in the smooth LL-field slot. -/
def compatibleLLSmoothFieldPairing
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  fderiv Real (compatibleCompletedLLAction period hPeriod) packet
    (smoothToCompatibleLLCompletion period hPeriod (0, (0, test)))

private theorem continuousLinearMap_eq_zero_iff_three_compatible_smooth_pairings
    (functional : CompatibleLLCompletion period hPeriod →L[Real] Real) :
    functional = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        functional
          (smoothToCompatibleLLCompletion period hPeriod (test, (0, 0))) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        functional
          (smoothToCompatibleLLCompletion period hPeriod (0, (test, 0))) = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        functional
          (smoothToCompatibleLLCompletion period hPeriod (0, (0, test))) = 0) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    have hDense : Dense
        (Submodule.span Real
            (Set.range (smoothToCompatibleLLCompletion period hPeriod)) :
          Set (CompatibleLLCompletion period hPeriod)) :=
      (smoothToCompatibleLLCompletion_denseRange period hPeriod).mono
        Submodule.subset_span
    apply ContinuousLinearMap.ext_on
      (s := Set.range (smoothToCompatibleLLCompletion period hPeriod)) hDense
    rintro _ ⟨direction, rfl⟩
    have hDirection : direction =
        (direction.1, (0, 0)) +
          (0, (direction.2.1, 0)) +
          (0, (0, direction.2.2)) := by
      apply Prod.ext
      · simp
      · apply Prod.ext <;> simp
    calc
      functional (smoothToCompatibleLLCompletion period hPeriod direction) =
          functional (smoothToCompatibleLLCompletion period hPeriod
              (direction.1, (0, 0))) +
            functional (smoothToCompatibleLLCompletion period hPeriod
              (0, (direction.2.1, 0))) +
            functional (smoothToCompatibleLLCompletion period hPeriod
              (0, (0, direction.2.2))) := by
        nth_rewrite 1 [hDirection]
        rw [
          (smoothToCompatibleLLCompletion period hPeriod).map_add,
          (smoothToCompatibleLLCompletion period hPeriod).map_add,
          functional.map_add, functional.map_add]
      _ = 0 := by
        rw [hAuxMetric direction.1, hMeasure direction.2.1,
          hField direction.2.2]
        simp

/-- On every compatible packet, its full restricted derivative is separated
by the three genuine smooth coefficient slots, with no density hypothesis. -/
theorem compatibleCompletedLLAction_fderiv_eq_zero_iff_three_smooth_pairings
    (packet : CompatibleLLCompletion period hPeriod) :
    fderiv Real (compatibleCompletedLLAction period hPeriod) packet = 0 ↔
      (∀ test : SmoothThroatField period hPeriod LLMetricFiber,
        compatibleLLSmoothAuxMetricPairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod Real,
        compatibleLLSmoothMeasurePairing period hPeriod packet test = 0) ∧
      (∀ test : SmoothThroatField period hPeriod LLFieldFiber,
        compatibleLLSmoothFieldPairing period hPeriod packet test = 0) := by
  simpa [compatibleLLSmoothAuxMetricPairing,
    compatibleLLSmoothMeasurePairing, compatibleLLSmoothFieldPairing] using
    continuousLinearMap_eq_zero_iff_three_compatible_smooth_pairings
      period hPeriod
      (fderiv Real (compatibleCompletedLLAction period hPeriod) packet)

theorem compatibleLLSmoothAuxMetricPairing_eq_ambient
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    compatibleLLSmoothAuxMetricPairing period hPeriod packet test =
      completedLLSmoothAuxMetricPairing period hPeriod
        (compatibleLLCompletionToAmbient period hPeriod packet) test := by
  simp [compatibleLLSmoothAuxMetricPairing,
    compatibleCompletedLLAction_fderiv,
    completedLLSmoothAuxMetricPairing]

theorem compatibleLLSmoothMeasurePairing_eq_ambient
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod Real) :
    compatibleLLSmoothMeasurePairing period hPeriod packet test =
      completedLLSmoothMeasurePairing period hPeriod
        (compatibleLLCompletionToAmbient period hPeriod packet) test := by
  simp [compatibleLLSmoothMeasurePairing,
    compatibleCompletedLLAction_fderiv,
    completedLLSmoothMeasurePairing]

theorem compatibleLLSmoothFieldPairing_eq_ambient
    (packet : CompatibleLLCompletion period hPeriod)
    (test : SmoothThroatField period hPeriod LLFieldFiber) :
    compatibleLLSmoothFieldPairing period hPeriod packet test =
      completedLLSmoothFieldPairing period hPeriod
        (compatibleLLCompletionToAmbient period hPeriod packet) test := by
  simp [compatibleLLSmoothFieldPairing,
    compatibleCompletedLLAction_fderiv,
    completedLLSmoothFieldPairing]

/-- On a genuine smooth packet, the compatible auxiliary-metric pairing is
the explicit strong-residual pairing from Gate 802. -/
theorem compatibleLLSmoothAuxMetricPairing_smooth_eq_strongResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    compatibleLLSmoothAuxMetricPairing period hPeriod
        (smoothToCompatibleLLCompletion period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      ∫ point, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields point)
        (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [compatibleLLSmoothAuxMetricPairing_eq_ambient]
  simpa using
    completedLLSmoothAuxMetricPairing_smooth_eq_strongResidual
      period hPeriod fields test

/-- On a genuine smooth packet, the compatible measure pairing is the
explicit strong-residual pairing from Gate 802. -/
theorem compatibleLLSmoothMeasurePairing_smooth_eq_strongResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod Real) :
    compatibleLLSmoothMeasurePairing period hPeriod
        (smoothToCompatibleLLCompletion period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      ∫ point, inner Real
        (llMeasureStrongResidual period hPeriod fields point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [compatibleLLSmoothMeasurePairing_eq_ambient]
  simpa using
    completedLLSmoothMeasurePairing_smooth_eq_strongResidual
      period hPeriod fields test

/-- On a genuine smooth packet, the compatible LL-field pairing is the weak
LL Euler operator from Gate 802. -/
theorem compatibleLLSmoothFieldPairing_smooth_eq_weakResidual
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod LLFieldFiber) :
    compatibleLLSmoothFieldPairing period hPeriod
        (smoothToCompatibleLLCompletion period hPeriod
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) test =
      weakLLEulerOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) test := by
  rw [compatibleLLSmoothFieldPairing_eq_ambient]
  simpa using
    completedLLSmoothFieldPairing_smooth_eq_weakResidual
      period hPeriod fields test

/-- At every genuine smooth LL packet, stationarity of the corrected
completion is exactly the two strong residual pairings and the weak LL-field
equation.  No false density statement about the old product is assumed. -/
theorem compatibleCompletedLLAction_fderiv_smooth_eq_zero_iff_residualSystem
    (fields : IndependentFields period hPeriod) :
    fderiv Real (compatibleCompletedLLAction period hPeriod)
        (smoothToCompatibleLLCompletion period hPeriod
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
  rw [compatibleCompletedLLAction_fderiv_eq_zero_iff_three_smooth_pairings]
  constructor
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    exact ⟨fun test => by
        rw [← compatibleLLSmoothAuxMetricPairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hAuxMetric test,
      fun test => by
        rw [← compatibleLLSmoothMeasurePairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hMeasure test,
      fun test => by
        rw [← compatibleLLSmoothFieldPairing_smooth_eq_weakResidual
          period hPeriod fields test]
        exact hField test⟩
  · rintro ⟨hAuxMetric, hMeasure, hField⟩
    exact ⟨fun test => by
        rw [compatibleLLSmoothAuxMetricPairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hAuxMetric test,
      fun test => by
        rw [compatibleLLSmoothMeasurePairing_smooth_eq_strongResidual
          period hPeriod fields test]
        exact hMeasure test,
      fun test => by
        rw [compatibleLLSmoothFieldPairing_smooth_eq_weakResidual
          period hPeriod fields test]
        exact hField test⟩

/-- Corrected LL completion gate: a closed compatible packet space with a
continuous ambient inclusion, dense genuine smooth lift, and an unconditional
smooth residual characterization of restricted stationarity. -/
theorem finite_frame_paired_c2_physical_maxwell_spinC_matter_LL_compatible_completion_gate :
    DenseRange (smoothToCompatibleLLCompletion period hPeriod) ∧
      Function.Injective (compatibleLLCompletionToAmbient period hPeriod) ∧
      ∀ fields : IndependentFields period hPeriod,
        fderiv Real (compatibleCompletedLLAction period hPeriod)
            (smoothToCompatibleLLCompletion period hPeriod
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
  exact ⟨smoothToCompatibleLLCompletion_denseRange period hPeriod,
    compatibleLLCompletionToAmbient_injective period hPeriod,
    compatibleCompletedLLAction_fderiv_smooth_eq_zero_iff_residualSystem
      period hPeriod⟩

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
end JanusFormal
