import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D

/-!
# Uniform C² jets to the canonical strong C⁰ ∩ H¹ core

Forgetting the ordered second derivatives sends the closed uniform C²-jet
core continuously to the existing first-jet graph closure.  Its value and
first-jet projections represent the same physical L² field, hence define a
continuous map to the strong C⁰ ∩ H¹ equalizer.  Continuity and density then
show that the image lies in the closed smooth strong core.

The bridge agrees exactly with both pre-existing smooth lifts.  No Sobolev
embedding, global frame, or additional regularity assumption is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev physicalFrame := finiteSmoothTangentFrame period hPeriod

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

private abbrev FrameIndex := Fin (physicalFrame period hPeriod).count

private abbrev GraphJetFiber :=
  Real × (FrameIndex period hPeriod → Real)

private abbrev GraphJetL2 :=
  Lp (GraphJetFiber period hPeriod) (2 : ENNReal)
    (physicalMeasure period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Forget the ordered second derivative in one finite-frame jet. -/
def scalarFrameJet2ToFirstJet :
    ScalarFrameJet2 (FrameIndex period hPeriod) →L[Real]
      GraphJetFiber period hPeriod :=
  (ContinuousLinearMap.fst Real Real
      ((FrameIndex period hPeriod → Real) ×
        (FrameIndex period hPeriod → FrameIndex period hPeriod → Real))).prod
    ((ContinuousLinearMap.fst Real
        (FrameIndex period hPeriod → Real)
        (FrameIndex period hPeriod → FrameIndex period hPeriod → Real)).comp
      (ContinuousLinearMap.snd Real Real
        ((FrameIndex period hPeriod → Real) ×
          (FrameIndex period hPeriod → FrameIndex period hPeriod → Real))))

/-- Retain only the scalar value in one finite-frame jet. -/
def scalarFrameJet2ToValue :
    ScalarFrameJet2 (FrameIndex period hPeriod) →L[Real] Real :=
  ContinuousLinearMap.fst Real Real
    ((FrameIndex period hPeriod → Real) ×
      (FrameIndex period hPeriod → FrameIndex period hPeriod → Real))

/-- Pointwise first-jet projection on continuous uniform jets. -/
def continuousScalarFrameJet2ToContinuousFirstJet :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
      C(EffectiveQuotient period hPeriod, GraphJetFiber period hPeriod) :=
  (scalarFrameJet2ToFirstJet period hPeriod).compLeftContinuous
    Real (EffectiveQuotient period hPeriod)

/-- Pointwise value projection on continuous uniform jets. -/
def continuousScalarFrameJet2ToContinuousValue :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  (scalarFrameJet2ToValue period hPeriod).compLeftContinuous
    Real (EffectiveQuotient period hPeriod)

/-- The continuous first jet viewed in the existing graph-L² ambient space. -/
def continuousScalarFrameJet2ToGraphL2 :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
      GraphJetL2 period hPeriod :=
  (ContinuousMap.toLp (2 : ENNReal)
      (physicalMeasure period hPeriod) Real :
        C(EffectiveQuotient period hPeriod, GraphJetFiber period hPeriod) →L[Real]
          GraphJetL2 period hPeriod).comp
    (continuousScalarFrameJet2ToContinuousFirstJet period hPeriod)

theorem continuousScalarFrameJet2ToGraphL2_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    continuousScalarFrameJet2ToGraphL2 period hPeriod
        (smoothScalarFrameJet2ContinuousLinearMap period hPeriod field) =
      smoothFirstJetL2LinearMap period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod) field := by
  change (ContinuousMap.toLp (2 : ENNReal)
      (physicalMeasure period hPeriod) Real)
        (continuousScalarFrameJet2ToContinuousFirstJet period hPeriod
          (smoothScalarFrameJet2ContinuousLinearMap period hPeriod field)) =
    smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod) field
  apply Lp.ext
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod)
      (𝕜 := Real)
      (continuousScalarFrameJet2ToContinuousFirstJet period hPeriod
        (smoothScalarFrameJet2ContinuousLinearMap period hPeriod field)),
     (smoothFirstJet_memLp period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
      field).coeFn_toLp]
    with point hLeft hRight
  rw [hLeft]
  simp only [smoothFirstJetToL2]
  rw [hRight]
  rfl

/-- The same first jet transported to the canonical Hilbert L² renorming. -/
def continuousScalarFrameJet2ToHilbertJetL2 :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
      CanonicalPhysicalHilbertJetL2 period hPeriod :=
  (canonicalPhysicalHilbertJetL2ToGraph period hPeriod).symm.toContinuousLinearMap.comp
    (continuousScalarFrameJet2ToGraphL2 period hPeriod)

theorem continuousScalarFrameJet2ToHilbertJetL2_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    continuousScalarFrameJet2ToHilbertJetL2 period hPeriod
        (smoothScalarFrameJet2ContinuousLinearMap period hPeriod field) =
      canonicalPhysicalHilbertFirstJet period hPeriod field := by
  apply (canonicalPhysicalHilbertJetL2ToGraph period hPeriod).injective
  change canonicalPhysicalHilbertJetL2ToGraph period hPeriod
      ((canonicalPhysicalHilbertJetL2ToGraph period hPeriod).symm
        (continuousScalarFrameJet2ToGraphL2 period hPeriod
          (smoothScalarFrameJet2ContinuousLinearMap period hPeriod field))) = _
  rw [(canonicalPhysicalHilbertJetL2ToGraph
      period hPeriod).apply_symm_apply,
    canonicalPhysicalHilbertJetL2ToGraph_firstJet]
  exact continuousScalarFrameJet2ToGraphL2_smooth period hPeriod field

private theorem canonicalPhysicalScalarC2JetCoreToHilbertJetL2_mem
    (jet : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    continuousScalarFrameJet2ToHilbertJetL2 period hPeriod jet.1 ∈
      canonicalPhysicalHilbertH1Submodule period hPeriod := by
  apply map_mem_closure
    (continuousScalarFrameJet2ToHilbertJetL2 period hPeriod).continuous
    jet.2
  intro smoothJet hSmoothJet
  rcases hSmoothJet with ⟨field, rfl⟩
  exact ⟨field,
    (continuousScalarFrameJet2ToHilbertJetL2_smooth
      period hPeriod field).symm⟩

/-- Continuous loss of the second derivative into the Hilbert H¹ closure. -/
def canonicalPhysicalScalarC2JetCoreToHilbertH1 :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      CanonicalPhysicalScalarHilbertH1 period hPeriod :=
  ((continuousScalarFrameJet2ToHilbertJetL2 period hPeriod).comp
      (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)).codRestrict
    (canonicalPhysicalHilbertH1Submodule period hPeriod)
    (canonicalPhysicalScalarC2JetCoreToHilbertJetL2_mem period hPeriod)

@[simp]
theorem canonicalPhysicalScalarC2JetCoreToHilbertH1_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarC2JetCoreToHilbertH1 period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) =
      smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field := by
  apply Subtype.ext
  exact continuousScalarFrameJet2ToHilbertJetL2_smooth
    period hPeriod field

/-- Continuous value projection from the C² core. -/
def canonicalPhysicalScalarC2JetCoreToContinuous :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  (continuousScalarFrameJet2ToContinuousValue period hPeriod).comp
    (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)

@[simp]
theorem canonicalPhysicalScalarC2JetCoreToContinuous_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod field := by
  apply ContinuousMap.ext
  intro point
  rfl

theorem canonicalPhysicalScalarC2JetCore_l2_compatibility
    (jet : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalPhysicalScalarC2JetCoreToContinuous
          period hPeriod jet) =
      canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        (canonicalPhysicalScalarC2JetCoreToHilbertH1
          period hPeriod jet) := by
  refine DenseRange.induction_on
    (p := fun jet : CanonicalPhysicalScalarC2JetCore period hPeriod =>
      continuousToCanonicalPhysicalBulkL2 period hPeriod
          (canonicalPhysicalScalarC2JetCoreToContinuous
            period hPeriod jet) =
        canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
          (canonicalPhysicalScalarC2JetCoreToHilbertH1
            period hPeriod jet))
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod)
    jet ?_ ?_
  · exact isClosed_eq
      ((continuousToCanonicalPhysicalBulkL2 period hPeriod).comp
        (canonicalPhysicalScalarC2JetCoreToContinuous
          period hPeriod)).continuous
      ((canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
        (canonicalPhysicalScalarC2JetCoreToHilbertH1
          period hPeriod)).continuous
  · intro field
    rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
      canonicalPhysicalScalarC2JetCoreToHilbertH1_smooth,
      continuousToCanonicalPhysicalBulkL2_agrees_on_smooth,
      canonicalPhysicalScalarHilbertH1ToBulkL2_agrees_on_smooth]

/-- Compatible value/first-jet pair in the ambient strong equalizer. -/
def canonicalPhysicalScalarC2JetCoreToStrongPair :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      (C(EffectiveQuotient period hPeriod, Real) ×
        CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).prod
    (canonicalPhysicalScalarC2JetCoreToHilbertH1 period hPeriod)

private theorem canonicalPhysicalScalarC2JetCoreToStrongPair_mem
    (jet : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToStrongPair period hPeriod jet ∈
      (canonicalPhysicalStrongH1C0Compatibility period hPeriod).ker := by
      change continuousToCanonicalPhysicalBulkL2 period hPeriod
          (canonicalPhysicalScalarC2JetCoreToContinuous
            period hPeriod jet) -
        canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
          (canonicalPhysicalScalarC2JetCoreToHilbertH1
            period hPeriod jet) = 0
      exact sub_eq_zero.mpr
        (canonicalPhysicalScalarC2JetCore_l2_compatibility
          period hPeriod jet)

/-- Continuous bridge from uniform C² jets to the ambient strong equalizer. -/
def canonicalPhysicalScalarC2JetCoreToStrong :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      CanonicalPhysicalScalarStrongH1C0 period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreToStrongPair
    period hPeriod).codRestrict
      (canonicalPhysicalStrongH1C0Compatibility period hPeriod).ker
      (canonicalPhysicalScalarC2JetCoreToStrongPair_mem period hPeriod)

@[simp]
theorem canonicalPhysicalScalarC2JetCoreToStrong_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarC2JetCoreToStrong period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) =
      smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod field := by
  apply canonicalPhysicalScalarStrongH1C0_ext period hPeriod
  · exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth
      period hPeriod field
  · exact canonicalPhysicalScalarC2JetCoreToHilbertH1_smooth
      period hPeriod field

private theorem canonicalPhysicalScalarC2JetCoreToStrong_mem_core
    (jet : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToStrong period hPeriod jet ∈
      canonicalPhysicalScalarStrongH1C0CoreSubmodule period hPeriod := by
  refine DenseRange.induction_on
    (p := fun jet : CanonicalPhysicalScalarC2JetCore period hPeriod =>
      canonicalPhysicalScalarC2JetCoreToStrong period hPeriod jet ∈
        canonicalPhysicalScalarStrongH1C0CoreSubmodule period hPeriod)
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod)
    jet ?_ ?_
  · exact (canonicalPhysicalScalarStrongH1C0Core_isClosed
      period hPeriod).preimage
        (canonicalPhysicalScalarC2JetCoreToStrong
          period hPeriod).continuous
  · intro field
    exact subset_closure ⟨field,
      (canonicalPhysicalScalarC2JetCoreToStrong_smooth
        period hPeriod field).symm⟩

/-- Final continuous bridge into the closed smooth strong core. -/
def canonicalPhysicalScalarC2JetCoreToStrongCore :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      CanonicalPhysicalScalarStrongH1C0Core period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreToStrong
    period hPeriod).codRestrict
      (canonicalPhysicalScalarStrongH1C0CoreSubmodule period hPeriod)
      (canonicalPhysicalScalarC2JetCoreToStrong_mem_core period hPeriod)

@[simp]
theorem canonicalPhysicalScalarC2JetCoreToStrongCore_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarC2JetCoreToStrongCore period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) =
      smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field := by
  apply Subtype.ext
  change canonicalPhysicalScalarC2JetCoreToStrong period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) =
    smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod field
  exact canonicalPhysicalScalarC2JetCoreToStrong_smooth
    period hPeriod field

/-- Summary gate: the new C² completion genuinely refines the established
strong C⁰ ∩ H¹ core and agrees with it on every smooth scalar. -/
theorem canonical_physical_scalar_c2_to_strong_h1_c0_bridge_gate :
    DenseRange
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarC2JetCoreToStrongCore period hPeriod
            (smoothToCanonicalPhysicalScalarC2JetCore
              period hPeriod field) =
          smoothToCanonicalPhysicalScalarStrongH1C0Core
            period hPeriod field) ∧
      (∀ jet : CanonicalPhysicalScalarC2JetCore period hPeriod,
        continuousToCanonicalPhysicalBulkL2 period hPeriod
            (canonicalPhysicalScalarC2JetCoreToContinuous
              period hPeriod jet) =
          canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
            (canonicalPhysicalScalarC2JetCoreToHilbertH1
              period hPeriod jet)) := by
  exact ⟨smoothToCanonicalPhysicalScalarC2JetCore_denseRange
      period hPeriod,
    canonicalPhysicalScalarC2JetCoreToStrongCore_smooth period hPeriod,
    canonicalPhysicalScalarC2JetCore_l2_compatibility period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
end JanusFormal
