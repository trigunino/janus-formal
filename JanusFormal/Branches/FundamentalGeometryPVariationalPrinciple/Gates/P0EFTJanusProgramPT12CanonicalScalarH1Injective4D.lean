import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D

/-! Faithfulness of the existing scalar H¹ completion, from concrete Stokes adjoints. -/
namespace JanusFormal.P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
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

open Set
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

private abbrev volume := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
private abbrev ScalarH1 (frame : SmoothD8Frame period hPeriod) :=
  H1GraphSpace period hPeriod Real frame (volume period hPeriod)

private def jetDerivativeProjection (frame : SmoothD8Frame period hPeriod)
    (index : Fin frame.count) : (Real × (Fin frame.count → Real)) →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp (ContinuousLinearMap.snd Real _ _)

def canonicalH1DerivativeToL2 (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    ScalarH1 period hPeriod frame →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  ((jetDerivativeProjection period hPeriod frame index).compLpL (2 : ENNReal)
    (volume period hPeriod)).comp (h1GraphSubmodule period hPeriod Real frame (volume period hPeriod)).subtypeL

theorem canonicalH1DerivativeToL2_smooth
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalH1DerivativeToL2 period hPeriod frame index
      (smoothToH1GraphLinearMap period hPeriod Real frame (volume period hPeriod) field) =
      canonicalFrameDerivativeL2 period hPeriod frame index field := by
  apply Lp.ext
  have hProjection := (jetDerivativeProjection period hPeriod frame index).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := volume period hPeriod)
    (smoothFirstJetToL2 period hPeriod Real frame (volume period hPeriod) field)
  have hJet := (smoothFirstJet_memLp period hPeriod Real frame (volume period hPeriod) field).coeFn_toLp
  filter_upwards [hProjection, hJet,
    smoothFieldToL2_ae period hPeriod Real (volume period hPeriod)
      (canonicalFrameDerivativeSmooth period hPeriod frame index field)] with point hp hj hv
  exact (hp.trans (congrArg (jetDerivativeProjection period hPeriod frame index) hj)).trans hv.symm

/-- Every completed H¹ derivative is the value of the minimal closed L² derivative. -/
theorem canonicalH1DerivativeGraph_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (x : ScalarH1 period hPeriod frame) :
    (h1GraphToL2 period hPeriod Real frame (volume period hPeriod) x,
      canonicalH1DerivativeToL2 period hPeriod frame index x) ∈
      (canonicalFrameDerivativeMinimal period hPeriod frame index).graph := by
  let inclusion := h1GraphToL2 period hPeriod Real frame (volume period hPeriod)
  let derivative := canonicalH1DerivativeToL2 period hPeriod frame index
  let operator := canonicalFrameDerivativeMinimal period hPeriod frame index
  have hClosed : IsClosed ((inclusion.prod derivative) ⁻¹' (operator.graph : Set _)) :=
    (canonicalFrameDerivativeMinimal_isClosed period hPeriod metric frame index).preimage
      (inclusion.prod derivative).continuous
  have hSmooth : Set.range (smoothToH1GraphLinearMap period hPeriod Real frame
      (volume period hPeriod)) ⊆ (inclusion.prod derivative) ⁻¹' (operator.graph : Set _) := by
    rintro _ ⟨field, rfl⟩
    change (h1GraphToL2 period hPeriod Real frame (volume period hPeriod) _,
      canonicalH1DerivativeToL2 period hPeriod frame index _) ∈ operator.graph
    rw [h1GraphToL2_agrees_on_smooth, canonicalH1DerivativeToL2_smooth]
    apply operator.mem_graph_iff.mpr
    exact ⟨⟨smoothToCanonicalPhysicalBulkL2 period hPeriod field,
      canonicalFrameDerivativeMinimal_smooth_mem period hPeriod frame index field⟩,
      rfl, canonicalFrameDerivativeMinimal_smooth_apply period hPeriod metric frame index field⟩
  exact closure_minimal hSmooth hClosed
    (smoothToH1Graph_denseRange period hPeriod Real frame (volume period hPeriod) x)

/-- Canonical-volume graph completion introduces no spurious scalar H¹ vector. -/
theorem canonicalScalarH1ToL2_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    Function.Injective (h1GraphToL2 period hPeriod Real frame (volume period hPeriod)) := by
  intro x y hValue
  have hDerivative (index : Fin frame.count) :
      canonicalH1DerivativeToL2 period hPeriod frame index x =
        canonicalH1DerivativeToL2 period hPeriod frame index y := by
    let operator := canonicalFrameDerivativeMinimal period hPeriod frame index
    have hDifference := operator.graph.sub_mem
      (canonicalH1DerivativeGraph_mem period hPeriod metric frame index x)
      (canonicalH1DerivativeGraph_mem period hPeriod metric frame index y)
    exact sub_eq_zero.mp (operator.graph_fst_eq_zero_snd hDifference (sub_eq_zero.mpr hValue))
  apply Subtype.ext
  apply Lp.ext
  have hFirstX := (ContinuousLinearMap.fst Real Real (Fin frame.count → Real)).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := volume period hPeriod) x.val
  have hFirstY := (ContinuousLinearMap.fst Real Real (Fin frame.count → Real)).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := volume period hPeriod) y.val
  have hRestX := ae_all_iff.mpr (fun index : Fin frame.count =>
    (jetDerivativeProjection period hPeriod frame index).coeFn_compLpL
      (p := (2 : ENNReal)) (μ := volume period hPeriod) x.val)
  have hRestY := ae_all_iff.mpr (fun index : Fin frame.count =>
    (jetDerivativeProjection period hPeriod frame index).coeFn_compLpL
      (p := (2 : ENNReal)) (μ := volume period hPeriod) y.val)
  filter_upwards [hFirstX, hFirstY, hRestX, hRestY] with point hx hy hdx hdy
  apply Prod.ext
  · exact hx.symm.trans ((congrArg (fun value : CanonicalPhysicalBulkL2 period hPeriod => value point)
      hValue).trans hy)
  · funext index
    exact (hdx index).symm.trans
      ((congrArg (fun value : CanonicalPhysicalBulkL2 period hPeriod => value point)
        (hDerivative index)).trans (hdy index))

theorem canonicalPhysicalScalarH1ToBulkL2_injective
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective (canonicalPhysicalScalarH1ToBulkL2 period hPeriod) :=
  canonicalScalarH1ToL2_injective period hPeriod metric (finiteSmoothTangentFrame period hPeriod)

end
end JanusFormal.P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
