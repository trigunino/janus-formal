import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalScalarH1Injective4D

/-! Faithfulness of the existing scalar H¹ completion without a global tangent frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeScalarH1Injective4D
set_option autoImplicit false
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
open P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D

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

/-- Completed scalar derivatives lie in the actual minimal L² derivative graph. -/
theorem frameFreeCanonicalH1DerivativeGraph_mem
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (x : H1GraphSpace period hPeriod Real frame
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) :
    (h1GraphToL2 period hPeriod Real frame
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) x,
      canonicalH1DerivativeToL2 period hPeriod frame index x) ∈
      (canonicalFrameDerivativeMinimal period hPeriod frame index).graph := by
  let volume := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let inclusion := h1GraphToL2 period hPeriod Real frame volume
  let derivative := canonicalH1DerivativeToL2 period hPeriod frame index
  let operator := canonicalFrameDerivativeMinimal period hPeriod frame index
  have hClosed : IsClosed ((inclusion.prod derivative) ⁻¹' (operator.graph : Set _)) :=
    (frameFreeCanonicalFrameDerivativeMinimal_isClosed period hPeriod frame index).preimage
      (inclusion.prod derivative).continuous
  have hSmooth : Set.range (smoothToH1GraphLinearMap period hPeriod Real frame volume) ⊆
      (inclusion.prod derivative) ⁻¹' (operator.graph : Set _) := by
    rintro _ ⟨field, rfl⟩
    change (h1GraphToL2 period hPeriod Real frame volume _,
      canonicalH1DerivativeToL2 period hPeriod frame index _) ∈ operator.graph
    rw [h1GraphToL2_agrees_on_smooth, canonicalH1DerivativeToL2_smooth]
    apply operator.mem_graph_iff.mpr
    exact ⟨⟨smoothToCanonicalPhysicalBulkL2 period hPeriod field,
      canonicalFrameDerivativeMinimal_smooth_mem period hPeriod frame index field⟩,
      rfl, frameFreeCanonicalFrameDerivativeMinimal_smooth_apply
        period hPeriod frame index field⟩
  exact closure_minimal hSmooth hClosed
    (smoothToH1Graph_denseRange period hPeriod Real frame volume x)

/-- The canonical scalar H¹ completion embeds faithfully in canonical L². -/
theorem frameFreeCanonicalScalarH1ToL2_injective
    (frame : SmoothD8Frame period hPeriod) :
    Function.Injective (h1GraphToL2 period hPeriod Real frame
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) := by
  intro x y hValue
  have hDerivative (index : Fin frame.count) :
      canonicalH1DerivativeToL2 period hPeriod frame index x =
        canonicalH1DerivativeToL2 period hPeriod frame index y := by
    let operator := canonicalFrameDerivativeMinimal period hPeriod frame index
    have hDifference := operator.graph.sub_mem
      (frameFreeCanonicalH1DerivativeGraph_mem period hPeriod frame index x)
      (frameFreeCanonicalH1DerivativeGraph_mem period hPeriod frame index y)
    exact sub_eq_zero.mp (operator.graph_fst_eq_zero_snd hDifference (sub_eq_zero.mpr hValue))
  apply Subtype.ext
  apply Lp.ext
  let projection (index : Fin frame.count) :
      (Real × (Fin frame.count → Real)) →L[Real] Real :=
    (ContinuousLinearMap.proj index).comp (ContinuousLinearMap.snd Real _ _)
  have hFirstX := (ContinuousLinearMap.fst Real Real (Fin frame.count → Real)).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) x.val
  have hFirstY := (ContinuousLinearMap.fst Real Real (Fin frame.count → Real)).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) y.val
  have hRestX := ae_all_iff.mpr (fun index : Fin frame.count =>
    (projection index).coeFn_compLpL (p := (2 : ENNReal))
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) x.val)
  have hRestY := ae_all_iff.mpr (fun index : Fin frame.count =>
    (projection index).coeFn_compLpL (p := (2 : ENNReal))
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) y.val)
  filter_upwards [hFirstX, hFirstY, hRestX, hRestY] with point hx hy hdx hdy
  apply Prod.ext
  · exact hx.symm.trans ((congrArg (fun value : CanonicalPhysicalBulkL2 period hPeriod => value point)
      hValue).trans hy)
  · funext index
    exact (hdx index).symm.trans
      ((congrArg (fun value : CanonicalPhysicalBulkL2 period hPeriod => value point)
        (hDerivative index)).trans (hdy index))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeScalarH1Injective4D
