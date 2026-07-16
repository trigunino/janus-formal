import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleDeterminantLineFamily
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

#check LinearMap.toSpanSingleton
#check LinearMap.toSpanSingleton_apply
#check LinearEquiv.ofBijective
#check exists_smul_eq_of_finrank_eq_one
#check smul_left_injective
#check smul_right_injective
#check LinearEquiv.toSpanNonzeroSingleton
#check Topology.IsInducing.induced
#check Topology.isInducing_const_prod
#check AddCircle.liftIco_continuous
#check Complex.continuous_exp
#check Complex.exp_log
#check Bundle.Trivial.vectorBundle
#check Bundle.Pretrivialization.IsLinear
#check FiberBundle.continuousAt_section

namespace JanusFormal
namespace Probe
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open Topology

noncomputable section

noncomputable def frameEquiv (fold : Fold) (twist : CircleTwist) :
    ℂ ≃ₗ[ℂ] CircleBoundedDeterminantLine fold twist :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ _ (circleDeterminantFourierFrame fold twist))
    ⟨by
      intro first second h
      apply (smul_left_injective ℂ
        (M := CircleBoundedDeterminantLine fold twist)
        (circleDeterminantFourierFrame_ne_zero fold twist))
      exact h,
      by
        intro output
        simpa using exists_smul_eq_of_finrank_eq_one
          (circleBoundedDeterminantLine_finrank_one fold twist)
          (circleDeterminantFourierFrame_ne_zero fold twist) output⟩

@[simp] theorem frameEquiv_apply (fold : Fold) (twist : CircleTwist) (z : ℂ) :
    frameEquiv fold twist z = z • circleDeterminantFourierFrame fold twist := by
  rfl

@[simp] theorem frameEquiv_one (fold : Fold) (twist : CircleTwist) :
    frameEquiv fold twist 1 = circleDeterminantFourierFrame fold twist := by simp

@[simp] theorem frameCoordinate_frame (fold : Fold) (twist : CircleTwist) :
    (frameEquiv fold twist).symm (circleDeterminantFourierFrame fold twist) = 1 := by
  rw [← frameEquiv_one fold twist, LinearEquiv.symm_apply_apply]

theorem frame_decomposition (fold : Fold) (twist : CircleTwist)
    (vector : CircleBoundedDeterminantLine fold twist) :
    vector = (frameEquiv fold twist).symm vector •
      circleDeterminantFourierFrame fold twist := by
  rw [← frameEquiv_apply]
  exact ((frameEquiv fold twist).apply_symm_apply vector).symm

noncomputable instance detTopology (fold : Fold) (twist : CircleTwist) :
    TopologicalSpace (CircleBoundedDeterminantLine fold twist) :=
  TopologicalSpace.induced (frameEquiv fold twist).symm inferInstance

abbrev DetFamily (fold : Fold) (twist : CircleTwist) :=
  CircleBoundedDeterminantLine fold twist

noncomputable def intervalPretrivialization (fold : Fold) :
    Bundle.Pretrivialization ℂ
      (Bundle.TotalSpace.proj : Bundle.TotalSpace ℂ (DetFamily fold) → CircleTwist) where
  toFun point := (point.1, (frameEquiv fold point.1).symm point.2)
  invFun point := ⟨point.1, frameEquiv fold point.1 point.2⟩
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' point _ := by
    rcases point with ⟨twist, vector⟩
    simp only [Bundle.TotalSpace.mk_inj]
    exact (frameEquiv fold twist).apply_symm_apply vector
  right_inv' point _ := by
    exact Prod.ext rfl ((frameEquiv fold point.1).symm_apply_apply point.2)
  open_target := isOpen_univ
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

noncomputable instance intervalPretrivialization_isLinear (fold : Fold) :
    (intervalPretrivialization fold).IsLinear ℂ where
  linear twist _ := (frameEquiv fold twist).symm.toLinearMap.isLinear

noncomputable def intervalVectorPrebundle (fold : Fold) :
    VectorPrebundle ℂ ℂ (DetFamily fold) where
  pretrivializationAtlas := {intervalPretrivialization fold}
  pretrivialization_linear' := by
    intro trivialization h
    rw [Set.mem_singleton_iff.mp h]
    infer_instance
  pretrivializationAt := fun _ => intervalPretrivialization fold
  mem_base_pretrivializationAt _ := Set.mem_univ _
  pretrivialization_mem_atlas _ := Set.mem_singleton _
  exists_coordChange := by
    intro first hFirst second hSecond
    rw [Set.mem_singleton_iff.mp hFirst, Set.mem_singleton_iff.mp hSecond]
    refine ⟨fun _ => ContinuousLinearMap.id ℂ ℂ, continuous_const.continuousOn, ?_⟩
    intro twist _ vector
    simp [intervalPretrivialization]
  totalSpaceMk_isInducing := by
    intro twist
    have hCoordinate : IsInducing (frameEquiv fold twist).symm :=
      Topology.IsInducing.induced _
    have hProduct : IsInducing
        (fun vector : DetFamily fold twist =>
          (twist, (frameEquiv fold twist).symm vector)) :=
      Topology.isInducing_const_prod.mpr hCoordinate
    change IsInducing
      (fun vector : DetFamily fold twist =>
        (twist, (frameEquiv fold twist).symm vector))
    exact hProduct

noncomputable instance intervalDeterminantTotalTopology (fold : Fold) :
    TopologicalSpace (Bundle.TotalSpace ℂ (DetFamily fold)) :=
  (intervalVectorPrebundle fold).totalSpaceTopology

noncomputable instance intervalDeterminantFiberBundle (fold : Fold) :
    FiberBundle ℂ (DetFamily fold) :=
  (intervalVectorPrebundle fold).toFiberBundle

noncomputable instance intervalDeterminantVectorBundle (fold : Fold) :
    VectorBundle ℂ ℂ (DetFamily fold) :=
  (intervalVectorPrebundle fold).toVectorBundle

@[simp] theorem interval_trivializationAt_snd
    (fold : Fold) (base twist : CircleTwist) (vector : DetFamily fold twist) :
    (trivializationAt ℂ (DetFamily fold) base
      (Bundle.TotalSpace.mk' ℂ twist vector)).2 =
      (frameEquiv fold twist).symm vector := by
  rfl

theorem continuous_circleTwist_value : Continuous CircleTwist.value :=
  (MetricSpace.isometry_induced CircleTwist.value circleTwist_value_injective).continuous

def intervalFourierFrameSection (fold : Fold) (twist : CircleTwist) :
    DetFamily fold twist :=
  circleDeterminantFourierFrame fold twist

theorem continuous_intervalFourierFrameSection (fold : Fold) :
    Continuous (fun twist =>
      Bundle.TotalSpace.mk' ℂ twist (intervalFourierFrameSection fold twist)) := by
  rw [continuous_iff_continuousAt]
  intro twist
  rw [FiberBundle.continuousAt_section ℂ twist]
  simpa [intervalFourierFrameSection] using
    (continuousAt_const : ContinuousAt (fun _ : CircleTwist => (1 : ℂ)) twist)

def intervalCrossingScalar (twist : CircleTwist) : ℂ :=
  (twist.value * (1 - twist.value) : ℝ)

theorem continuous_intervalCrossingScalar : Continuous intervalCrossingScalar := by
  change Continuous (fun twist : CircleTwist =>
    ((twist.value * (1 - twist.value) : ℝ) : ℂ))
  exact Complex.continuous_ofReal.comp
    (continuous_circleTwist_value.mul
      (continuous_const.sub continuous_circleTwist_value))

def intervalFredholmCrossingSection (fold : Fold) (twist : CircleTwist) :
    DetFamily fold twist :=
  intervalCrossingScalar twist • intervalFourierFrameSection fold twist

theorem intervalFredholmCrossingSection_eq_zero_iff
    (fold : Fold) (twist : CircleTwist) :
    intervalFredholmCrossingSection fold twist = 0 ↔
      twist.value = 0 ∨ twist.value = 1 := by
  rw [intervalFredholmCrossingSection, smul_eq_zero]
  simp only [intervalFourierFrameSection,
    circleDeterminantFourierFrame_ne_zero, or_false]
  simp only [intervalCrossingScalar, Complex.ofReal_eq_zero, mul_eq_zero]
  constructor
  · rintro (hZero | hOne)
    · exact Or.inl hZero
    · exact Or.inr (sub_eq_zero.mp hOne).symm
  · rintro (hZero | hOne)
    · exact Or.inl hZero
    · exact Or.inr (sub_eq_zero.mpr hOne.symm)

theorem continuous_intervalFredholmCrossingSection (fold : Fold) :
    Continuous (fun twist =>
      Bundle.TotalSpace.mk' ℂ twist (intervalFredholmCrossingSection fold twist)) := by
  rw [continuous_iff_continuousAt]
  intro twist
  rw [FiberBundle.continuousAt_section ℂ twist]
  simpa [intervalFredholmCrossingSection, intervalFourierFrameSection] using
    continuous_intervalCrossingScalar.continuousAt

/-! Large-gauge clutching in Fourier coordinates. -/

noncomputable def largeGaugeClutchingScalar (fold : Fold) : ℂ :=
  (frameEquiv fold periodicTwist).symm
    (circleLargeGaugeDeterminantTransition fold
      (circleDeterminantFourierFrame fold unitCircleTwist))

theorem largeGaugeClutchingScalar_ne_zero (fold : Fold) :
    largeGaugeClutchingScalar fold ≠ 0 := by
  intro hZero
  have hImageZero :
      circleLargeGaugeDeterminantTransition fold
          (circleDeterminantFourierFrame fold unitCircleTwist) = 0 := by
    apply (frameEquiv fold periodicTwist).symm.injective
    simpa [largeGaugeClutchingScalar] using hZero
  apply circleDeterminantFourierFrame_ne_zero fold unitCircleTwist
  apply (circleLargeGaugeDeterminantTransition fold).injective
  simpa using hImageZero

noncomputable def largeGaugeClutchingUnit (fold : Fold) : ℂˣ :=
  Units.mk0 (largeGaugeClutchingScalar fold)
    (largeGaugeClutchingScalar_ne_zero fold)

theorem circleLargeGaugeDeterminantTransition_frame
    (fold : Fold) :
    circleLargeGaugeDeterminantTransition fold
        (circleDeterminantFourierFrame fold unitCircleTwist) =
      largeGaugeClutchingScalar fold •
        circleDeterminantFourierFrame fold periodicTwist := by
  rw [← frameEquiv_apply]
  exact ((frameEquiv fold periodicTwist).apply_symm_apply
    (circleLargeGaugeDeterminantTransition fold
      (circleDeterminantFourierFrame fold unitCircleTwist))).symm

noncomputable def clutchingGauge (fold : Fold) (parameter : ℝ) : ℂ :=
  Complex.exp ((parameter : ℂ) * Complex.log (largeGaugeClutchingScalar fold))

theorem clutchingGauge_ne_zero (fold : Fold) (parameter : ℝ) :
    clutchingGauge fold parameter ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem clutchingGauge_zero (fold : Fold) :
    clutchingGauge fold 0 = 1 := by
  simp [clutchingGauge]

@[simp] theorem clutchingGauge_one (fold : Fold) :
    clutchingGauge fold 1 = largeGaugeClutchingScalar fold := by
  simp [clutchingGauge, Complex.exp_log (largeGaugeClutchingScalar_ne_zero fold)]

theorem continuous_clutchingGauge (fold : Fold) :
    Continuous (clutchingGauge fold) := by
  exact Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const)

end
end Probe
end JanusFormal
