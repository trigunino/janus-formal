import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Positive scalar shifts of the closed LL Jacobi operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev LLFieldL2 :=
  Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The scalar shift acts on exactly the closed Jacobi domain. -/
def llJacobiShiftedPMap (fields : IndependentFields period hPeriod) (shift : Real) :
    LLFieldL2 period hPeriod →ₗ.[Real] LLFieldL2 period hPeriod :=
  let C := llJacobiClosedPMap period hPeriod fields
  ⟨C.domain, C.toFun + shift • C.domain.subtype⟩

theorem llJacobiShiftedPMap_domain (fields : IndependentFields period hPeriod)
    (shift : Real) :
    (llJacobiShiftedPMap period hPeriod fields shift).domain =
      (llJacobiClosedPMap period hPeriod fields).domain := rfl

theorem llJacobiShiftedPMap_apply (fields : IndependentFields period hPeriod)
    (shift : Real) (x : (llJacobiClosedPMap period hPeriod fields).domain) :
    llJacobiShiftedPMap period hPeriod fields shift x =
      llJacobiClosedPMap period hPeriod fields x +
        shift • (x : LLFieldL2 period hPeriod) := by
  simp [llJacobiShiftedPMap]

/-- A scalar shift preserves closedness of the Jacobi realization. -/
theorem llJacobiShiftedPMap_isClosed (fields : IndependentFields period hPeriod)
    (shift : Real) :
    (llJacobiShiftedPMap period hPeriod fields shift).IsClosed := by
  let E := LLFieldL2 period hPeriod
  let C := llJacobiClosedPMap period hPeriod fields
  let S := llJacobiShiftedPMap period hPeriod fields shift
  have hDomain : S.domain = C.domain :=
    llJacobiShiftedPMap_domain period hPeriod fields shift
  have hValue (u : E) (huS : u ∈ S.domain) (huC : u ∈ C.domain) :
      S ⟨u, huS⟩ = C ⟨u, huC⟩ + shift • u := by
    change C ⟨u, huS⟩ + shift • u = C ⟨u, huC⟩ + shift • u
    rfl
  have hGraph : (S.graph : Set (E × E)) =
      (fun p : E × E => (p.1, p.2 - shift • p.1)) ⁻¹' (C.graph : Set (E × E)) := by
    ext p
    constructor
    · intro hp
      have huS : p.1 ∈ S.domain := S.mem_domain_of_mem_graph hp
      have huC : p.1 ∈ C.domain := by rw [← hDomain]; exact huS
      have hv : p.2 = S ⟨p.1, huS⟩ := (S.image_iff huS).mpr hp
      have hvC : p.2 - shift • p.1 = C ⟨p.1, huC⟩ := by
        rw [hv, hValue p.1 huS huC]
        simp
      exact (C.image_iff huC).mp hvC
    · intro hp
      have huC : p.1 ∈ C.domain := C.mem_domain_of_mem_graph hp
      have huS : p.1 ∈ S.domain := by rw [hDomain]; exact huC
      have hv : p.2 - shift • p.1 = C ⟨p.1, huC⟩ :=
        (C.image_iff huC).mpr hp
      apply (S.image_iff huS).mp
      rw [hValue p.1 huS huC]
      exact (sub_eq_iff_eq_add).mp hv
  have hShear : Continuous (fun p : E × E => (p.1, p.2 - shift • p.1)) :=
    continuous_fst.prodMk (continuous_snd.sub (continuous_const.smul continuous_fst))
  change IsClosed (S.graph : Set (E × E))
  rw [hGraph]
  exact (llJacobiClosedPMap_isClosed period hPeriod fields).preimage hShear

/-- Any shift beyond the semiboundedness constant is coercive on the same domain. -/
theorem llJacobiShiftedPMap_coercive (fields : IndependentFields period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (shift : Real), constant < shift →
        ∀ x : (llJacobiShiftedPMap period hPeriod fields shift).domain,
          (shift - constant) * ‖(x : LLFieldL2 period hPeriod)‖ ^ 2 ≤
            inner Real (llJacobiShiftedPMap period hPeriod fields shift x)
              (x : LLFieldL2 period hPeriod) := by
  obtain ⟨constant, hNonnegative, hLower⟩ :=
    llJacobiClosedPMap_l2_lower_bound period hPeriod fields
  refine ⟨constant, hNonnegative, ?_⟩
  intro shift hShift x
  have hBase := hLower x
  rw [llJacobiShiftedPMap_apply]
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith

private theorem closed_range_of_norm_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (T : E →ₗ.[Real] E) (hClosed : T.IsClosed)
    (c : Real) (hc : 0 < c)
    (hLower : ∀ x : T.domain, c * ‖(x : E)‖ ≤ ‖T x‖) :
    IsClosed (Set.range T.toFun) := by
  let d : Real := min 1 c
  have hd : 0 < d := lt_min (by norm_num) hc
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdc : d ≤ c := min_le_right _ _
  let projection : T.graph →ₗ[Real] E :=
    (LinearMap.snd Real E E).comp T.graph.subtype
  have hProjection (z : T.graph) : d * ‖z‖ ≤ ‖projection z‖ := by
    obtain ⟨x, hx, hy⟩ := T.mem_graph_iff.mp z.property
    have hInput : c * ‖z.1.1‖ ≤ ‖z.1.2‖ := by
      simpa only [hx, hy] using hLower x
    have hInput' : d * ‖z.1.1‖ ≤ ‖z.1.2‖ :=
      (mul_le_mul_of_nonneg_right hdc (norm_nonneg _)).trans hInput
    have hOutput : d * ‖z.1.2‖ ≤ ‖z.1.2‖ := by
      nlinarith [norm_nonneg z.1.2]
    change d * max ‖z.1.1‖ ‖z.1.2‖ ≤ ‖z.1.2‖
    rcases le_total ‖z.1.1‖ ‖z.1.2‖ with h | h
    · rw [max_eq_right h]
      exact hOutput
    · rw [max_eq_left h]
      exact hInput'
  have hAnti : ∃ K : NNReal, AntilipschitzWith K projection :=
    antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨d, hd, hProjection⟩
  letI : CompleteSpace T.graph := hClosed.completeSpace_coe
  have hProjectionClosed : IsClosed (Set.range projection) :=
    hAnti.choose_spec.isClosed_range
      (uniformContinuous_snd.comp uniformContinuous_subtype_val)
  have hRange : Set.range projection = Set.range T.toFun := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, _, hy⟩ := T.mem_graph_iff.mp z.property
      exact ⟨x, hy⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : E), T x), T.mem_graph x⟩, rfl⟩
  exact hRange ▸ hProjectionClosed

/-- Every shift above the semiboundedness constant has closed range. -/
theorem llJacobiShiftedPMap_closed_range_of_gt
    (fields : IndependentFields period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ shift : Real, constant < shift →
        IsClosed (Set.range
          (llJacobiShiftedPMap period hPeriod fields shift).toFun) := by
  obtain ⟨constant, hNonnegative, hLower⟩ :=
    llJacobiShiftedPMap_coercive period hPeriod fields
  refine ⟨constant, hNonnegative, ?_⟩
  intro shift hShift
  let E := LLFieldL2 period hPeriod
  let S := llJacobiShiftedPMap period hPeriod fields shift
  have hNormLower (x : S.domain) :
      (shift - constant) * ‖(x : E)‖ ≤ ‖S x‖ := by
    have h := hLower shift hShift x
    change (shift - constant) * ‖(x : E)‖ ^ 2 ≤ inner Real (S x) (x : E) at h
    have hCS := real_inner_le_norm (S x) (x : E)
    by_cases hx : ‖(x : E)‖ = 0
    · simp [hx]
    · have hxpos : 0 < ‖(x : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      apply le_of_mul_le_mul_right ?_ hxpos
      nlinarith
  exact closed_range_of_norm_lower S
    (llJacobiShiftedPMap_isClosed period hPeriod fields shift)
    (shift - constant) (sub_pos.mpr hShift) hNormLower

end
end P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D
end JanusFormal
