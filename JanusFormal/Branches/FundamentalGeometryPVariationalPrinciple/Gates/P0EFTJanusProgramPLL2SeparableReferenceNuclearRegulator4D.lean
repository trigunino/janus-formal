import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Bases
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D

/-!
# Unconditional separable reference regulator on the LL `L2` space

This file constructs a basis-dependent reference regulator on the genuine LL
flux `L2` space.  It is compact, injective, and supplied with an explicit
nuclear rank-one expansion at every positive time.  It is an auxiliary
separable-Hilbert-space regulator only: no equality with the LL Hessian or its
heat operator is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D

set_option autoImplicit false
noncomputable section

open Set Filter
open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal LinearPMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusCircleDiracHeatTraceCancellation

section SeparableHilbertReference

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

private theorem basis_dist_ge_one
    {I : Type*} (basis : HilbertBasis I Real H)
    {first second : I} (hne : first ≠ second) :
    1 ≤ dist (basis first) (basis second) := by
  have hSq : ‖basis first - basis second‖ ^ 2 = (2 : Real) := by
    rw [norm_sub_sq_real,
      (HilbertBasis.orthonormal basis).1 first,
      (HilbertBasis.orthonormal basis).1 second,
      (HilbertBasis.orthonormal basis).inner_eq_zero hne]
    norm_num
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (basis first - basis second)]

private theorem hilbertBasis_index_countable
    {I : Type*} (basis : HilbertBasis I Real H) :
    Countable I := by
  let balls : I → Set H :=
    fun mode => Metric.ball (basis mode) (1 / 3 : Real)
  apply Pairwise.countable_of_isOpen_disjoint (s := balls)
  · intro first second hne
    change Disjoint
      (Metric.ball (basis first) (1 / 3 : Real))
      (Metric.ball (basis second) (1 / 3 : Real))
    rw [Set.disjoint_left]
    intro point hFirst hSecond
    have hFirstPoint :
        dist (basis first) point < (1 / 3 : Real) := by
      simpa [Metric.mem_ball, dist_comm] using hFirst
    have hPointSecond :
        dist point (basis second) < (1 / 3 : Real) := by
      simpa [Metric.mem_ball] using hSecond
    have hlt : dist (basis first) (basis second) < 2 / 3 :=
      lt_of_le_of_lt (dist_triangle _ point _) (by linarith)
    linarith [basis_dist_ge_one basis hne]
  · intro mode
    exact Metric.isOpen_ball
  · intro mode
    exact ⟨basis mode, Metric.mem_ball_self (by norm_num)⟩

/-- A canonical chosen Hilbert-basis index set for a separable Hilbert space. -/
def referenceIndex : Set H :=
  Classical.choose (exists_hilbertBasis Real H)

/-- A chosen complete orthonormal basis of a separable Hilbert space. -/
def referenceBasis : HilbertBasis (referenceIndex (H := H)) Real H :=
  Classical.choose
    (Classical.choose_spec (exists_hilbertBasis Real H))

local instance referenceIndexDecidableEq :
    DecidableEq (referenceIndex (H := H)) :=
  Classical.decEq _

private theorem referenceIndex_countable :
    Countable (referenceIndex (H := H)) :=
  hilbertBasis_index_countable (referenceBasis (H := H))

/-- An injective numbering of the chosen basis. -/
def referenceCode :
    referenceIndex (H := H) → Nat := by
  letI : Countable (referenceIndex (H := H)) :=
    referenceIndex_countable (H := H)
  exact Classical.choose
    (Countable.exists_injective_nat (referenceIndex (H := H)))

theorem referenceCode_injective :
    Function.Injective (referenceCode (H := H)) := by
  letI : Countable (referenceIndex (H := H)) :=
    referenceIndex_countable (H := H)
  exact Classical.choose_spec
    (Countable.exists_injective_nat (referenceIndex (H := H)))

/-- Geometric reference weight attached to a numbered basis mode. -/
def referenceWeight
    (time : HeatTime) (mode : referenceIndex (H := H)) : Real :=
  Real.exp (-time.1) ^ (referenceCode (H := H) mode + 1)

theorem referenceWeight_pos
    (time : HeatTime) (mode : referenceIndex (H := H)) :
    0 < referenceWeight (H := H) time mode := by
  exact pow_pos (Real.exp_pos _) _

theorem referenceWeight_lt_one
    (time : HeatTime) (mode : referenceIndex (H := H)) :
    referenceWeight (H := H) time mode < 1 := by
  apply pow_lt_one₀ (Real.exp_nonneg _)
  · exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr time.2)
  · omega

theorem referenceWeight_summable (time : HeatTime) :
    Summable (referenceWeight (H := H) time) := by
  let ratio : Real := Real.exp (-time.1)
  have hRatioPos : 0 < ratio := Real.exp_pos _
  have hRatioLt : ratio < 1 := by
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr time.2)
  have hGeom : Summable (fun index : Nat => ratio ^ index) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos hRatioPos]
    exact hRatioLt
  have hShift : Summable (fun index : Nat => ratio ^ (index + 1)) :=
    (summable_nat_add_iff 1).2 hGeom
  change Summable
    (fun mode =>
      Real.exp (-time.1) ^ (referenceCode (H := H) mode + 1))
  simpa [ratio, Function.comp_def] using
    hShift.comp_injective (referenceCode_injective (H := H))

/-- One weighted rank-one basis projector. -/
def referenceRankOne
    (time : HeatTime) (mode : referenceIndex (H := H)) :
    H →L[Real] H :=
  referenceWeight (H := H) time mode •
    InnerProductSpace.rankOne Real
      (referenceBasis (H := H) mode)
      (referenceBasis (H := H) mode)

theorem referenceRankOne_norm
    (time : HeatTime) (mode : referenceIndex (H := H)) :
    ‖referenceRankOne (H := H) time mode‖ =
      referenceWeight (H := H) time mode := by
  rw [referenceRankOne, norm_smul, InnerProductSpace.norm_rankOne,
    (HilbertBasis.orthonormal (referenceBasis (H := H))).1 mode,
    mul_one, Real.norm_eq_abs,
    abs_of_pos (referenceWeight_pos (H := H) time mode)]
  ring

theorem referenceRankOne_norm_summable (time : HeatTime) :
    Summable
      (fun mode => ‖referenceRankOne (H := H) time mode‖) := by
  simpa only [referenceRankOne_norm] using
    referenceWeight_summable (H := H) time

theorem referenceRankOne_summable (time : HeatTime) :
    Summable (referenceRankOne (H := H) time) :=
  Summable.of_norm (referenceRankOne_norm_summable (H := H) time)

/-- The unconditional nuclear reference regulator. -/
def referenceOperator (time : HeatTime) : H →L[Real] H :=
  ∑' mode, referenceRankOne (H := H) time mode

private theorem referenceRankOne_isCompact
    (time : HeatTime) (mode : referenceIndex (H := H)) :
    IsCompactOperator (referenceRankOne (H := H) time mode) := by
  rw [referenceRankOne]
  have hCompact :
      IsCompactOperator
        (InnerProductSpace.rankOne Real
          (referenceBasis (H := H) mode)
          (referenceBasis (H := H) mode)) := by
    rw [InnerProductSpace.rankOne_def']
    exact
      (isCompactOperator_of_locallyCompactSpace_dom
        (innerSL Real (referenceBasis (H := H) mode))).clm_comp
          (ContinuousLinearMap.toSpanSingleton Real
            (referenceBasis (H := H) mode))
  exact hCompact.smul (referenceWeight (H := H) time mode)

theorem referenceOperator_isCompact (time : HeatTime) :
    IsCompactOperator (referenceOperator (H := H) time) := by
  letI : DecidableEq (referenceIndex (H := H)) := Classical.decEq _
  refine isCompactOperator_of_tendsto
    (l := (SummationFilter.unconditional
      (referenceIndex (H := H))).filter)
    (F := fun modes : Finset (referenceIndex (H := H)) =>
      ∑ mode ∈ modes, referenceRankOne (H := H) time mode)
    (f := referenceOperator (H := H) time)
    (referenceRankOne_summable (H := H) time).hasSum ?_
  filter_upwards [] with modes
  refine Finset.sum_induction
    (fun mode => referenceRankOne (H := H) time mode)
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro mode _
  exact referenceRankOne_isCompact (H := H) time mode

/-- Explicit nuclear certificate for the reference regulator. -/
structure ReferenceNuclearCertificate (time : HeatTime) where
  components : referenceIndex (H := H) → (H →L[Real] H)
  summable_norm : Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    referenceOperator (H := H) time = ∑' mode, components mode

def referenceNuclearCertificate (time : HeatTime) :
    ReferenceNuclearCertificate (H := H) time where
  components := referenceRankOne (H := H) time
  summable_norm := referenceRankOne_norm_summable (H := H) time
  operator_eq_tsum := rfl

private theorem weightedRankOneTsum_inner_basis
    {I : Type*} [DecidableEq I]
    (basis : HilbertBasis I Real H) (weight : I → Real)
    (hOperators :
      Summable
        (fun mode =>
          weight mode •
            InnerProductSpace.rankOne Real
              (basis mode) (basis mode)))
    (state : H) (mode : I) :
    inner Real (basis mode)
        ((∑' other,
          weight other •
            InnerProductSpace.rankOne Real
              (basis other) (basis other)) state) =
      weight mode * inner Real (basis mode) state := by
  let coordinate : (H →L[Real] H) →L[Real] Real :=
    (innerSL Real (basis mode)).comp
      (ContinuousLinearMap.apply Real H state)
  rw [show
      inner Real (basis mode)
          ((∑' other,
            weight other •
              InnerProductSpace.rankOne Real
                (basis other) (basis other)) state) =
        ∑' other,
          inner Real (basis mode)
            ((weight other •
              InnerProductSpace.rankOne Real
                (basis other) (basis other)) state) by
    simpa only [coordinate, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply] using
      coordinate.map_tsum hOperators]
  rw [tsum_eq_single mode]
  · have hInner :=
      (orthonormal_iff_ite.mp
        (HilbertBasis.orthonormal basis)) mode mode
    rw [smul_apply, InnerProductSpace.rankOne_apply,
      inner_smul_right, inner_smul_right, hInner]
    simp
  · intro other hOther
    have hOrtho :
        inner Real (basis mode) (basis other) = 0 :=
      (HilbertBasis.orthonormal basis).inner_eq_zero (Ne.symm hOther)
    rw [smul_apply, InnerProductSpace.rankOne_apply,
      inner_smul_right, inner_smul_right, hOrtho]
    simp

theorem referenceOperator_inner_basis
    (time : HeatTime) (state : H)
    (mode : referenceIndex (H := H)) :
    inner Real (referenceBasis (H := H) mode)
        (referenceOperator (H := H) time state) =
      referenceWeight (H := H) time mode *
        inner Real (referenceBasis (H := H) mode) state := by
  have hOperators :
      Summable
        (fun other =>
          referenceWeight (H := H) time other •
            InnerProductSpace.rankOne Real
              (referenceBasis (H := H) other)
              (referenceBasis (H := H) other)) := by
    change Summable (referenceRankOne (H := H) time)
    exact referenceRankOne_summable (H := H) time
  unfold referenceOperator referenceRankOne
  exact weightedRankOneTsum_inner_basis
    (referenceBasis (H := H))
    (referenceWeight (H := H) time)
    hOperators
    state mode

theorem referenceOperator_injective (time : HeatTime) :
    Function.Injective (referenceOperator (H := H) time) := by
  intro first second hEqual
  apply (referenceBasis (H := H)).repr.injective
  ext mode
  rw [(referenceBasis (H := H)).repr_apply_apply,
    (referenceBasis (H := H)).repr_apply_apply]
  have hCoordinate :=
    congrArg
      (fun state =>
        inner Real (referenceBasis (H := H) mode) state)
      hEqual
  rw [referenceOperator_inner_basis (H := H),
    referenceOperator_inner_basis (H := H)] at hCoordinate
  exact mul_left_cancel₀
    (ne_of_gt (referenceWeight_pos (H := H) time mode))
    hCoordinate

end SeparableHilbertReference

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatSecondCountable :
    SecondCountableTopology (EffectiveThroat period hPeriod) :=
  (mappingTorusMk_isCoveringMap
      (fixedEquatorData period hPeriod)).isQuotientMap
    (mappingTorusMk_surjective (fixedEquatorData period hPeriod))
  |>.secondCountableTopology
      (mappingTorusMk_isCoveringMap
        (fixedEquatorData period hPeriod)).isOpenMap

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance lpTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance llMeasureIsFinite
    (llData : PositiveLLH1Data period hPeriod) :
    IsFiniteMeasure llData.mu :=
  llData.finiteMeasure

local instance llMeasureIsSeparable
    (llData : PositiveLLH1Data period hPeriod) :
    MeasureTheory.IsSeparable llData.mu := by
  infer_instance

local instance llFluxL2SecondCountable
    (llData : PositiveLLH1Data period hPeriod) :
    SecondCountableTopology (LLFluxL2 period hPeriod llData) := by
  infer_instance

/-- Public separability witness which downstream LL gates can install locally. -/
@[reducible] def llFluxL2SeparableSpace
    (llData : PositiveLLH1Data period hPeriod) :
    TopologicalSpace.SeparableSpace
      (LLFluxL2 period hPeriod llData) :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

local instance llFluxL2Separable
    (llData : PositiveLLH1Data period hPeriod) :
    TopologicalSpace.SeparableSpace
      (LLFluxL2 period hPeriod llData) :=
  llFluxL2SeparableSpace period hPeriod llData

/-- Unconditional compact, nuclear, injective reference regulator on LL flux
`L2`.  This conclusion uses only separability and the Hilbert structure. -/
theorem programPLL2_reference_regulator_gate
    (llData : PositiveLLH1Data period hPeriod)
    (time : HeatTime) :
    IsCompactOperator
        (referenceOperator
          (H := LLFluxL2 period hPeriod llData) time) ∧
      Function.Injective
        (referenceOperator
          (H := LLFluxL2 period hPeriod llData) time) ∧
      Nonempty
        (ReferenceNuclearCertificate
          (H := LLFluxL2 period hPeriod llData) time) := by
  exact ⟨referenceOperator_isCompact
      (H := LLFluxL2 period hPeriod llData) time,
    referenceOperator_injective
      (H := LLFluxL2 period hPeriod llData) time,
    ⟨referenceNuclearCertificate
      (H := LLFluxL2 period hPeriod llData) time⟩⟩

end
end P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D
end JanusFormal
