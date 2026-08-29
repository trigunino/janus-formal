import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJetSubstitutionC2

/-!
# Bounded second-fiber-jet substitution

The twice Frechet differentiable substitution theorem for a compatible
value/first/second fiber jet whose second component is uniformly continuous.
This is the derivative-optimal companion to the order-three Lipschitz helper:
it requires no fourth spatial derivative and contains no geometric data.
-/

namespace JanusFormal
namespace P0EFTJanusBoundedFiberJet2SubstitutionC2

open Asymptotics Filter Set
open scoped BoundedContinuousFunction Topology
open JanusFormal.P0EFTJanusBoundedFiberJetSubstitutionC2

noncomputable section

private abbrev canonicalRealAddCommGroup : AddCommGroup Real :=
  NormedField.toNormedCommRing.toAddCommGroup

private abbrev canonicalRealModule : Module Real Real :=
  (NormedAlgebra.toNormedSpace Real).toModule

attribute [local instance 10000] canonicalRealAddCommGroup canonicalRealModule

variable (X : Type*) [PseudoMetricSpace X]

private abbrev RealHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  HasDerivAt function derivative point

abbrev Field := BoundedContinuousFunction (X × Real) Real
abbrev Ambient := Fin 3 → Field X

/-- The product of two bounded uniformly continuous real fields is uniformly
continuous. Boundedness is supplied by the existing sup-norm fields. -/
theorem field_mul_uniformContinuous
    (first second : Field X)
    (hFirst : UniformContinuous first)
    (hSecond : UniformContinuous second) :
    UniformContinuous (first * second) := by
  let paired : X × Real → Real × Real := fun point =>
    (first point, second point)
  have hPaired : UniformContinuous paired := hFirst.prodMk hSecond
  have hRange : Bornology.IsBounded (Set.range paired) := by
    apply Bornology.IsBounded.subset
      (first.isBounded_range.prod second.isBounded_range)
    rintro _ ⟨point, rfl⟩
    exact ⟨Set.mem_range_self point, Set.mem_range_self point⟩
  have hMultiply := hRange.uniformContinuousOn_smul
  have hComposed := hMultiply.comp hPaired.uniformContinuousOn
    (Set.mapsTo_range paired Set.univ)
  rw [uniformContinuousOn_univ] at hComposed
  change UniformContinuous (fun point => first point * second point)
  simpa [Function.comp_def, Function.uncurry, paired] using hComposed

def jet2Submodule : Submodule Real (Ambient X) where
  carrier := { jet |
    (∀ point fiber, RealHasDerivAt
      (fun varied => jet 0 (point, varied)) (jet 1 (point, fiber)) fiber) ∧
    (∀ point fiber, RealHasDerivAt
      (fun varied => jet 1 (point, varied)) (jet 2 (point, fiber)) fiber) ∧
    UniformContinuous (jet 2) }
  zero_mem' := by
    refine ⟨?_, ?_, uniformContinuous_const⟩
    · intro point fiber
      simpa using hasDerivAt_const fiber (0 : Real)
    · intro point fiber
      simpa using hasDerivAt_const fiber (0 : Real)
  add_mem' := by
    rintro first second ⟨hFirst0, hFirst1, hFirst2⟩
      ⟨hSecond0, hSecond1, hSecond2⟩
    refine ⟨?_, ?_, hFirst2.add hSecond2⟩
    · intro point fiber
      change RealHasDerivAt
        ((fun varied => first 0 (point, varied)) +
          fun varied => second 0 (point, varied))
        (first 1 (point, fiber) + second 1 (point, fiber)) fiber
      exact (hFirst0 point fiber).add (hSecond0 point fiber)
    · intro point fiber
      change RealHasDerivAt
        ((fun varied => first 1 (point, varied)) +
          fun varied => second 1 (point, varied))
        (first 2 (point, fiber) + second 2 (point, fiber)) fiber
      exact (hFirst1 point fiber).add (hSecond1 point fiber)
  smul_mem' := by
    rintro scalar jet ⟨hJet0, hJet1, hJet2⟩
    refine ⟨?_, ?_, hJet2.const_smul scalar⟩
    · intro point fiber
      change RealHasDerivAt
        (scalar • fun varied => jet 0 (point, varied))
        (scalar • jet 1 (point, fiber)) fiber
      exact (hJet0 point fiber).const_smul scalar
    · intro point fiber
      change RealHasDerivAt
        (scalar • fun varied => jet 1 (point, varied))
        (scalar • jet 2 (point, fiber)) fiber
      exact (hJet1 point fiber).const_smul scalar

/-- The two derivative relations, without the separately supplied uniform
continuity certificate for the top derivative. -/
def jet2DerivativeSubmodule : Submodule Real (Ambient X) where
  carrier := { jet |
    (∀ point fiber, RealHasDerivAt
      (fun varied => jet 0 (point, varied)) (jet 1 (point, fiber)) fiber) ∧
    (∀ point fiber, RealHasDerivAt
      (fun varied => jet 1 (point, varied)) (jet 2 (point, fiber)) fiber) }
  zero_mem' := by
    exact ⟨fun _ fiber => by simpa using hasDerivAt_const fiber (0 : Real),
      fun _ fiber => by simpa using hasDerivAt_const fiber (0 : Real)⟩
  add_mem' := by
    rintro first second ⟨hFirst0, hFirst1⟩ ⟨hSecond0, hSecond1⟩
    exact ⟨fun point fiber => by
        change RealHasDerivAt
          ((fun varied => first 0 (point, varied)) +
            fun varied => second 0 (point, varied))
          (first 1 (point, fiber) + second 1 (point, fiber)) fiber
        exact (hFirst0 point fiber).add (hSecond0 point fiber),
      fun point fiber => by
        change RealHasDerivAt
          ((fun varied => first 1 (point, varied)) +
            fun varied => second 1 (point, varied))
          (first 2 (point, fiber) + second 2 (point, fiber)) fiber
        exact (hFirst1 point fiber).add (hSecond1 point fiber)⟩
  smul_mem' := by
    rintro scalar jet ⟨hJet0, hJet1⟩
    exact ⟨fun point fiber => by
        change RealHasDerivAt
          (scalar • fun varied => jet 0 (point, varied))
          (scalar • jet 1 (point, fiber)) fiber
        exact (hJet0 point fiber).const_smul scalar,
      fun point fiber => by
        change RealHasDerivAt
          (scalar • fun varied => jet 1 (point, varied))
          (scalar • jet 2 (point, fiber)) fiber
        exact (hJet1 point fiber).const_smul scalar⟩

/-- Compatibility of the first two derivative levels is closed under uniform
convergence of all three components. -/
theorem jet2DerivativeSubmodule_isClosed :
    IsClosed (jet2DerivativeSubmodule X : Set (Ambient X)) := by
  refine IsSeqClosed.isClosed fun sequence jet hSequence hConverges => ?_
  have hComponent (index : Fin 3) :
      Tendsto (fun n => sequence n index) atTop (nhds (jet index)) :=
    tendsto_pi_nhds.mp hConverges index
  have hUniform (index : Fin 3) :
      TendstoUniformly (fun n => sequence n index) (jet index) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (hComponent index)
  refine ⟨fun point fiber => ?_, fun point fiber => ?_⟩
  · exact hasDerivAt_of_tendstoUniformly
      ((hUniform 1).comp (fun varied => (point, varied)))
      (Filter.Eventually.of_forall fun n varied =>
        (hSequence n).1 point varied)
      (fun varied => (hUniform 0).tendsto_at (point, varied)) fiber
  · exact hasDerivAt_of_tendstoUniformly
      ((hUniform 2).comp (fun varied => (point, varied)))
      (Filter.Eventually.of_forall fun n varied =>
        (hSequence n).2 point varied)
      (fun varied => (hUniform 1).tendsto_at (point, varied)) fiber

abbrev Jet2 := jet2Submodule X

private theorem scalarImageSubBound
    (value derivative : Real → Real)
    (hDerivative : ∀ fiber,
      RealHasDerivAt value (derivative fiber) fiber)
    (bound : Real) (hBound : ∀ fiber, ‖derivative fiber‖ ≤ bound)
    (fiber increment : Real) :
    ‖value (fiber + increment) - value fiber‖ ≤
      bound * ‖increment‖ := by
  have hEstimate :=
    (convex_segment fiber (fiber + increment)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := value) (f' := derivative)
      (fun current _ => (hDerivative current).hasDerivWithinAt)
      (fun current _ => hBound current)
      (left_mem_segment Real fiber (fiber + increment))
      (right_mem_segment Real fiber (fiber + increment))
  simpa only [add_sub_cancel_left] using hEstimate

/-- The canonical compactified `arctan` coordinate is uniformly continuous. -/
theorem arctanCompactFiberMap_uniformContinuous :
    UniformContinuous
      (arctanCompactFiberMap : Real → ArctanCompactFiber) := by
  rw [Metric.uniformContinuous_iff]
  intro epsilon hEpsilon
  refine ⟨epsilon, hEpsilon, ?_⟩
  intro first second hDistance
  change dist (Real.arctan first) (Real.arctan second) < epsilon
  rw [dist_eq_norm]
  have hDerivativeBound : ∀ point : Real,
      ‖1 / (1 + point ^ 2)‖ ≤ (1 : Real) := by
    intro point
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg point])
  have hBound := scalarImageSubBound Real.arctan
    (fun point => 1 / (1 + point ^ 2)) Real.hasDerivAt_arctan
    1 hDerivativeBound second (first - second)
  have hShift : second + (first - second) = first := by ring
  rw [hShift, one_mul] at hBound
  exact hBound.trans_lt (by simpa only [dist_eq_norm] using hDistance)

/-- Pulling a continuous scalar on the compact latitude strip through the
canonical `arctan` input yields a uniformly continuous bounded field. -/
theorem boundedArctanCompactPullback_uniformContinuous
    [CompactSpace X]
    (field : C(X × ArctanCompactFiber, Real)) :
    UniformContinuous (boundedArctanCompactPullbackCLM X field) := by
  have hField : UniformContinuous field :=
    CompactSpace.uniformContinuous_of_continuous field.continuous
  have hInput : UniformContinuous (arctanCompactFiberInput X) :=
    uniformContinuous_fst.prodMk
      (arctanCompactFiberMap_uniformContinuous.comp uniformContinuous_snd)
  exact hField.comp hInput

/-- Each of the first three scalar `arctan` jet components is uniformly
continuous on the raw product, using the next bounded derivative. -/
theorem boundedFiberArctanJet3_component_uniformContinuous
    (index : Fin 3) :
    UniformContinuous
      ((boundedFiberArctanJet3 X).1 index.castSucc) := by
  rw [Metric.uniformContinuous_iff]
  intro epsilon hEpsilon
  let derivativeBound := ‖(boundedFiberArctanJet3 X).1 index.succ‖
  have hDenominator : 0 < derivativeBound + 1 := by
    dsimp only [derivativeBound]
    positivity
  refine ⟨epsilon / (derivativeBound + 1),
    div_pos hEpsilon hDenominator, ?_⟩
  intro first second hDistance
  have hFiberDistance : ‖first.2 - second.2‖ <
      epsilon / (derivativeBound + 1) := by
    calc
      ‖first.2 - second.2‖ = dist first.2 second.2 := by rw [dist_eq_norm]
      _ ≤ dist first second := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ < epsilon / (derivativeBound + 1) := hDistance
  have hDerivative : ∀ fiber,
      RealHasDerivAt
        (fun varied => (boundedFiberArctanJet3 X).1 index.castSucc
          (second.1, varied))
        ((boundedFiberArctanJet3 X).1 index.succ
          (second.1, fiber)) fiber := by
    fin_cases index
    · exact (boundedFiberArctanJet3 X).2.1 second.1
    · exact (boundedFiberArctanJet3 X).2.2.1 second.1
    · exact (boundedFiberArctanJet3 X).2.2.2 second.1
  have hScalar := scalarImageSubBound
    (fun varied => (boundedFiberArctanJet3 X).1 index.castSucc
      (second.1, varied))
    (fun varied => (boundedFiberArctanJet3 X).1 index.succ
      (second.1, varied)) hDerivative derivativeBound
    (fun fiber => (boundedFiberArctanJet3 X).1 index.succ
      |>.norm_coe_le_norm (second.1, fiber))
    second.2 (first.2 - second.2)
  have hShift : second.2 + (first.2 - second.2) = first.2 := by ring
  rw [hShift] at hScalar
  have hBaseIndependence :
      (boundedFiberArctanJet3 X).1 index.castSucc first =
        (boundedFiberArctanJet3 X).1 index.castSucc (second.1, first.2) := by
    fin_cases index <;> rfl
  rw [hBaseIndependence, dist_eq_norm]
  exact hScalar.trans_lt (calc
    derivativeBound * ‖first.2 - second.2‖ ≤
        (derivativeBound + 1) * ‖first.2 - second.2‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < epsilon := by
      simpa only [mul_comm] using
        (lt_div_iff₀ hDenominator).mp hFiberDistance)

private theorem scalarTaylorOneBound
    (value first second : Real → Real)
    (hValue : ∀ fiber, RealHasDerivAt value (first fiber) fiber)
    (hFirst : ∀ fiber, RealHasDerivAt first (second fiber) fiber)
    (bound : Real) (hBound : ∀ fiber, ‖second fiber‖ ≤ bound)
    (fiber increment : Real) :
    ‖value (fiber + increment) - value fiber - first fiber * increment‖ ≤
      bound * ‖increment‖ ^ 2 := by
  let remainder : Real → Real := fun current =>
    value (fiber + current) - value fiber - first fiber * current
  let remainderDerivative : Real → Real := fun current =>
    first (fiber + current) - first fiber
  have hRemainder : ∀ current,
      RealHasDerivAt remainder (remainderDerivative current) current := by
    intro current
    have hShift : RealHasDerivAt (fun varied => fiber + varied) 1 current := by
      change RealHasDerivAt ((fun _ : Real => fiber) + id) 1 current
      simpa only [zero_add] using
        (hasDerivAt_const current fiber).add (hasDerivAt_id current)
    have hValueShift := (hValue (fiber + current)).comp current hShift
    have hLinear := (hasDerivAt_const current (first fiber)).mul
      (hasDerivAt_id current)
    change RealHasDerivAt
      (((value ∘ fun varied => fiber + varied) -
          fun _ : Real => value fiber) -
        (fun _ : Real => first fiber) * id)
      (first (fiber + current) - first fiber) current
    simpa only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, id_eq,
      mul_one, zero_mul, zero_add, sub_zero] using
      (hValueShift.sub (hasDerivAt_const current (value fiber)) |>.sub hLinear)
  have hRemainderBound : ∀ current ∈ segment Real 0 increment,
      ‖remainderDerivative current‖ ≤ bound * ‖increment‖ := by
    intro current hCurrent
    have hFirstDifference := scalarImageSubBound first second hFirst bound
      hBound fiber current
    have hCurrentNorm : ‖current‖ ≤ ‖increment‖ := by
      simpa using norm_sub_le_of_mem_segment hCurrent
    exact hFirstDifference.trans
      (mul_le_mul_of_nonneg_left hCurrentNorm
        (le_trans (norm_nonneg _) (hBound fiber)))
  have hEstimate :=
    (convex_segment (0 : Real) increment).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := remainder) (f' := remainderDerivative)
      (fun current _ => (hRemainder current).hasDerivWithinAt)
      hRemainderBound
      (left_mem_segment Real (0 : Real) increment)
      (right_mem_segment Real (0 : Real) increment)
  have hRemainderZero : remainder 0 = 0 := by simp [remainder]
  rw [hRemainderZero, sub_zero] at hEstimate
  convert hEstimate using 1 <;>
    simp only [remainder, Real.norm_eq_abs, pow_two, sub_zero] <;> ring

private theorem scalarTaylorOneModulus
    (value derivative : Real → Real)
    (hDerivative : ∀ fiber,
      RealHasDerivAt value (derivative fiber) fiber)
    (bound : Real) (hBoundNonnegative : 0 ≤ bound)
    (fiber increment : Real)
    (hBound : ∀ current ∈ segment Real 0 increment,
      ‖derivative (fiber + current) - derivative fiber‖ ≤ bound) :
    ‖value (fiber + increment) - value fiber -
        derivative fiber * increment‖ ≤ bound * ‖increment‖ := by
  let remainder : Real → Real := fun current =>
    value (fiber + current) - value fiber - derivative fiber * current
  let remainderDerivative : Real → Real := fun current =>
    derivative (fiber + current) - derivative fiber
  have hRemainder : ∀ current,
      RealHasDerivAt remainder (remainderDerivative current) current := by
    intro current
    have hShift : RealHasDerivAt (fun varied => fiber + varied) 1 current := by
      change RealHasDerivAt ((fun _ : Real => fiber) + id) 1 current
      simpa only [zero_add] using
        (hasDerivAt_const current fiber).add (hasDerivAt_id current)
    have hValueShift := (hDerivative (fiber + current)).comp current hShift
    have hLinear := (hasDerivAt_const current (derivative fiber)).mul
      (hasDerivAt_id current)
    change RealHasDerivAt
      (((value ∘ fun varied => fiber + varied) -
          fun _ : Real => value fiber) -
        (fun _ : Real => derivative fiber) * id)
      (derivative (fiber + current) - derivative fiber) current
    simpa only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, id_eq,
      mul_one, zero_mul, zero_add, sub_zero] using
      (hValueShift.sub (hasDerivAt_const current (value fiber)) |>.sub hLinear)
  have hEstimate :=
    (convex_segment (0 : Real) increment).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := remainder) (f' := remainderDerivative)
      (fun current _ => (hRemainder current).hasDerivWithinAt)
      (fun current hCurrent => hBound current hCurrent)
      (left_mem_segment Real (0 : Real) increment)
      (right_mem_segment Real (0 : Real) increment)
  have hRemainderZero : remainder 0 = 0 := by
    simp [remainder]
  rw [hRemainderZero, sub_zero] at hEstimate
  simpa only [remainder, Real.norm_eq_abs, sub_zero] using hEstimate

private theorem jet2SubstitutionTaylorOneLittleO
    (jet : Jet2 X) (graph : BoundedContinuousFunction X Real) :
    (fun increment : BoundedContinuousFunction X Real =>
      boundedFiberSubstitution X
          (jet.1 1) (graph + increment) -
        boundedFiberSubstitution X
          (jet.1 1) graph -
        boundedFiberSubstitution X
          (jet.1 2) graph * increment) =o[nhds 0]
      (fun increment => increment) := by
  rw [isLittleO_iff]
  intro coefficient hCoefficient
  obtain ⟨radius, hRadius, hUniform⟩ :=
    Metric.uniformContinuous_iff.mp jet.2.2.2 coefficient hCoefficient
  filter_upwards [Metric.ball_mem_nhds
    (0 : BoundedContinuousFunction X Real) hRadius] with increment hIncrement
  rw [BoundedContinuousFunction.norm_le
    (mul_nonneg hCoefficient.le (norm_nonneg increment))]
  intro point
  have hPoint := scalarTaylorOneModulus
    (fun fiber => jet.1 1 (point, fiber))
    (fun fiber => jet.1 2 (point, fiber))
    (fun fiber => jet.2.2.1 point fiber)
    coefficient hCoefficient.le (graph point) (increment point) (by
      intro current hCurrent
      exact (hUniform (a := (point, graph point + current))
        (b := (point, graph point)) (by
          rw [dist_prod_same_left, Real.dist_eq]
          have hCurrentNorm : ‖current‖ ≤ ‖increment point‖ := by
            simpa using norm_sub_le_of_mem_segment hCurrent
          have hIncrementPoint : ‖increment point‖ ≤ ‖increment‖ :=
            increment.norm_coe_le_norm point
          have hIncrementNorm : ‖increment‖ < radius := by
            simpa only [Metric.mem_ball, dist_zero_right] using hIncrement
          simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
            (hCurrentNorm.trans hIncrementPoint).trans_lt hIncrementNorm)).le)
  change ‖jet.1 1 (point, graph point + increment point) -
      jet.1 1 (point, graph point) -
      jet.1 2 (point, graph point) * increment point‖ ≤ _
  exact hPoint.trans (mul_le_mul_of_nonneg_left
    (increment.norm_coe_le_norm point) hCoefficient.le)

private theorem boundedFiberSubstitution_continuousAt_graph
    (field : Field X) (hUniform : UniformContinuous field)
    (graph : BoundedContinuousFunction X Real) :
    ContinuousAt
      (fun varied => boundedFiberSubstitution X field varied) graph := by
  rw [Metric.continuousAt_iff]
  intro epsilon hEpsilon
  have hHalf : 0 < epsilon / 2 := half_pos hEpsilon
  obtain ⟨radius, hRadius, hUniformRadius⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (epsilon / 2) hHalf
  refine ⟨radius, hRadius, ?_⟩
  intro varied hVaried
  rw [dist_eq_norm]
  have hNormLe :
      ‖boundedFiberSubstitution X field varied -
        boundedFiberSubstitution X field graph‖ ≤ epsilon / 2 := by
    rw [BoundedContinuousFunction.norm_le hHalf.le]
    intro point
    change ‖field (point, varied point) - field (point, graph point)‖ ≤ _
    rw [← dist_eq_norm]
    exact (hUniformRadius (a := (point, varied point))
      (b := (point, graph point)) (by
        rw [dist_prod_same_left]
        rw [dist_eq_norm]
        calc
          ‖varied point - graph point‖ ≤ ‖varied - graph‖ :=
            (varied - graph).norm_coe_le_norm point
          _ = dist varied graph := by rw [dist_eq_norm]
          _ < radius := hVaried)).le
  exact hNormLe.trans_lt (half_lt_self hEpsilon)

def jet2ComponentCLM (index : Fin 3) :
    Jet2 X →L[Real] Field X :=
  (ContinuousLinearMap.proj index).comp (jet2Submodule X).subtypeL

@[simp]
theorem jet2ComponentCLM_apply (index : Fin 3) (jet : Jet2 X) :
    jet2ComponentCLM X index jet = jet.1 index := rfl

theorem jet2_component_norm_le (jet : Jet2 X) (index : Fin 3) :
    ‖jet.1 index‖ ≤ ‖jet‖ := by
  change ‖jet.1 index‖ ≤ ‖jet.1‖
  exact norm_le_pi_norm jet.1 index

theorem jet2_substitution_taylor_zero
    (jet : Jet2 X)
    (graph increment : BoundedContinuousFunction X Real) :
    ‖boundedFiberSubstitution X (jet.1 0) (graph + increment) -
        boundedFiberSubstitution X (jet.1 0) graph -
        boundedFiberSubstitution X (jet.1 1) graph * increment‖ ≤
      ‖jet.1 2‖ * ‖increment‖ ^ 2 := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg
    (norm_nonneg _) (sq_nonneg _))]
  intro point
  have hPoint := scalarTaylorOneBound
      (fun fiber => jet.1 0 (point, fiber))
      (fun fiber => jet.1 1 (point, fiber))
      (fun fiber => jet.1 2 (point, fiber))
      (fun fiber => jet.2.1 point fiber)
      (fun fiber => jet.2.2.1 point fiber) ‖jet.1 2‖
      (fun fiber => (jet.1 2).norm_coe_le_norm (point, fiber))
      (graph point) (increment point)
  exact hPoint.trans (by
    gcongr
    exact increment.norm_coe_le_norm point)

theorem jet2_substitution_lipschitz
    (jet : Jet2 X) (index : Fin 2)
    (graph increment : BoundedContinuousFunction X Real) :
    ‖boundedFiberSubstitution X (jet.1 index.castSucc) (graph + increment) -
        boundedFiberSubstitution X (jet.1 index.castSucc) graph‖ ≤
      ‖jet.1 index.succ‖ * ‖increment‖ := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg
    (norm_nonneg _) (norm_nonneg _))]
  intro point
  have hDerivative : ∀ fiber,
      RealHasDerivAt
        (fun varied => jet.1 index.castSucc (point, varied))
        (jet.1 index.succ (point, fiber)) fiber := by
    fin_cases index
    · exact jet.2.1 point
    · exact jet.2.2.1 point
  have hPoint := scalarImageSubBound
      (fun fiber => jet.1 index.castSucc (point, fiber))
      (fun fiber => jet.1 index.succ (point, fiber))
      hDerivative ‖jet.1 index.succ‖
      (fun fiber => (jet.1 index.succ).norm_coe_le_norm (point, fiber))
      (graph point) (increment point)
  exact hPoint.trans (by
    gcongr
    exact increment.norm_coe_le_norm point)

private abbrev Graph := BoundedContinuousFunction X Real
private abbrev Source := Jet2 X × Graph X

local instance sourceNormedAddCommGroup :
    NormedAddCommGroup (Source X) := inferInstance

local instance sourceNormedSpace :
    NormedSpace Real (Source X) := inferInstance

local instance sourceTopologicalSpace : TopologicalSpace (Source X) :=
  (sourceNormedAddCommGroup (X := X)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance sourceAddCommGroup : AddCommGroup (Source X) :=
  (sourceNormedAddCommGroup (X := X)).toAddCommGroup

local instance sourceAddCommMonoid : AddCommMonoid (Source X) :=
  (sourceNormedAddCommGroup (X := X)).toAddCommGroup.toAddCommMonoid

local instance sourceModule : Module Real (Source X) :=
  (sourceNormedSpace (X := X)).toModule

local instance derivativeNormedAddCommGroup :
    NormedAddCommGroup (Source X →L[Real] Graph X) := inferInstance

local instance derivativeNormedSpace :
    NormedSpace Real (Source X →L[Real] Graph X) := inferInstance

local instance derivativeTopologicalSpace :
    TopologicalSpace (Source X →L[Real] Graph X) :=
  (derivativeNormedAddCommGroup (X := X)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance derivativeAddCommGroup :
    AddCommGroup (Source X →L[Real] Graph X) :=
  (derivativeNormedAddCommGroup (X := X)).toAddCommGroup

local instance derivativeAddCommMonoid :
    AddCommMonoid (Source X →L[Real] Graph X) :=
  (derivativeNormedAddCommGroup (X := X)).toAddCommGroup.toAddCommMonoid

local instance derivativeModule :
    Module Real (Source X →L[Real] Graph X) :=
  (derivativeNormedSpace (X := X)).toModule

def evaluation (current : Source X) : Graph X :=
  boundedFiberSubstitution X (current.1.1 0) current.2

def evaluationFDeriv (current : Source X) :
    Source X →L[Real] Graph X :=
  ((JanusFormal.P0EFTJanusBoundedFiberJetSubstitutionC2.boundedFiberSubstitutionFieldCLM
      X current.2).comp
      ((jet2ComponentCLM X 0).comp
        (ContinuousLinearMap.fst Real (Jet2 X) (Graph X)))) +
    ((ContinuousLinearMap.mul Real (Graph X)
      (boundedFiberSubstitution X (current.1.1 1) current.2)).comp
        (ContinuousLinearMap.snd Real (Jet2 X) (Graph X)))

@[simp]
theorem evaluationFDeriv_apply (current increment : Source X) :
    evaluationFDeriv X current increment =
      boundedFiberSubstitution X (increment.1.1 0) current.2 +
        boundedFiberSubstitution X (current.1.1 1) current.2 * increment.2 :=
  rfl

private theorem evaluation_increment (current increment : Source X) :
    evaluation X (current + increment) - evaluation X current -
        evaluationFDeriv X current increment =
      (boundedFiberSubstitution X (current.1.1 0)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 0) current.2 -
        boundedFiberSubstitution X (current.1.1 1) current.2 * increment.2) +
      (boundedFiberSubstitution X (increment.1.1 0)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (increment.1.1 0) current.2) := by
  rw [evaluationFDeriv_apply]
  ext point
  change
    (current.1.1 0 (point, current.2 point + increment.2 point) +
        increment.1.1 0 (point, current.2 point + increment.2 point) -
      current.1.1 0 (point, current.2 point)) -
      (increment.1.1 0 (point, current.2 point) +
        current.1.1 1 (point, current.2 point) * increment.2 point) =
      (current.1.1 0 (point, current.2 point + increment.2 point) -
          current.1.1 0 (point, current.2 point) -
          current.1.1 1 (point, current.2 point) * increment.2 point) +
        (increment.1.1 0 (point, current.2 point + increment.2 point) -
          increment.1.1 0 (point, current.2 point))
  ring

private theorem evaluation_remainder_norm_le
    (current increment : Source X) :
    ‖evaluation X (current + increment) - evaluation X current -
        evaluationFDeriv X current increment‖ ≤
      (‖current.1‖ + 1) * ‖increment‖ ^ 2 := by
  rw [evaluation_increment]
  calc
    _ ≤
        ‖boundedFiberSubstitution X (current.1.1 0)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (current.1.1 0) current.2 -
          boundedFiberSubstitution X (current.1.1 1) current.2 * increment.2‖ +
        ‖boundedFiberSubstitution X (increment.1.1 0)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (increment.1.1 0) current.2‖ :=
      norm_add_le _ _
    _ ≤ ‖current.1.1 2‖ * ‖increment.2‖ ^ 2 +
        ‖increment.1.1 1‖ * ‖increment.2‖ :=
      add_le_add
        (jet2_substitution_taylor_zero X current.1 current.2 increment.2)
        (jet2_substitution_lipschitz X increment.1 0 current.2 increment.2)
    _ ≤ ‖current.1‖ * ‖increment‖ ^ 2 + ‖increment‖ ^ 2 := by
      apply add_le_add
      · exact mul_le_mul
          (jet2_component_norm_le X current.1 2)
          (by gcongr; exact norm_snd_le increment)
          (sq_nonneg _) (norm_nonneg current.1)
      · calc
          ‖increment.1.1 1‖ * ‖increment.2‖ ≤
              ‖increment.1‖ * ‖increment.2‖ := by
            gcongr
            exact jet2_component_norm_le X increment.1 1
          _ ≤ ‖increment‖ * ‖increment‖ := by
            exact mul_le_mul (norm_fst_le increment) (norm_snd_le increment)
              (norm_nonneg increment.2) (norm_nonneg increment)
          _ = ‖increment‖ ^ 2 := by ring
    _ = (‖current.1‖ + 1) * ‖increment‖ ^ 2 := by ring

private theorem littleO_id_of_norm_le_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (remainder : E → F) (bound : Real) (hBoundNonnegative : 0 ≤ bound)
    (hRemainder : ∀ increment,
      ‖remainder increment‖ ≤ bound * ‖increment‖ ^ 2) :
    remainder =o[nhds 0] (fun increment : E => increment) := by
  rw [isLittleO_iff]
  intro coefficient hCoefficient
  have hDenominator : 0 < bound + 1 := by linarith
  have hRadius : 0 < coefficient / (bound + 1) :=
    div_pos hCoefficient hDenominator
  filter_upwards [Metric.ball_mem_nhds (0 : E) hRadius] with increment hIncrement
  have hNorm : ‖increment‖ < coefficient / (bound + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hIncrement
  have hScaled : (bound + 1) * ‖increment‖ < coefficient := by
    simpa only [mul_comm] using (lt_div_iff₀ hDenominator).mp hNorm
  calc
    ‖remainder increment‖ ≤ bound * ‖increment‖ ^ 2 := hRemainder increment
    _ ≤ (bound + 1) * ‖increment‖ ^ 2 := by gcongr; linarith
    _ = ((bound + 1) * ‖increment‖) * ‖increment‖ := by ring
    _ ≤ coefficient * ‖increment‖ :=
      mul_le_mul_of_nonneg_right hScaled.le (norm_nonneg _)

theorem evaluation_hasFDerivAt (current : Source X) :
    HasFDerivAt (evaluation X) (evaluationFDeriv X current) current := by
  refine (hasFDerivAt_iff_isLittleO_nhds_zero
    (f := evaluation X) (f' := evaluationFDeriv X current)
    (x := current)).2 ?_
  exact littleO_id_of_norm_le_sq
    (fun increment : Source X =>
      evaluation X (current + increment) - evaluation X current -
        evaluationFDeriv X current increment)
    (‖current.1‖ + 1) (by positivity)
    (evaluation_remainder_norm_le X current)

theorem evaluation_differentiable : Differentiable Real (evaluation X) :=
  fun current => (evaluation_hasFDerivAt X current).differentiableAt

theorem evaluation_fderiv (current : Source X) :
    fderiv Real (evaluation X) current = evaluationFDeriv X current :=
  (evaluation_hasFDerivAt X current).fderiv

private def evaluationSecondLinear (current : Source X) :
    Source X →ₗ[Real] (Source X →ₗ[Real] Graph X) :=
  LinearMap.mk₂ Real
    (fun first second =>
      boundedFiberSubstitution X (second.1.1 1) current.2 * first.2 +
        boundedFiberSubstitution X (first.1.1 1) current.2 * second.2 +
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          first.2 * second.2)
    (by intro first second third; ext point
        simp [boundedFiberSubstitution]; ring)
    (by intro scalar first second; ext point
        simp [boundedFiberSubstitution]; ring)
    (by intro first second third; ext point
        simp [boundedFiberSubstitution]; ring)
    (by intro scalar first second; ext point
        simp [boundedFiberSubstitution]; ring)

def evaluationSecond (current : Source X) :
    Source X →L[Real] (Source X →L[Real] Graph X) :=
  (evaluationSecondLinear X current).mkContinuous₂
    (2 + ‖current.1.1 2‖)
    (fun (first : Source X) (second : Source X) => by
      have hFirstJet : ‖first.1.1 1‖ ≤ ‖first‖ :=
        (jet2_component_norm_le X first.1 1).trans (norm_fst_le first)
      have hSecondJet : ‖second.1.1 1‖ ≤ ‖second‖ :=
        (jet2_component_norm_le X second.1 1).trans (norm_fst_le second)
      have hFirstGraph : ‖first.2‖ ≤ ‖first‖ := norm_snd_le first
      have hSecondGraph : ‖second.2‖ ≤ ‖second‖ := norm_snd_le second
      have hCurrentField := boundedFiberSubstitution_norm_le X
        (current.1.1 2) current.2
      change
        ‖boundedFiberSubstitution X (second.1.1 1) current.2 * first.2 +
          boundedFiberSubstitution X (first.1.1 1) current.2 * second.2 +
          boundedFiberSubstitution X (current.1.1 2) current.2 *
            first.2 * second.2‖ ≤ _
      calc
        _ ≤
            ‖boundedFiberSubstitution X (second.1.1 1) current.2‖ *
                ‖first.2‖ +
              ‖boundedFiberSubstitution X (first.1.1 1) current.2‖ *
                ‖second.2‖ +
              ‖boundedFiberSubstitution X (current.1.1 2) current.2‖ *
                ‖first.2‖ * ‖second.2‖ := by
          exact (norm_add_le _ _).trans (add_le_add
            (norm_add_le _ _) (norm_mul_le _ _)) |>.trans (by
              gcongr <;> exact norm_mul_le _ _)
        _ ≤ ‖second‖ * ‖first‖ + ‖first‖ * ‖second‖ +
              ‖current.1.1 2‖ * ‖first‖ * ‖second‖ := by
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul
                ((boundedFiberSubstitution_norm_le X
                  (second.1.1 1) current.2).trans hSecondJet)
                hFirstGraph (norm_nonneg first.2) (norm_nonneg second)
            · exact mul_le_mul
                ((boundedFiberSubstitution_norm_le X
                  (first.1.1 1) current.2).trans hFirstJet)
                hSecondGraph (norm_nonneg second.2) (norm_nonneg first)
          · exact mul_le_mul
              (mul_le_mul hCurrentField hFirstGraph
                (norm_nonneg first.2) (norm_nonneg (current.1.1 2)))
              hSecondGraph (norm_nonneg second.2)
              (mul_nonneg (norm_nonneg (current.1.1 2)) (norm_nonneg first))
        _ = (2 + ‖current.1.1 2‖) * ‖first‖ * ‖second‖ := by ring)

@[simp]
theorem evaluationSecond_apply (current first second : Source X) :
    evaluationSecond X current first second =
      boundedFiberSubstitution X (second.1.1 1) current.2 * first.2 +
        boundedFiberSubstitution X (first.1.1 1) current.2 * second.2 +
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          first.2 * second.2 := by
  simp only [evaluationSecond, LinearMap.mkContinuous₂_apply,
    evaluationSecondLinear, LinearMap.mk₂_apply]

private theorem evaluationFDeriv_increment_apply
    (current increment direction : Source X) :
    (evaluationFDeriv X (current + increment) -
        evaluationFDeriv X current -
        evaluationSecond X current increment) direction =
      (boundedFiberSubstitution X (direction.1.1 0)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (direction.1.1 0) current.2 -
        boundedFiberSubstitution X (direction.1.1 1) current.2 *
          increment.2) +
      (boundedFiberSubstitution X (current.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 1) current.2 -
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          increment.2) * direction.2 +
      (boundedFiberSubstitution X (increment.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (increment.1.1 1) current.2) *
          direction.2 := by
  ext point
  simp [boundedFiberSubstitution]
  ring

private theorem evaluationFDeriv_remainder_apply_norm_le_of_middle
    (current increment direction : Source X)
    (coefficient : Real) (hCoefficient : 0 ≤ coefficient)
    (hMiddle :
      ‖boundedFiberSubstitution X (current.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 1) current.2 -
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          increment.2‖ ≤ coefficient * ‖increment.2‖) :
    ‖(evaluationFDeriv X (current + increment) -
        evaluationFDeriv X current -
        evaluationSecond X current increment) direction‖ ≤
      (2 * ‖increment‖ + coefficient) * ‖increment‖ * ‖direction‖ := by
  rw [evaluationFDeriv_increment_apply]
  have hDirectionJet2 : ‖direction.1.1 2‖ ≤ ‖direction‖ :=
    (jet2_component_norm_le X direction.1 2).trans (norm_fst_le direction)
  have hIncrementJet2 : ‖increment.1.1 2‖ ≤ ‖increment‖ :=
    (jet2_component_norm_le X increment.1 2).trans (norm_fst_le increment)
  have hIncrementGraph : ‖increment.2‖ ≤ ‖increment‖ := norm_snd_le increment
  have hDirectionGraph : ‖direction.2‖ ≤ ‖direction‖ := norm_snd_le direction
  have hIncrementGraphSq : ‖increment.2‖ ^ 2 ≤ ‖increment‖ ^ 2 := by
    gcongr
  have hFirstTerm :
      ‖direction.1.1 2‖ * ‖increment.2‖ ^ 2 ≤
        ‖direction‖ * ‖increment‖ ^ 2 :=
    mul_le_mul hDirectionJet2 hIncrementGraphSq
      (sq_nonneg ‖increment.2‖) (norm_nonneg direction)
  have hSecondTerm :
      (coefficient * ‖increment.2‖) * ‖direction.2‖ ≤
        (coefficient * ‖increment‖) * ‖direction‖ := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hIncrementGraph hCoefficient)
      hDirectionGraph (norm_nonneg direction.2)
      (mul_nonneg hCoefficient (norm_nonneg increment))
  have hThirdTerm :
      (‖increment.1.1 2‖ * ‖increment.2‖) * ‖direction.2‖ ≤
        ‖increment‖ ^ 2 * ‖direction‖ := by
    have hProduct :
        ‖increment.1.1 2‖ * ‖increment.2‖ ≤
          ‖increment‖ * ‖increment‖ :=
      mul_le_mul hIncrementJet2 hIncrementGraph
        (norm_nonneg increment.2) (norm_nonneg increment)
    exact mul_le_mul (hProduct.trans_eq (by ring)) hDirectionGraph
      (norm_nonneg direction.2) (sq_nonneg ‖increment‖)
  calc
    _ ≤
        ‖boundedFiberSubstitution X (direction.1.1 0)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (direction.1.1 0) current.2 -
          boundedFiberSubstitution X (direction.1.1 1) current.2 *
            increment.2‖ +
        ‖(boundedFiberSubstitution X (current.1.1 1)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (current.1.1 1) current.2 -
          boundedFiberSubstitution X (current.1.1 2) current.2 *
            increment.2) * direction.2‖ +
        ‖(boundedFiberSubstitution X (increment.1.1 1)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (increment.1.1 1) current.2) *
            direction.2‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        (norm_add_le _ _) le_rfl)
    _ ≤
        ‖direction.1.1 2‖ * ‖increment.2‖ ^ 2 +
        (coefficient * ‖increment.2‖) * ‖direction.2‖ +
        (‖increment.1.1 2‖ * ‖increment.2‖) * ‖direction.2‖ := by
      apply add_le_add
      · apply add_le_add
        · exact jet2_substitution_taylor_zero X
            direction.1 current.2 increment.2
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right hMiddle (norm_nonneg _))
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right
            (jet2_substitution_lipschitz X
              increment.1 1 current.2 increment.2)
            (norm_nonneg _))
    _ ≤
        ‖direction‖ * ‖increment‖ ^ 2 +
        (coefficient * ‖increment‖) * ‖direction‖ +
        ‖increment‖ ^ 2 * ‖direction‖ :=
      add_le_add (add_le_add hFirstTerm hSecondTerm) hThirdTerm
    _ = (2 * ‖increment‖ + coefficient) * ‖increment‖ *
        ‖direction‖ := by ring

private theorem evaluationFDeriv_remainder_isLittleO (current : Source X) :
    (fun increment : Source X =>
      evaluationFDeriv X (current + increment) -
        evaluationFDeriv X current -
        evaluationSecond X current increment) =o[nhds 0]
      (fun increment : Source X => increment) := by
  rw [isLittleO_iff]
  intro coefficient hCoefficient
  let smallCoefficient : Real := coefficient / 3
  have hSmallCoefficient : 0 < smallCoefficient := by
    exact div_pos hCoefficient (by norm_num)
  have hMiddleGraph : ∀ᶠ increment : Graph X in nhds 0,
      ‖boundedFiberSubstitution X (current.1.1 1)
          (current.2 + increment) -
        boundedFiberSubstitution X (current.1.1 1) current.2 -
        boundedFiberSubstitution X (current.1.1 2) current.2 * increment‖ ≤
          smallCoefficient * ‖increment‖ :=
    (isLittleO_iff.mp
      (jet2SubstitutionTaylorOneLittleO X current.1 current.2))
      hSmallCoefficient
  have hSndTendsto : Tendsto (fun increment : Source X => increment.2)
      (nhds 0) (nhds 0) := by
    have hZero : (0 : Source X).2 = (0 : Graph X) := rfl
    rw [← hZero]
    exact (ContinuousLinearMap.snd Real (Jet2 X) (Graph X)).continuous.continuousAt
  have hMiddleSource : ∀ᶠ increment : Source X in nhds 0,
      ‖boundedFiberSubstitution X (current.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 1) current.2 -
        boundedFiberSubstitution X (current.1.1 2) current.2 * increment.2‖ ≤
          smallCoefficient * ‖increment.2‖ :=
    hSndTendsto.eventually hMiddleGraph
  have hRadius : 0 < coefficient / 3 :=
    div_pos hCoefficient (by norm_num)
  filter_upwards [hMiddleSource,
    Metric.ball_mem_nhds (0 : Source X) hRadius] with increment hMiddle hBall
  have hIncrementNorm : ‖increment‖ < coefficient / 3 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hBall
  have hLinearBound :
      2 * ‖increment‖ + smallCoefficient ≤ coefficient := by
    dsimp only [smallCoefficient]
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hCoefficient.le (norm_nonneg increment))
  intro direction
  exact (evaluationFDeriv_remainder_apply_norm_le_of_middle X
    current increment direction smallCoefficient hSmallCoefficient.le
      hMiddle).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hLinearBound (norm_nonneg increment))
      (norm_nonneg direction))

theorem evaluationFDeriv_hasFDerivAt (current : Source X) :
    HasFDerivAt (evaluationFDeriv X) (evaluationSecond X current) current := by
  refine (hasFDerivAt_iff_isLittleO_nhds_zero
    (f := evaluationFDeriv X) (f' := evaluationSecond X current)
    (x := current)).2 ?_
  exact evaluationFDeriv_remainder_isLittleO X current

theorem evaluationFDeriv_differentiable :
    Differentiable Real (evaluationFDeriv X) :=
  fun current => (evaluationFDeriv_hasFDerivAt X current).differentiableAt

theorem evaluationFDeriv_fderiv (current : Source X) :
    fderiv Real (evaluationFDeriv X) current = evaluationSecond X current :=
  (evaluationFDeriv_hasFDerivAt X current).fderiv

private theorem evaluationSecond_increment_apply
    (current increment first second : Source X) :
    (evaluationSecond X (current + increment) -
        evaluationSecond X current) first second =
      (boundedFiberSubstitution X (second.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (second.1.1 1) current.2) * first.2 +
      (boundedFiberSubstitution X (first.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (first.1.1 1) current.2) * second.2 +
      (boundedFiberSubstitution X (current.1.1 2)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 2) current.2) *
          first.2 * second.2 +
      boundedFiberSubstitution X (increment.1.1 2)
          (current.2 + increment.2) * first.2 * second.2 := by
  ext point
  simp [boundedFiberSubstitution]
  ring

private def secondGraphVariationNorm
    (current increment : Source X) : Real :=
  ‖boundedFiberSubstitution X (current.1.1 2)
      (current.2 + increment.2) -
    boundedFiberSubstitution X (current.1.1 2) current.2‖

private theorem evaluationSecond_increment_apply_norm_le
    (current increment first second : Source X) :
    ‖(evaluationSecond X (current + increment) -
        evaluationSecond X current) first second‖ ≤
      (3 * ‖increment‖ + secondGraphVariationNorm X current increment) *
        ‖first‖ * ‖second‖ := by
  rw [evaluationSecond_increment_apply]
  have hIncrementGraph : ‖increment.2‖ ≤ ‖increment‖ := norm_snd_le increment
  have hFirstGraph : ‖first.2‖ ≤ ‖first‖ := norm_snd_le first
  have hSecondGraph : ‖second.2‖ ≤ ‖second‖ := norm_snd_le second
  have hFirstJet2 : ‖first.1.1 2‖ ≤ ‖first‖ :=
    (jet2_component_norm_le X first.1 2).trans (norm_fst_le first)
  have hSecondJet2 : ‖second.1.1 2‖ ≤ ‖second‖ :=
    (jet2_component_norm_le X second.1 2).trans (norm_fst_le second)
  have hIncrementJet2 : ‖increment.1.1 2‖ ≤ ‖increment‖ :=
    (jet2_component_norm_le X increment.1 2).trans (norm_fst_le increment)
  have hFirstTerm :
      ‖(boundedFiberSubstitution X (second.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (second.1.1 1) current.2) * first.2‖ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤ ‖boundedFiberSubstitution X (second.1.1 1)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (second.1.1 1) current.2‖ *
              ‖first.2‖ := norm_mul_le _ _
      _ ≤ (‖second.1.1 2‖ * ‖increment.2‖) * ‖first.2‖ :=
        mul_le_mul_of_nonneg_right
          (jet2_substitution_lipschitz X
            second.1 1 current.2 increment.2) (norm_nonneg _)
      _ ≤ (‖second‖ * ‖increment‖) * ‖first‖ :=
        mul_le_mul
          (mul_le_mul hSecondJet2 hIncrementGraph
            (norm_nonneg increment.2) (norm_nonneg second))
          hFirstGraph (norm_nonneg first.2)
          (mul_nonneg (norm_nonneg second) (norm_nonneg increment))
      _ = ‖increment‖ * ‖first‖ * ‖second‖ := by ring
  have hSecondTerm :
      ‖(boundedFiberSubstitution X (first.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (first.1.1 1) current.2) * second.2‖ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤ ‖boundedFiberSubstitution X (first.1.1 1)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (first.1.1 1) current.2‖ *
              ‖second.2‖ := norm_mul_le _ _
      _ ≤ (‖first.1.1 2‖ * ‖increment.2‖) * ‖second.2‖ :=
        mul_le_mul_of_nonneg_right
          (jet2_substitution_lipschitz X
            first.1 1 current.2 increment.2) (norm_nonneg _)
      _ ≤ (‖first‖ * ‖increment‖) * ‖second‖ :=
        mul_le_mul
          (mul_le_mul hFirstJet2 hIncrementGraph
            (norm_nonneg increment.2) (norm_nonneg first))
          hSecondGraph (norm_nonneg second.2)
          (mul_nonneg (norm_nonneg first) (norm_nonneg increment))
      _ = ‖increment‖ * ‖first‖ * ‖second‖ := by ring
  have hThirdTerm :
      ‖(boundedFiberSubstitution X (current.1.1 2)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 2) current.2) *
          first.2 * second.2‖ ≤
        secondGraphVariationNorm X current increment * ‖first‖ * ‖second‖ := by
    unfold secondGraphVariationNorm
    calc
      _ ≤ (‖boundedFiberSubstitution X (current.1.1 2)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (current.1.1 2) current.2‖ *
              ‖first.2‖) * ‖second.2‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (_ * ‖first‖) * ‖second‖ := by
        gcongr
  have hFourthTerm :
      ‖boundedFiberSubstitution X (increment.1.1 2)
          (current.2 + increment.2) * first.2 * second.2‖ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤ (‖boundedFiberSubstitution X (increment.1.1 2)
              (current.2 + increment.2)‖ * ‖first.2‖) *
            ‖second.2‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖increment.1.1 2‖ * ‖first.2‖) * ‖second.2‖ := by
        gcongr
        exact boundedFiberSubstitution_norm_le X
          (increment.1.1 2) (current.2 + increment.2)
      _ ≤ (‖increment‖ * ‖first‖) * ‖second‖ := by
        apply mul_le_mul
        · exact mul_le_mul hIncrementJet2 hFirstGraph
            (norm_nonneg first.2) (norm_nonneg increment)
        · exact hSecondGraph
        · exact norm_nonneg second.2
        · positivity
      _ = ‖increment‖ * ‖first‖ * ‖second‖ := by ring
  calc
    _ ≤
        ‖(boundedFiberSubstitution X (second.1.1 1)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (second.1.1 1) current.2) * first.2‖ +
        ‖(boundedFiberSubstitution X (first.1.1 1)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (first.1.1 1) current.2) * second.2‖ +
        ‖(boundedFiberSubstitution X (current.1.1 2)
            (current.2 + increment.2) -
          boundedFiberSubstitution X (current.1.1 2) current.2) *
            first.2 * second.2‖ +
        ‖boundedFiberSubstitution X (increment.1.1 2)
            (current.2 + increment.2) * first.2 * second.2‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ +
        ‖increment‖ * ‖first‖ * ‖second‖ +
        secondGraphVariationNorm X current increment * ‖first‖ * ‖second‖ +
        ‖increment‖ * ‖first‖ * ‖second‖ :=
      add_le_add (add_le_add (add_le_add hFirstTerm hSecondTerm)
        hThirdTerm) hFourthTerm
    _ = (3 * ‖increment‖ + secondGraphVariationNorm X current increment) *
        ‖first‖ * ‖second‖ := by ring

private theorem evaluationSecond_increment_norm_le
    (current increment : Source X) :
    ‖evaluationSecond X (current + increment) - evaluationSecond X current‖ ≤
      3 * ‖increment‖ + secondGraphVariationNorm X current increment := by
  have hVariation : 0 ≤ secondGraphVariationNorm X current increment := by
    unfold secondGraphVariationNorm
    exact norm_nonneg _
  have hBound : 0 ≤ 3 * ‖increment‖ +
      secondGraphVariationNorm X current increment :=
    add_nonneg (mul_nonneg (by norm_num) (norm_nonneg increment)) hVariation
  apply ContinuousLinearMap.opNorm_le_bound _ hBound
  intro first
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hBound (norm_nonneg first))
  intro second
  exact evaluationSecond_increment_apply_norm_le X
    current increment first second

private theorem secondGraphVariationNorm_tendsto_zero
    (current : Source X) :
    Tendsto (secondGraphVariationNorm X current) (nhds 0) (nhds 0) := by
  have hSndTendsto : Tendsto (fun increment : Source X => increment.2)
      (nhds 0) (nhds 0) := by
    have hZero : (0 : Source X).2 = (0 : Graph X) := rfl
    rw [← hZero]
    exact (ContinuousLinearMap.snd Real (Jet2 X) (Graph X)).continuous.continuousAt
  have hAddTendsto : Tendsto
      (fun graph : Graph X => current.2 + graph) (nhds 0) (nhds current.2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_id : Tendsto
        (fun graph : Graph X => current.2 + graph)
        (nhds 0) (nhds (current.2 + 0)))
  have hGraphTendsto : Tendsto
      (fun increment : Source X => current.2 + increment.2)
      (nhds 0) (nhds current.2) := hAddTendsto.comp hSndTendsto
  have hEvaluationAt := boundedFiberSubstitution_continuousAt_graph X
    (current.1.1 2) current.1.2.2.2 current.2
  have hEvaluationTendstoRaw :=
    Filter.Tendsto.comp hEvaluationAt hGraphTendsto
  have hEvaluationTendsto : Tendsto
      (fun increment : Source X => boundedFiberSubstitution X
        (current.1.1 2) (current.2 + increment.2))
      (nhds 0) (nhds (boundedFiberSubstitution X
        (current.1.1 2) current.2)) := by
    apply hEvaluationTendstoRaw.congr'
    filter_upwards [] with increment
    rfl
  have hConstTendsto : Tendsto
      (fun _ : Source X => boundedFiberSubstitution X
        (current.1.1 2) current.2)
      (nhds 0) (nhds (boundedFiberSubstitution X
        (current.1.1 2) current.2)) := tendsto_const_nhds
  have hDifferenceTendsto := hEvaluationTendsto.sub hConstTendsto
  have hNormTendsto := hDifferenceTendsto.norm
  unfold secondGraphVariationNorm
  have hZero :
      ‖boundedFiberSubstitution X (current.1.1 2) current.2 -
        boundedFiberSubstitution X (current.1.1 2) current.2‖ = 0 :=
    by rw [sub_self, norm_zero]
  rw [hZero] at hNormTendsto
  exact hNormTendsto

theorem evaluationSecond_continuous : Continuous (evaluationSecond X) := by
  rw [continuous_iff_continuousAt]
  intro current
  have hAtZero : Tendsto
      (fun increment : Source X => evaluationSecond X (current + increment))
      (nhds 0) (nhds (evaluationSecond X current)) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hEpsilon
    have hSixth : 0 < epsilon / 6 := div_pos hEpsilon (by norm_num)
    have hHalf : 0 < epsilon / 2 := half_pos hEpsilon
    have hVariationEventually := Metric.tendsto_nhds.mp
      (secondGraphVariationNorm_tendsto_zero X current)
      (epsilon / 2) hHalf
    filter_upwards [Metric.ball_mem_nhds (0 : Source X) hSixth,
      hVariationEventually] with increment hIncrement hVariation
    rw [dist_eq_norm]
    have hIncrementNorm : ‖increment‖ < epsilon / 6 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hIncrement
    have hVariationNonnegative :
        0 ≤ secondGraphVariationNorm X current increment := by
      unfold secondGraphVariationNorm
      exact norm_nonneg _
    have hVariationSmall :
        secondGraphVariationNorm X current increment < epsilon / 2 := by
      simpa only [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg hVariationNonnegative] using hVariation
    exact (evaluationSecond_increment_norm_le X current increment).trans_lt
      (by linarith)
  have hIncrementTendsto : Tendsto
      (fun varied : Source X => varied - current)
      (nhds current) (nhds 0) := by
    have hConstTendsto : Tendsto (fun _ : Source X => current)
        (nhds current) (nhds current) := tendsto_const_nhds
    have hRaw := tendsto_id.sub hConstTendsto
    have hTarget : Tendsto (fun varied : Source X => varied - current)
        (nhds current) (nhds (current - current)) := by
      apply hRaw.congr'
      filter_upwards [] with varied
      rfl
    simpa only [sub_self] using hTarget
  have hComposed := hAtZero.comp hIncrementTendsto
  apply hComposed.congr'
  filter_upwards [] with varied
  have hValue : current + (varied - current) = varied := by abel
  simpa only [Function.comp_apply, hValue]

theorem evaluationFDeriv_contDiff_one :
    ContDiff Real 1 (evaluationFDeriv X) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨evaluationFDeriv_differentiable X, ?_⟩
  have hDerivativeIdentity :
      fderiv Real (evaluationFDeriv X) = evaluationSecond X :=
    funext (evaluationFDeriv_fderiv X)
  rw [hDerivativeIdentity]
  exact evaluationSecond_continuous X

theorem evaluation_contDiff_two : ContDiff Real 2 (evaluation X) := by
  refine (contDiff_succ_iff_fderiv (n := 1)).2 ?_
  refine ⟨evaluation_differentiable X, by norm_num, ?_⟩
  have hDerivativeIdentity :
      fderiv Real (evaluation X) = evaluationFDeriv X :=
    funext (evaluation_fderiv X)
  rw [hDerivativeIdentity]
  exact evaluationFDeriv_contDiff_one X

/-- Public derivative-optimal substitution gate. -/
theorem bounded_fiber_jet2_substitution_c2_gate :
    ContDiff Real 2 (evaluation X) ∧
    (∀ current, fderiv Real (evaluation X) current =
      evaluationFDeriv X current) ∧
    (∀ current, fderiv Real (evaluationFDeriv X) current =
      evaluationSecond X current) :=
  ⟨evaluation_contDiff_two X, evaluation_fderiv X,
    evaluationFDeriv_fderiv X⟩

end
end P0EFTJanusBoundedFiberJet2SubstitutionC2
end JanusFormal
