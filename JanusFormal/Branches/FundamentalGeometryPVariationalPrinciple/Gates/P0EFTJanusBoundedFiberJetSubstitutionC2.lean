import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Bounded fiber-jet substitution

An analytic helper for moving-boundary charts.  A bounded scalar field and
its first three derivatives in one real fiber variable can be evaluated on a
bounded continuous graph.  The resulting substitution map is twice Frechet
differentiable.  This file contains no geometric or physical data.
-/

namespace JanusFormal
namespace P0EFTJanusBoundedFiberJetSubstitutionC2

set_option autoImplicit false

noncomputable section

open Asymptotics Filter Set
open scoped BoundedContinuousFunction Topology

private abbrev canonicalRealAddCommGroup : AddCommGroup Real :=
  NormedField.toNormedCommRing.toAddCommGroup

private abbrev canonicalRealModule : Module Real Real :=
  (NormedAlgebra.toNormedSpace Real).toModule

attribute [local instance 10000] canonicalRealAddCommGroup canonicalRealModule

variable (X : Type*) [TopologicalSpace X]

/-- Canonical real derivative structure used by Mathlib's normed-field
calculus, made explicit to avoid the bare-semiring module diamond. -/
private abbrev RealHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  HasDerivAt function derivative point

/-- On a compact base, the ordinary continuous-map norm and bounded-function
norm coincide, giving a canonical continuous linear inclusion. -/
def compactContinuousToBoundedCLM [CompactSpace X] :
    C(X, Real) →L[Real] (X →ᵇ Real) :=
  LinearMap.mkContinuous
    { toFun := BoundedContinuousFunction.mkOfCompact
      map_add' := fun first second => by
        ext point
        rfl
      map_smul' := fun scalar field => by
        ext point
        rfl }
    1 (fun field => by
      change ‖BoundedContinuousFunction.mkOfCompact field‖ ≤ 1 * ‖field‖
      rw [one_mul, BoundedContinuousFunction.norm_mkOfCompact])

@[simp]
theorem compactContinuousToBoundedCLM_apply
    [CompactSpace X] (field : C(X, Real)) (point : X) :
    compactContinuousToBoundedCLM X field point = field point :=
  rfl

/-- Package a continuous real function with a uniform norm bound as a
bounded continuous function. -/
def boundedContinuousOfNormBound
    {Y : Type*} [TopologicalSpace Y]
    (function : Y → Real) (continuousFunction : Continuous function)
    (bound : Real) (norm_le : ∀ point, ‖function point‖ ≤ bound) :
    Y →ᵇ Real where
  toFun := function
  continuous_toFun := continuousFunction
  map_bounded' := ⟨2 * bound, fun first second => by
    rw [dist_eq_norm]
    calc
      ‖function first - function second‖ ≤
          ‖function first‖ + ‖function second‖ := norm_sub_le _ _
      _ ≤ bound + bound := add_le_add (norm_le first) (norm_le second)
      _ = 2 * bound := by ring⟩

private theorem abs_le_one_add_sq (value : Real) :
    |value| ≤ 1 + value ^ 2 := by
  have hSquare : |value| ^ 2 = value ^ 2 := sq_abs value
  nlinarith [sq_nonneg (|value| - 1)]

/-- The bounded reciprocal quadratic used by the derivatives of `arctan`. -/
def boundedFiberInvQuadratic : BoundedContinuousFunction (X × Real) Real :=
  boundedContinuousOfNormBound
    (fun current : X × Real => 1 / (1 + current.2 ^ 2))
    (continuous_const.div (continuous_const.add
      (continuous_snd.pow 2)) (fun current => by positivity))
    1 (fun current => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [sq_nonneg current.2])

/-- The bounded ratio `r / (1 + r²)` used by the same jet. -/
def boundedFiberRatioQuadratic : BoundedContinuousFunction (X × Real) Real :=
  boundedContinuousOfNormBound
    (fun current : X × Real => current.2 / (1 + current.2 ^ 2))
    (continuous_snd.div (continuous_const.add
      (continuous_snd.pow 2)) (fun current => by positivity))
    1 (fun current => by
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos (show 0 < 1 + current.2 ^ 2 by positivity)]
      exact (div_le_one (by positivity)).2 (abs_le_one_add_sq current.2))

/-- The bounded scalar `arctan` field, constant in the base variable. -/
def boundedFiberArctan : BoundedContinuousFunction (X × Real) Real :=
  boundedContinuousOfNormBound
    (fun current : X × Real => Real.arctan current.2)
    (Real.continuous_arctan.comp continuous_snd)
    (Real.pi / 2) (fun current => by
      rw [Real.norm_eq_abs]
      exact abs_le.2
        ⟨(Real.neg_pi_div_two_lt_arctan current.2).le,
          (Real.arctan_lt_pi_div_two current.2).le⟩)

/-- Compact latitude interval containing the canonical `arctan` collar. -/
abbrev ArctanCompactFiber :=
  Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- Canonical continuous lift of `arctan` to its compact closed range. -/
def arctanCompactFiberMap : C(Real, ArctanCompactFiber) where
  toFun := fun fiber =>
    ⟨Real.arctan fiber,
      ⟨(Real.neg_pi_div_two_lt_arctan fiber).le,
        (Real.arctan_lt_pi_div_two fiber).le⟩⟩
  continuous_toFun :=
    Real.continuous_arctan.subtype_mk _

/-- Product input used to pull a field on the compact latitude strip back to
the unrestricted raw fiber. -/
def arctanCompactFiberInput :
    C(X × Real, X × ArctanCompactFiber) where
  toFun := fun current => (current.1, arctanCompactFiberMap current.2)
  continuous_toFun := continuous_fst.prodMk
    (arctanCompactFiberMap.continuous.comp continuous_snd)

/-- Continuous linear pullback from the compact latitude strip to the raw
fiber.  Boundedness follows from compactness before composition. -/
def boundedArctanCompactPullbackCLM [CompactSpace X] :
    C(X × ArctanCompactFiber, Real) →L[Real]
      BoundedContinuousFunction (X × Real) Real :=
  LinearMap.mkContinuous
    { toFun := fun field =>
        (BoundedContinuousFunction.mkOfCompact field).compContinuous
          (arctanCompactFiberInput X)
      map_add' := fun first second => by
        ext current
        rfl
      map_smul' := fun scalar field => by
        ext current
        rfl }
    1 (fun field => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_compContinuous_le
        (BoundedContinuousFunction.mkOfCompact field)
        (arctanCompactFiberInput X)).trans_eq
          (BoundedContinuousFunction.norm_mkOfCompact field))

@[simp]
theorem boundedArctanCompactPullbackCLM_apply
    [CompactSpace X]
    (field : C(X × ArctanCompactFiber, Real))
    (point : X) (fiber : Real) :
    boundedArctanCompactPullbackCLM X field (point, fiber) =
      field (point, arctanCompactFiberMap fiber) :=
  rfl

/-- The first four compatible bounded derivatives of scalar `arctan`. -/
def boundedFiberArctanJetAmbient : Fin 4 →
    BoundedContinuousFunction (X × Real) Real
  | 0 => boundedFiberArctan X
  | 1 => boundedFiberInvQuadratic X
  | 2 => (-2 : Real) •
      (boundedFiberRatioQuadratic X * boundedFiberInvQuadratic X)
  | 3 =>
      (6 : Real) • ((boundedFiberRatioQuadratic X) ^ 2 *
        boundedFiberInvQuadratic X) -
      (2 : Real) • ((boundedFiberInvQuadratic X) ^ 3)

set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_invQuadratic (fiber : Real) :
    RealHasDerivAt (fun varied : Real => 1 / (1 + varied ^ 2))
      (-(2 * fiber) / (1 + fiber ^ 2) ^ 2) fiber := by
  have hDenominator : RealHasDerivAt (fun varied : Real => 1 + varied ^ 2)
      (2 * fiber) fiber := by
    simpa using ((hasDerivAt_id fiber).pow 2).const_add 1
  have hQuotient := (hasDerivAt_const fiber (1 : Real)).div
    hDenominator (by positivity : 1 + fiber ^ 2 ≠ 0)
  change RealHasDerivAt ((fun _ : Real => 1) /
    fun varied : Real => 1 + varied ^ 2) _ _
  simpa only [Pi.div_apply, Pi.one_apply, zero_mul, one_mul, zero_sub]
    using hQuotient

set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_ratioQuadratic (fiber : Real) :
    RealHasDerivAt (fun varied : Real => varied / (1 + varied ^ 2))
      ((1 + fiber ^ 2 - fiber * (2 * fiber)) /
        (1 + fiber ^ 2) ^ 2) fiber := by
  have hDenominator : RealHasDerivAt (fun varied : Real => 1 + varied ^ 2)
      (2 * fiber) fiber := by
    simpa using ((hasDerivAt_id fiber).pow 2).const_add 1
  have hQuotient := (hasDerivAt_id fiber).div hDenominator
    (by positivity : 1 + fiber ^ 2 ≠ 0)
  change RealHasDerivAt (id /
    fun varied : Real => 1 + varied ^ 2) _ _
  simpa only [Pi.div_apply, id_eq, one_mul] using hQuotient

set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_arctanSecondComponent (fiber : Real) :
    RealHasDerivAt
      (fun varied : Real =>
        (-2) * (varied / (1 + varied ^ 2)) *
          (1 / (1 + varied ^ 2)))
      ((-2) *
        (((1 + fiber ^ 2 - fiber * (2 * fiber)) /
            (1 + fiber ^ 2) ^ 2) * (1 / (1 + fiber ^ 2)) +
          (fiber / (1 + fiber ^ 2)) *
            (-(2 * fiber) / (1 + fiber ^ 2) ^ 2))) fiber := by
  have hProduct := (hasDerivAt_ratioQuadratic fiber).mul
    (hasDerivAt_invQuadratic fiber)
  have hScaled := hProduct.const_mul (-2)
  simpa only [Pi.mul_apply, mul_assoc] using hScaled

abbrev BoundedFiberField := (X × Real) →ᵇ Real

abbrev BoundedFiberJet3Ambient :=
  Fin 4 → BoundedFiberField X

/-- Compatible bounded value/derivative jets in one real fiber variable. -/
def boundedFiberJet3Submodule :
    Submodule Real (BoundedFiberJet3Ambient X) where
  carrier := {jet |
    (∀ point fiber,
      RealHasDerivAt (fun varied => jet 0 (point, varied))
        (jet 1 (point, fiber)) fiber) ∧
    (∀ point fiber,
      RealHasDerivAt (fun varied => jet 1 (point, varied))
        (jet 2 (point, fiber)) fiber) ∧
    (∀ point fiber,
      RealHasDerivAt (fun varied => jet 2 (point, varied))
        (jet 3 (point, fiber)) fiber)}
  zero_mem' := by
    exact ⟨fun _ fiber => by
        simpa using hasDerivAt_const fiber (0 : Real),
      fun _ fiber => by
        simpa using hasDerivAt_const fiber (0 : Real),
      fun _ fiber => by
        simpa using hasDerivAt_const fiber (0 : Real)⟩
  add_mem' := by
    intro first second hFirst hSecond
    rcases hFirst with ⟨hFirst0, hFirst1, hFirst2⟩
    rcases hSecond with ⟨hSecond0, hSecond1, hSecond2⟩
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
        exact (hFirst1 point fiber).add (hSecond1 point fiber),
      fun point fiber => by
        change RealHasDerivAt
          ((fun varied => first 2 (point, varied)) +
            fun varied => second 2 (point, varied))
          (first 3 (point, fiber) + second 3 (point, fiber)) fiber
        exact (hFirst2 point fiber).add (hSecond2 point fiber)⟩
  smul_mem' := by
    intro scalar jet hJet
    rcases hJet with ⟨hJet0, hJet1, hJet2⟩
    exact ⟨fun point fiber => by
        change RealHasDerivAt
          (scalar • fun varied => jet 0 (point, varied))
          (scalar • jet 1 (point, fiber)) fiber
        exact (hJet0 point fiber).const_smul scalar,
      fun point fiber => by
        change RealHasDerivAt
          (scalar • fun varied => jet 1 (point, varied))
          (scalar • jet 2 (point, fiber)) fiber
        exact (hJet1 point fiber).const_smul scalar,
      fun point fiber => by
        change RealHasDerivAt
          (scalar • fun varied => jet 2 (point, varied))
          (scalar • jet 3 (point, fiber)) fiber
        exact (hJet2 point fiber).const_smul scalar⟩

abbrev BoundedFiberJet3 := boundedFiberJet3Submodule X

/-- Compatible bounded fiber jets are closed under uniform convergence of
all four components. -/
theorem boundedFiberJet3Submodule_isClosed :
    IsClosed (boundedFiberJet3Submodule X :
      Set (BoundedFiberJet3Ambient X)) := by
  refine IsSeqClosed.isClosed fun sequence jet hSequence hConverges => ?_
  have hComponent (index : Fin 4) :
      Tendsto (fun n => sequence n index) atTop (𝓝 (jet index)) :=
    tendsto_pi_nhds.mp hConverges index
  have hUniform (index : Fin 4) :
      TendstoUniformly (fun n => sequence n index) (jet index) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (hComponent index)
  refine ⟨fun point fiber => ?_, fun point fiber => ?_,
    fun point fiber => ?_⟩
  · exact hasDerivAt_of_tendstoUniformly
      ((hUniform 1).comp (fun varied => (point, varied)))
      (Filter.Eventually.of_forall fun n varied =>
        (hSequence n).1 point varied)
      (fun varied => (hUniform 0).tendsto_at (point, varied)) fiber
  · exact hasDerivAt_of_tendstoUniformly
      ((hUniform 2).comp (fun varied => (point, varied)))
      (Filter.Eventually.of_forall fun n varied =>
        (hSequence n).2.1 point varied)
      (fun varied => (hUniform 1).tendsto_at (point, varied)) fiber
  · exact hasDerivAt_of_tendstoUniformly
      ((hUniform 3).comp (fun varied => (point, varied)))
      (Filter.Eventually.of_forall fun n varied =>
        (hSequence n).2.2 point varied)
      (fun varied => (hUniform 2).tendsto_at (point, varied)) fiber

/-- Compatible bounded third jet of scalar `arctan`. -/
def boundedFiberArctanJet3 : BoundedFiberJet3 X := by
  refine ⟨boundedFiberArctanJetAmbient X, ?_⟩
  refine ⟨fun point fiber => ?_, fun point fiber => ?_,
    fun point fiber => ?_⟩
  · change RealHasDerivAt Real.arctan (1 / (1 + fiber ^ 2)) fiber
    exact Real.hasDerivAt_arctan fiber
  · dsimp [boundedFiberArctanJetAmbient, boundedFiberInvQuadratic,
      boundedFiberRatioQuadratic, boundedContinuousOfNormBound]
    change RealHasDerivAt
      (fun varied : Real => 1 / (1 + varied ^ 2))
      ((-2) * ((fiber / (1 + fiber ^ 2)) *
        (1 / (1 + fiber ^ 2)))) fiber
    convert hasDerivAt_invQuadratic fiber using 1
    field_simp [show 1 + fiber ^ 2 ≠ 0 by positivity] <;> ring
  · dsimp [boundedFiberArctanJetAmbient, boundedFiberInvQuadratic,
      boundedFiberRatioQuadratic, boundedContinuousOfNormBound]
    change RealHasDerivAt
      (fun varied : Real =>
        (-2) * ((varied / (1 + varied ^ 2)) *
          (1 / (1 + varied ^ 2))))
      ((6 : Real) • ((fiber / (1 + fiber ^ 2)) ^ 2 *
          (1 / (1 + fiber ^ 2))) -
        (2 : Real) • ((1 / (1 + fiber ^ 2)) ^ 3)) fiber
    convert hasDerivAt_arctanSecondComponent fiber using 1
    · funext varied
      ring
    · change
        6 * ((fiber / (1 + fiber ^ 2)) ^ 2 *
            (1 / (1 + fiber ^ 2))) -
          2 * ((1 / (1 + fiber ^ 2)) ^ 3) = _
      field_simp [show 1 + fiber ^ 2 ≠ 0 by positivity] <;> ring

@[simp]
theorem boundedFiberArctanJet3_value
    (point : X) (fiber : Real) :
    (boundedFiberArctanJet3 X).1 0 (point, fiber) = Real.arctan fiber :=
  rfl

local instance boundedFiberJet3ExplicitAddCommGroup :
    AddCommGroup (BoundedFiberJet3 X) :=
  inferInstanceAs (AddCommGroup (boundedFiberJet3Submodule X))

local instance boundedFiberJet3ExplicitNormedAddCommGroup :
    NormedAddCommGroup (BoundedFiberJet3 X) :=
  inferInstanceAs (NormedAddCommGroup (boundedFiberJet3Submodule X))

local instance boundedFiberJet3ExplicitNormedSpace :
    NormedSpace Real (BoundedFiberJet3 X) :=
  inferInstanceAs (NormedSpace Real (boundedFiberJet3Submodule X))

/-- Evaluation of a bounded field on a bounded continuous graph. -/
def boundedFiberSubstitution
    (field : BoundedFiberField X)
    (graph : X →ᵇ Real) : X →ᵇ Real where
  toFun point := field (point, graph point)
  continuous_toFun := field.continuous.comp
    (continuous_id.prodMk graph.continuous)
  map_bounded' := field.bounded.imp fun bound hBound first second =>
    hBound (first, graph first) (second, graph second)

@[simp]
theorem boundedFiberSubstitution_apply
    (field : BoundedFiberField X)
    (graph : X →ᵇ Real) (point : X) :
    boundedFiberSubstitution X field graph point =
      field (point, graph point) :=
  rfl

theorem boundedFiberSubstitution_norm_le
    (field : BoundedFiberField X)
    (graph : X →ᵇ Real) :
    ‖boundedFiberSubstitution X field graph‖ ≤ ‖field‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg field)]
  intro point
  exact field.norm_coe_le_norm (point, graph point)

/-- Substitution is a contraction in its field argument when the graph is
fixed. -/
def boundedFiberSubstitutionFieldCLM
    (graph : X →ᵇ Real) :
    BoundedFiberField X →L[Real] (X →ᵇ Real) :=
  LinearMap.mkContinuous
    { toFun := fun field => boundedFiberSubstitution X field graph
      map_add' := fun first second => by
        ext point
        rfl
      map_smul' := fun scalar field => by
        ext point
        rfl }
    1 (fun field => by
      simpa using boundedFiberSubstitution_norm_le X field graph)

@[simp]
theorem boundedFiberSubstitutionFieldCLM_apply
    (graph : X →ᵇ Real) (field : BoundedFiberField X) :
    boundedFiberSubstitutionFieldCLM X graph field =
      boundedFiberSubstitution X field graph :=
  rfl

/-- Continuous projection of one component of a compatible jet. -/
def boundedFiberJet3ComponentCLM (index : Fin 4) :
    BoundedFiberJet3 X →L[Real] BoundedFiberField X :=
  (ContinuousLinearMap.proj index).comp
    (boundedFiberJet3Submodule X).subtypeL

@[simp]
theorem boundedFiberJet3ComponentCLM_apply
    (index : Fin 4) (jet : BoundedFiberJet3 X) :
    boundedFiberJet3ComponentCLM X index jet = jet.1 index :=
  rfl

theorem boundedFiberJet3_component_norm_le
    (jet : BoundedFiberJet3 X) (index : Fin 4) :
    ‖jet.1 index‖ ≤ ‖jet‖ := by
  change ‖jet.1 index‖ ≤ ‖jet.1‖
  exact norm_le_pi_norm jet.1 index

private theorem scalar_image_sub_bound
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

private theorem scalar_taylor_one_bound
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
    have hFirstDifference := scalar_image_sub_bound first second hFirst bound
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
  have hRemainderZero : remainder 0 = 0 := by
    simp [remainder]
  rw [hRemainderZero, sub_zero] at hEstimate
  convert hEstimate using 1 <;>
    simp only [remainder, Real.norm_eq_abs, pow_two, sub_zero] <;> ring

/-- Uniform first-order Taylor bound for compatible bounded jets. -/
theorem boundedFiberJet3_substitution_taylor_zero
    (jet : BoundedFiberJet3 X)
    (graph increment : X →ᵇ Real) :
    ‖boundedFiberSubstitution X (jet.1 0) (graph + increment) -
        boundedFiberSubstitution X (jet.1 0) graph -
        boundedFiberSubstitution X (jet.1 1) graph * increment‖ ≤
      ‖jet.1 2‖ * ‖increment‖ ^ 2 := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg
    (norm_nonneg _) (sq_nonneg _))]
  intro point
  have hPoint := scalar_taylor_one_bound
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

/-- The same Taylor bound one derivative higher. -/
theorem boundedFiberJet3_substitution_taylor_one
    (jet : BoundedFiberJet3 X)
    (graph increment : X →ᵇ Real) :
    ‖boundedFiberSubstitution X (jet.1 1) (graph + increment) -
        boundedFiberSubstitution X (jet.1 1) graph -
        boundedFiberSubstitution X (jet.1 2) graph * increment‖ ≤
      ‖jet.1 3‖ * ‖increment‖ ^ 2 := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg
    (norm_nonneg _) (sq_nonneg _))]
  intro point
  have hPoint := scalar_taylor_one_bound
    (fun fiber => jet.1 1 (point, fiber))
    (fun fiber => jet.1 2 (point, fiber))
    (fun fiber => jet.1 3 (point, fiber))
    (fun fiber => jet.2.2.1 point fiber)
    (fun fiber => jet.2.2.2 point fiber) ‖jet.1 3‖
    (fun fiber => (jet.1 3).norm_coe_le_norm (point, fiber))
    (graph point) (increment point)
  exact hPoint.trans (by
    gcongr
    exact increment.norm_coe_le_norm point)

/-- Uniform mean-value bound for the first three jet components. -/
theorem boundedFiberJet3_substitution_lipschitz
    (jet : BoundedFiberJet3 X)
    (index : Fin 3)
    (graph increment : X →ᵇ Real) :
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
    · exact jet.2.2.2 point
  have hPoint := scalar_image_sub_bound
    (fun fiber => jet.1 index.castSucc (point, fiber))
    (fun fiber => jet.1 index.succ (point, fiber))
    hDerivative ‖jet.1 index.succ‖
    (fun fiber => (jet.1 index.succ).norm_coe_le_norm (point, fiber))
    (graph point) (increment point)
  exact hPoint.trans (by
    gcongr
    exact increment.norm_coe_le_norm point)

/-! ## First Frechet derivative -/

private abbrev FiberGraph := X →ᵇ Real

private abbrev FiberEvaluationSource :=
  BoundedFiberJet3 X × FiberGraph X

local instance fiberEvaluationSourceNormedAddCommGroup :
    NormedAddCommGroup (FiberEvaluationSource X) :=
  inferInstance

local instance fiberEvaluationSourceNormedSpace :
    NormedSpace Real (FiberEvaluationSource X) :=
  inferInstance

local instance fiberEvaluationSourceTopologicalSpace :
    TopologicalSpace (FiberEvaluationSource X) :=
  (fiberEvaluationSourceNormedAddCommGroup (X := X)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance fiberEvaluationSourceAddCommGroup :
    AddCommGroup (FiberEvaluationSource X) :=
  (fiberEvaluationSourceNormedAddCommGroup (X := X)).toAddCommGroup

local instance fiberEvaluationSourceAddCommMonoid :
    AddCommMonoid (FiberEvaluationSource X) :=
  (fiberEvaluationSourceNormedAddCommGroup (X := X)).toAddCommGroup.toAddCommMonoid

local instance fiberEvaluationSourceModule :
    Module Real (FiberEvaluationSource X) :=
  (fiberEvaluationSourceNormedSpace (X := X)).toModule

local instance fiberEvaluationDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  inferInstance

local instance fiberEvaluationDerivativeNormedSpace :
    NormedSpace Real
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  inferInstance

local instance fiberEvaluationDerivativeTopologicalSpace :
    TopologicalSpace
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  (fiberEvaluationDerivativeNormedAddCommGroup (X := X)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance fiberEvaluationDerivativeAddCommGroup :
    AddCommGroup
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  (fiberEvaluationDerivativeNormedAddCommGroup (X := X)).toAddCommGroup

local instance fiberEvaluationDerivativeAddCommMonoid :
    AddCommMonoid
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  (fiberEvaluationDerivativeNormedAddCommGroup (X := X)).toAddCommGroup.toAddCommMonoid

local instance fiberEvaluationDerivativeModule :
    Module Real
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  (fiberEvaluationDerivativeNormedSpace (X := X)).toModule

/-- Evaluation of the value component of a compatible jet on its graph. -/
def boundedFiberJet3Evaluation
    (current : FiberEvaluationSource X) : FiberGraph X :=
  boundedFiberSubstitution X (current.1.1 0) current.2

/-- Candidate first derivative of bounded fiber substitution. -/
def boundedFiberJet3EvaluationFDeriv
    (current : FiberEvaluationSource X) :
    FiberEvaluationSource X →L[Real] FiberGraph X :=
  ((boundedFiberSubstitutionFieldCLM X current.2).comp
      ((boundedFiberJet3ComponentCLM X 0).comp
        (ContinuousLinearMap.fst Real
          (BoundedFiberJet3 X) (FiberGraph X)))) +
    ((ContinuousLinearMap.mul Real (FiberGraph X)
      (boundedFiberSubstitution X (current.1.1 1) current.2)).comp
        (ContinuousLinearMap.snd Real
          (BoundedFiberJet3 X) (FiberGraph X)))

@[simp]
theorem boundedFiberJet3EvaluationFDeriv_apply
    (current increment : FiberEvaluationSource X) :
    boundedFiberJet3EvaluationFDeriv X current increment =
      boundedFiberSubstitution X (increment.1.1 0) current.2 +
        boundedFiberSubstitution X (current.1.1 1) current.2 * increment.2 := by
  rfl

private theorem boundedFiberJet3Evaluation_increment
    (current increment : FiberEvaluationSource X) :
    boundedFiberJet3Evaluation X (current + increment) -
        boundedFiberJet3Evaluation X current -
        boundedFiberJet3EvaluationFDeriv X current increment =
      (boundedFiberSubstitution X (current.1.1 0)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (current.1.1 0) current.2 -
        boundedFiberSubstitution X (current.1.1 1) current.2 * increment.2) +
      (boundedFiberSubstitution X (increment.1.1 0)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (increment.1.1 0) current.2) := by
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

private theorem boundedFiberJet3Evaluation_remainder_norm_le
    (current increment : FiberEvaluationSource X) :
    ‖boundedFiberJet3Evaluation X (current + increment) -
        boundedFiberJet3Evaluation X current -
        boundedFiberJet3EvaluationFDeriv X current increment‖ ≤
      (‖current.1‖ + 1) * ‖increment‖ ^ 2 := by
  rw [boundedFiberJet3Evaluation_increment]
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
        (boundedFiberJet3_substitution_taylor_zero X current.1 current.2
          increment.2)
        (boundedFiberJet3_substitution_lipschitz X increment.1 0 current.2
          increment.2)
    _ ≤ ‖current.1‖ * ‖increment‖ ^ 2 + ‖increment‖ ^ 2 := by
      apply add_le_add
      · exact mul_le_mul
          (boundedFiberJet3_component_norm_le X current.1 2)
          (by gcongr; exact norm_snd_le increment)
          (sq_nonneg _) (norm_nonneg current.1)
      · calc
          ‖increment.1.1 1‖ * ‖increment.2‖ ≤
              ‖increment.1‖ * ‖increment.2‖ := by
            gcongr
            exact boundedFiberJet3_component_norm_le X increment.1 1
          _ ≤ ‖increment‖ * ‖increment‖ := by
            exact mul_le_mul (norm_fst_le increment) (norm_snd_le increment)
              (norm_nonneg increment.2) (norm_nonneg increment)
          _ = ‖increment‖ ^ 2 := by ring
    _ = (‖current.1‖ + 1) * ‖increment‖ ^ 2 := by ring

private theorem isLittleO_id_of_norm_le_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (remainder : E → F) (bound : Real) (hBoundNonnegative : 0 ≤ bound)
    (hRemainder : ∀ increment,
      ‖remainder increment‖ ≤ bound * ‖increment‖ ^ 2) :
    remainder =o[𝓝 0] (fun increment : E => increment) := by
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
    ‖remainder increment‖ ≤ bound * ‖increment‖ ^ 2 :=
      hRemainder increment
    _ ≤ (bound + 1) * ‖increment‖ ^ 2 := by
      gcongr
      linarith
    _ = ((bound + 1) * ‖increment‖) * ‖increment‖ := by ring
    _ ≤ coefficient * ‖increment‖ :=
      mul_le_mul_of_nonneg_right hScaled.le (norm_nonneg _)

/-- Exact first Frechet derivative of bounded compatible-jet substitution. -/
theorem boundedFiberJet3Evaluation_hasFDerivAt
    (current : FiberEvaluationSource X) :
    HasFDerivAt (boundedFiberJet3Evaluation X)
      (boundedFiberJet3EvaluationFDeriv X current) current := by
  refine (hasFDerivAt_iff_isLittleO_nhds_zero
    (f := boundedFiberJet3Evaluation X)
    (f' := boundedFiberJet3EvaluationFDeriv X current)
    (x := current)).2 ?_
  exact isLittleO_id_of_norm_le_sq
    (fun increment : FiberEvaluationSource X =>
      boundedFiberJet3Evaluation X (current + increment) -
        boundedFiberJet3Evaluation X current -
        boundedFiberJet3EvaluationFDeriv X current increment)
    (‖current.1‖ + 1) (by positivity)
    (boundedFiberJet3Evaluation_remainder_norm_le X current)

theorem boundedFiberJet3Evaluation_differentiable :
    Differentiable Real (boundedFiberJet3Evaluation X) :=
  fun current =>
    (boundedFiberJet3Evaluation_hasFDerivAt X current).differentiableAt

theorem boundedFiberJet3Evaluation_fderiv
    (current : FiberEvaluationSource X) :
    fderiv Real (boundedFiberJet3Evaluation X) current =
      boundedFiberJet3EvaluationFDeriv X current :=
  (boundedFiberJet3Evaluation_hasFDerivAt X current).fderiv

/-! ## Second Frechet derivative -/

private def boundedFiberJet3EvaluationSecondLinear
    (current : FiberEvaluationSource X) :
    FiberEvaluationSource X →ₗ[Real]
      (FiberEvaluationSource X →ₗ[Real] FiberGraph X) :=
  LinearMap.mk₂ Real
    (fun first second =>
      boundedFiberSubstitution X (second.1.1 1) current.2 * first.2 +
        boundedFiberSubstitution X (first.1.1 1) current.2 * second.2 +
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          first.2 * second.2)
    (by
      intro first second third
      ext point
      simp [boundedFiberSubstitution]
      ring)
    (by
      intro scalar first second
      ext point
      simp [boundedFiberSubstitution]
      ring)
    (by
      intro first second third
      ext point
      simp [boundedFiberSubstitution]
      ring)
    (by
      intro scalar first second
      ext point
      simp [boundedFiberSubstitution]
      ring)

/-- Candidate second derivative, bundled as a continuous bilinear map. -/
def boundedFiberJet3EvaluationSecond
    (current : FiberEvaluationSource X) :
    FiberEvaluationSource X →L[Real]
      (FiberEvaluationSource X →L[Real] FiberGraph X) :=
  (boundedFiberJet3EvaluationSecondLinear X current).mkContinuous₂
    (2 + ‖current.1.1 2‖)
    (fun (first : FiberEvaluationSource X)
        (second : FiberEvaluationSource X) => by
      have hFirstJet : ‖first.1.1 1‖ ≤ ‖first‖ :=
        (boundedFiberJet3_component_norm_le X first.1 1).trans
          (norm_fst_le first)
      have hSecondJet : ‖second.1.1 1‖ ≤ ‖second‖ :=
        (boundedFiberJet3_component_norm_le X second.1 1).trans
          (norm_fst_le second)
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
            (norm_add_le _ _)
            (norm_mul_le _ _)) |>.trans (by
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
theorem boundedFiberJet3EvaluationSecond_apply
    (current first second : FiberEvaluationSource X) :
    boundedFiberJet3EvaluationSecond X current first second =
      boundedFiberSubstitution X (second.1.1 1) current.2 * first.2 +
        boundedFiberSubstitution X (first.1.1 1) current.2 * second.2 +
        boundedFiberSubstitution X (current.1.1 2) current.2 *
          first.2 * second.2 := by
  simp only [boundedFiberJet3EvaluationSecond,
    LinearMap.mkContinuous₂_apply,
    boundedFiberJet3EvaluationSecondLinear,
    LinearMap.mk₂_apply]

private theorem boundedFiberJet3EvaluationFDeriv_increment_apply
    (current increment direction : FiberEvaluationSource X) :
    (boundedFiberJet3EvaluationFDeriv X (current + increment) -
        boundedFiberJet3EvaluationFDeriv X current -
        boundedFiberJet3EvaluationSecond X current increment) direction =
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

private theorem boundedFiberJet3EvaluationFDeriv_remainder_apply_norm_le
    (current increment direction : FiberEvaluationSource X) :
    ‖(boundedFiberJet3EvaluationFDeriv X (current + increment) -
        boundedFiberJet3EvaluationFDeriv X current -
        boundedFiberJet3EvaluationSecond X current increment) direction‖ ≤
      (‖current.1‖ + 2) * ‖increment‖ ^ 2 * ‖direction‖ := by
  rw [boundedFiberJet3EvaluationFDeriv_increment_apply]
  have hDirectionJet2 : ‖direction.1.1 2‖ ≤ ‖direction‖ :=
    (boundedFiberJet3_component_norm_le X direction.1 2).trans
      (norm_fst_le direction)
  have hCurrentJet3 : ‖current.1.1 3‖ ≤ ‖current.1‖ :=
    boundedFiberJet3_component_norm_le X current.1 3
  have hIncrementJet2 : ‖increment.1.1 2‖ ≤ ‖increment‖ :=
    (boundedFiberJet3_component_norm_le X increment.1 2).trans
      (norm_fst_le increment)
  have hIncrementGraph : ‖increment.2‖ ≤ ‖increment‖ :=
    norm_snd_le increment
  have hDirectionGraph : ‖direction.2‖ ≤ ‖direction‖ :=
    norm_snd_le direction
  have hIncrementGraphSq : ‖increment.2‖ ^ 2 ≤ ‖increment‖ ^ 2 := by
    gcongr
  have hFirstTerm :
      ‖direction.1.1 2‖ * ‖increment.2‖ ^ 2 ≤
        ‖direction‖ * ‖increment‖ ^ 2 :=
    mul_le_mul hDirectionJet2 hIncrementGraphSq
      (sq_nonneg ‖increment.2‖) (norm_nonneg direction)
  have hSecondTerm :
      (‖current.1.1 3‖ * ‖increment.2‖ ^ 2) * ‖direction.2‖ ≤
        (‖current.1‖ * ‖increment‖ ^ 2) * ‖direction‖ := by
    exact mul_le_mul
      (mul_le_mul hCurrentJet3 hIncrementGraphSq
        (sq_nonneg ‖increment.2‖) (norm_nonneg current.1))
      hDirectionGraph (norm_nonneg direction.2)
      (mul_nonneg (norm_nonneg current.1) (sq_nonneg ‖increment‖))
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
        (‖current.1.1 3‖ * ‖increment.2‖ ^ 2) * ‖direction.2‖ +
        (‖increment.1.1 2‖ * ‖increment.2‖) * ‖direction.2‖ := by
      apply add_le_add
      · apply add_le_add
        · exact boundedFiberJet3_substitution_taylor_zero X
            direction.1 current.2 increment.2
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (boundedFiberJet3_substitution_taylor_one X
                current.1 current.2 increment.2)
              (norm_nonneg _))
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right
            (boundedFiberJet3_substitution_lipschitz X
              increment.1 1 current.2 increment.2)
            (norm_nonneg _))
    _ ≤
        ‖direction‖ * ‖increment‖ ^ 2 +
        (‖current.1‖ * ‖increment‖ ^ 2) * ‖direction‖ +
        ‖increment‖ ^ 2 * ‖direction‖ :=
      add_le_add (add_le_add hFirstTerm hSecondTerm) hThirdTerm
    _ = (‖current.1‖ + 2) * ‖increment‖ ^ 2 * ‖direction‖ := by
      ring

private theorem boundedFiberJet3EvaluationFDeriv_remainder_norm_le
    (current increment : FiberEvaluationSource X) :
    ‖boundedFiberJet3EvaluationFDeriv X (current + increment) -
        boundedFiberJet3EvaluationFDeriv X current -
        boundedFiberJet3EvaluationSecond X current increment‖ ≤
      (‖current.1‖ + 2) * ‖increment‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (sq_nonneg _))
  intro direction
  exact boundedFiberJet3EvaluationFDeriv_remainder_apply_norm_le X
    current increment direction

/-- The bilinear candidate is the exact Frechet derivative of the first
derivative field. -/
theorem boundedFiberJet3EvaluationFDeriv_hasFDerivAt
    (current : FiberEvaluationSource X) :
    HasFDerivAt (boundedFiberJet3EvaluationFDeriv X)
      (boundedFiberJet3EvaluationSecond X current) current := by
  refine (hasFDerivAt_iff_isLittleO_nhds_zero
    (f := boundedFiberJet3EvaluationFDeriv X)
    (f' := boundedFiberJet3EvaluationSecond X current)
    (x := current)).2 ?_
  exact isLittleO_id_of_norm_le_sq
    (fun increment : FiberEvaluationSource X =>
      boundedFiberJet3EvaluationFDeriv X (current + increment) -
        boundedFiberJet3EvaluationFDeriv X current -
        boundedFiberJet3EvaluationSecond X current increment)
    (‖current.1‖ + 2) (by positivity)
    (boundedFiberJet3EvaluationFDeriv_remainder_norm_le X current)

theorem boundedFiberJet3EvaluationFDeriv_differentiable :
    Differentiable Real (boundedFiberJet3EvaluationFDeriv X) :=
  fun current =>
    (boundedFiberJet3EvaluationFDeriv_hasFDerivAt X current).differentiableAt

theorem boundedFiberJet3EvaluationFDeriv_fderiv
    (current : FiberEvaluationSource X) :
    fderiv Real (boundedFiberJet3EvaluationFDeriv X) current =
      boundedFiberJet3EvaluationSecond X current :=
  (boundedFiberJet3EvaluationFDeriv_hasFDerivAt X current).fderiv

private theorem boundedFiberJet3EvaluationSecond_increment_apply
    (current increment first second : FiberEvaluationSource X) :
    (boundedFiberJet3EvaluationSecond X (current + increment) -
        boundedFiberJet3EvaluationSecond X current) first second =
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

private theorem boundedFiberJet3EvaluationSecond_increment_apply_norm_le
    (current increment first second : FiberEvaluationSource X) :
    ‖(boundedFiberJet3EvaluationSecond X (current + increment) -
        boundedFiberJet3EvaluationSecond X current) first second‖ ≤
      (‖current.1‖ + 3) * ‖increment‖ * ‖first‖ * ‖second‖ := by
  rw [boundedFiberJet3EvaluationSecond_increment_apply]
  have hIncrementGraph : ‖increment.2‖ ≤ ‖increment‖ :=
    norm_snd_le increment
  have hFirstGraph : ‖first.2‖ ≤ ‖first‖ := norm_snd_le first
  have hSecondGraph : ‖second.2‖ ≤ ‖second‖ := norm_snd_le second
  have hFirstJet2 : ‖first.1.1 2‖ ≤ ‖first‖ :=
    (boundedFiberJet3_component_norm_le X first.1 2).trans
      (norm_fst_le first)
  have hSecondJet2 : ‖second.1.1 2‖ ≤ ‖second‖ :=
    (boundedFiberJet3_component_norm_le X second.1 2).trans
      (norm_fst_le second)
  have hCurrentJet3 : ‖current.1.1 3‖ ≤ ‖current.1‖ :=
    boundedFiberJet3_component_norm_le X current.1 3
  have hIncrementJet2 : ‖increment.1.1 2‖ ≤ ‖increment‖ :=
    (boundedFiberJet3_component_norm_le X increment.1 2).trans
      (norm_fst_le increment)
  have hFirstTerm :
      ‖(boundedFiberSubstitution X (second.1.1 1)
          (current.2 + increment.2) -
        boundedFiberSubstitution X (second.1.1 1) current.2) * first.2‖ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤
          ‖boundedFiberSubstitution X (second.1.1 1)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (second.1.1 1) current.2‖ *
              ‖first.2‖ := norm_mul_le _ _
      _ ≤ (‖second.1.1 2‖ * ‖increment.2‖) * ‖first.2‖ :=
        mul_le_mul_of_nonneg_right
          (boundedFiberJet3_substitution_lipschitz X
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
      _ ≤
          ‖boundedFiberSubstitution X (first.1.1 1)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (first.1.1 1) current.2‖ *
              ‖second.2‖ := norm_mul_le _ _
      _ ≤ (‖first.1.1 2‖ * ‖increment.2‖) * ‖second.2‖ :=
        mul_le_mul_of_nonneg_right
          (boundedFiberJet3_substitution_lipschitz X
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
        ‖current.1‖ * ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤
          (‖boundedFiberSubstitution X (current.1.1 2)
              (current.2 + increment.2) -
            boundedFiberSubstitution X (current.1.1 2) current.2‖ *
              ‖first.2‖) * ‖second.2‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
      _ ≤ ((‖current.1.1 3‖ * ‖increment.2‖) * ‖first.2‖) *
            ‖second.2‖ := by
        gcongr
        exact boundedFiberJet3_substitution_lipschitz X
          current.1 2 current.2 increment.2
      _ ≤ ((‖current.1‖ * ‖increment‖) * ‖first‖) * ‖second‖ := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul hCurrentJet3 hIncrementGraph
              (norm_nonneg increment.2) (norm_nonneg current.1)
          · exact hFirstGraph
          · exact norm_nonneg first.2
          · exact mul_nonneg (norm_nonneg current.1) (norm_nonneg increment)
        · exact hSecondGraph
        · exact norm_nonneg second.2
        · positivity
      _ = ‖current.1‖ * ‖increment‖ * ‖first‖ * ‖second‖ := by ring
  have hFourthTerm :
      ‖boundedFiberSubstitution X (increment.1.1 2)
          (current.2 + increment.2) * first.2 * second.2‖ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ := by
    calc
      _ ≤
          (‖boundedFiberSubstitution X (increment.1.1 2)
              (current.2 + increment.2)‖ * ‖first.2‖) *
            ‖second.2‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
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
        ((norm_add_le _ _).trans (add_le_add
          (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤
        ‖increment‖ * ‖first‖ * ‖second‖ +
        ‖increment‖ * ‖first‖ * ‖second‖ +
        ‖current.1‖ * ‖increment‖ * ‖first‖ * ‖second‖ +
        ‖increment‖ * ‖first‖ * ‖second‖ :=
      add_le_add (add_le_add (add_le_add hFirstTerm hSecondTerm)
        hThirdTerm) hFourthTerm
    _ = (‖current.1‖ + 3) * ‖increment‖ * ‖first‖ * ‖second‖ := by
      ring

private theorem boundedFiberJet3EvaluationSecond_increment_inner_norm_le
    (current increment first : FiberEvaluationSource X) :
    ‖(boundedFiberJet3EvaluationSecond X (current + increment) -
        boundedFiberJet3EvaluationSecond X current) first‖ ≤
      (‖current.1‖ + 3) * ‖increment‖ * ‖first‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro second
  exact boundedFiberJet3EvaluationSecond_increment_apply_norm_le X
    current increment first second

private theorem boundedFiberJet3EvaluationSecond_increment_norm_le
    (current increment : FiberEvaluationSource X) :
    ‖boundedFiberJet3EvaluationSecond X (current + increment) -
        boundedFiberJet3EvaluationSecond X current‖ ≤
      (‖current.1‖ + 3) * ‖increment‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro first
  exact boundedFiberJet3EvaluationSecond_increment_inner_norm_le X
    current increment first

/-- The exact second derivative varies continuously in the completed jet and
graph variables. -/
theorem boundedFiberJet3EvaluationSecond_continuous :
    Continuous (boundedFiberJet3EvaluationSecond X) := by
  rw [continuous_iff_continuousAt]
  intro current
  refine continuousAt_of_locally_lipschitz zero_lt_one
    (‖current.1‖ + 3) ?_
  intro varied _
  rw [dist_eq_norm, dist_eq_norm]
  have hVaried : current + (varied - current) = varied := by abel
  simpa only [hVaried] using
    (boundedFiberJet3EvaluationSecond_increment_norm_le X current
      (varied - current))

theorem boundedFiberJet3EvaluationFDeriv_contDiff_one :
    ContDiff Real 1 (boundedFiberJet3EvaluationFDeriv X) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨boundedFiberJet3EvaluationFDeriv_differentiable X, ?_⟩
  have hFDeriv :
      fderiv Real (boundedFiberJet3EvaluationFDeriv X) =
        boundedFiberJet3EvaluationSecond X :=
    funext (boundedFiberJet3EvaluationFDeriv_fderiv X)
  rw [hFDeriv]
  exact boundedFiberJet3EvaluationSecond_continuous X

/-- Bounded compatible fiber-jet substitution is genuinely C² on the full
completed jet-times-graph Banach space. -/
theorem boundedFiberJet3Evaluation_contDiff_two :
    ContDiff Real 2 (boundedFiberJet3Evaluation X) := by
  refine (contDiff_succ_iff_fderiv (n := 1)).2 ?_
  refine ⟨boundedFiberJet3Evaluation_differentiable X, by norm_num, ?_⟩
  have hFDeriv :
      fderiv Real (boundedFiberJet3Evaluation X) =
        boundedFiberJet3EvaluationFDeriv X :=
    funext (boundedFiberJet3Evaluation_fderiv X)
  rw [hFDeriv]
  exact boundedFiberJet3EvaluationFDeriv_contDiff_one X

/-- Pointwise `arctan` on bounded continuous graphs, obtained by evaluating
the fixed compatible bounded `arctan` fiber jet. -/
def boundedArctanNemytskii (graph : X →ᵇ Real) : X →ᵇ Real :=
  boundedFiberSubstitution X ((boundedFiberArctanJet3 X).1 0) graph

@[simp]
theorem boundedArctanNemytskii_apply
    (graph : X →ᵇ Real) (point : X) :
    boundedArctanNemytskii X graph point = Real.arctan (graph point) :=
  rfl

/-- Pointwise `arctan` is genuinely C² on the completed bounded-graph
Banach space. -/
theorem boundedArctanNemytskii_contDiff_two :
    ContDiff Real 2 (boundedArctanNemytskii X) := by
  have hInput : ContDiff Real 2
      (fun graph : X →ᵇ Real => (boundedFiberArctanJet3 X, graph)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff Real 2
    (fun graph : X →ᵇ Real =>
      boundedFiberJet3Evaluation X (boundedFiberArctanJet3 X, graph))
  exact (boundedFiberJet3Evaluation_contDiff_two X).comp hInput

/-- Public gate bundling C² regularity with the exact first and second
Frechet derivatives used by moving-boundary charts. -/
theorem bounded_fiber_jet_substitution_c2_gate :
    ContDiff Real 2 (boundedFiberJet3Evaluation X) ∧
    (∀ current,
      fderiv Real (boundedFiberJet3Evaluation X) current =
        boundedFiberJet3EvaluationFDeriv X current) ∧
    (∀ current,
      fderiv Real (boundedFiberJet3EvaluationFDeriv X) current =
        boundedFiberJet3EvaluationSecond X current) :=
  ⟨boundedFiberJet3Evaluation_contDiff_two X,
    boundedFiberJet3Evaluation_fderiv X,
    boundedFiberJet3EvaluationFDeriv_fderiv X⟩

end

end P0EFTJanusBoundedFiberJetSubstitutionC2
end JanusFormal
