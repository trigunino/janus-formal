import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatTraceCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

/-!
# Elliptic L2 contract and nuclear heat regulator for the LL Hessian

The existing LL completion uses its Hessian as the Hilbert scalar product.
Its Riesz representative is consequently the identity, whose positive-time
heat is not compact in infinite dimension.  This gate does not duplicate that
no-go construction.

Instead it isolates the missing order-sensitive realization on the genuine
LL-flux `L2` space.  The contract requires an unbounded self-adjoint operator
whose smooth core represents the already proved LL Hessian, one compact
resolvent, a complete eigenbasis, and the precise heat summability estimate
not implied by compact resolvent alone.  From those inputs the positive-time
heat operator is constructed as an operator-norm summable rank-one series.
Compactness and an explicit nuclear certificate are then proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D

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
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusCircleDiracHeatTraceCancellation

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

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Genuine `L2` space of the four-component LL flux. -/
abbrev LLFluxL2 (llData : PositiveLLH1Data period hPeriod) :=
  Lp LLFieldFiber (2 : ENNReal) llData.mu

/-- A smooth LL direction as an actual vector-valued `L2` field. -/
def llH1SmoothToFluxL2
    (llData : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod llData) :
    LLFluxL2 period hPeriod llData := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  exact
    (smoothThroatField_memLp period hPeriod LLFieldFiber llData.mu
      direction.toTest).toLp direction.toTest.toFun

theorem llH1SmoothToFluxL2_ae
    (llData : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod llData) :
    (llH1SmoothToFluxL2 period hPeriod llData direction :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[llData.mu]
        direction.toTest.toFun := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  exact
    (smoothThroatField_memLp period hPeriod LLFieldFiber llData.mu
      direction.toTest).coeFn_toLp

/-- The smooth LL-to-`L2` inclusion is genuinely linear. -/
def llH1SmoothToFluxL2LinearMap
    (llData : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod llData →ₗ[Real]
      LLFluxL2 period hPeriod llData where
  toFun := llH1SmoothToFluxL2 period hPeriod llData
  map_add' first second := by
    letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
    apply Lp.ext
    filter_upwards
      [llH1SmoothToFluxL2_ae period hPeriod llData (first + second),
       llH1SmoothToFluxL2_ae period hPeriod llData first,
       llH1SmoothToFluxL2_ae period hPeriod llData second,
       Lp.coeFn_add
         (llH1SmoothToFluxL2 period hPeriod llData first)
         (llH1SmoothToFluxL2 period hPeriod llData second)]
      with point hSum hFirst hSecond hAdd
    rw [hSum, hAdd]
    change first.toTest point + second.toTest point =
      (llH1SmoothToFluxL2 period hPeriod llData first :
        EffectiveThroat period hPeriod → LLFieldFiber) point +
      (llH1SmoothToFluxL2 period hPeriod llData second :
        EffectiveThroat period hPeriod → LLFieldFiber) point
    rw [hFirst, hSecond]
  map_smul' scalar direction := by
    letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
    apply Lp.ext
    filter_upwards
      [llH1SmoothToFluxL2_ae period hPeriod llData (scalar • direction),
       llH1SmoothToFluxL2_ae period hPeriod llData direction,
       Lp.coeFn_smul scalar
         (llH1SmoothToFluxL2 period hPeriod llData direction)]
      with point hScaled hDirection hSmul
    rw [hScaled]
    simp only [RingHom.id_apply]
    rw [hSmul]
    change scalar • direction.toTest point =
      scalar •
        (llH1SmoothToFluxL2 period hPeriod llData direction :
          EffectiveThroat period hPeriod → LLFieldFiber) point
    rw [hDirection]

local instance llFluxL2LinearPMapStar
    (llData : PositiveLLH1Data period hPeriod) :
    Star (LLFluxL2 period hPeriod llData →ₗ.[Real]
      LLFluxL2 period hPeriod llData) :=
  LinearPMap.instStar

/-- Minimal analytic data still needed for the LL regulator on its natural
`L2` space.  `heatSummable` is kept separate from compact resolvent because
the latter alone does not imply trace class at every positive time. -/
structure ProgramPLL2EllipticHeatData
    (llData : PositiveLLH1Data period hPeriod)
    (Mode : Type*) [DecidableEq Mode] where
  operator :
    LLFluxL2 period hPeriod llData →ₗ.[Real]
      LLFluxL2 period hPeriod llData
  smoothCore :
    LLH1Smooth period hPeriod llData →ₗ[Real] operator.domain
  smoothCore_coe :
    ∀ direction,
      ((smoothCore direction : operator.domain) :
        LLFluxL2 period hPeriod llData) =
      llH1SmoothToFluxL2 period hPeriod llData direction
  domain_dense :
    Dense (operator.domain : Set (LLFluxL2 period hPeriod llData))
  selfAdjoint : IsSelfAdjoint operator
  hessian_pairing :
    ∀ first second,
      inner Real (operator (smoothCore first))
          (llH1SmoothToFluxL2 period hPeriod llData second) =
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          llData.frame llData.fields first.toTest second.toTest llData.mu
  referenceParameter : Real
  resolvent :
    LLFluxL2 period hPeriod llData →L[Real]
      LLFluxL2 period hPeriod llData
  resolvent_mem_domain :
    ∀ source, resolvent source ∈ operator.domain
  resolvent_right_inverse :
    ∀ source,
      operator ⟨resolvent source, resolvent_mem_domain source⟩ -
          referenceParameter • resolvent source =
        source
  resolvent_left_inverse :
    ∀ field : operator.domain,
      resolvent
          (operator field -
            referenceParameter •
              (field : LLFluxL2 period hPeriod llData)) =
        (field : LLFluxL2 period hPeriod llData)
  resolvent_compact : IsCompactOperator resolvent
  basis :
    HilbertBasis Mode Real (LLFluxL2 period hPeriod llData)
  eigenvalue : Mode → Real
  basis_mem_domain :
    ∀ mode, basis mode ∈ operator.domain
  operator_on_basis :
    ∀ mode,
      operator ⟨basis mode, basis_mem_domain mode⟩ =
        eigenvalue mode • basis mode
  heatSummable :
    ∀ time : HeatTime,
      Summable
        (fun mode =>
          Real.exp (-time.1 * eigenvalue mode ^ 2))

/-- Positive Gaussian weight of the genuine order-sensitive LL realization. -/
def programPLL2HeatWeight
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) : Real :=
  Real.exp (-time.1 * analytic.eigenvalue mode ^ 2)

theorem programPLL2HeatWeight_pos
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) :
    0 < programPLL2HeatWeight period hPeriod analytic time mode :=
  Real.exp_pos _

theorem programPLL2HeatWeight_summable
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    Summable
      (programPLL2HeatWeight period hPeriod analytic time) :=
  analytic.heatSummable time

/-- One heat-weighted spectral rank-one projection. -/
def programPLL2HeatRankOne
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) :
    LLFluxL2 period hPeriod llData →L[Real]
      LLFluxL2 period hPeriod llData :=
  programPLL2HeatWeight period hPeriod analytic time mode •
    InnerProductSpace.rankOne Real
      (analytic.basis mode) (analytic.basis mode)

theorem programPLL2HeatRankOne_norm
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) :
    ‖programPLL2HeatRankOne period hPeriod analytic time mode‖ =
      programPLL2HeatWeight period hPeriod analytic time mode := by
  rw [programPLL2HeatRankOne, norm_smul,
    InnerProductSpace.norm_rankOne,
    (HilbertBasis.orthonormal analytic.basis).1 mode,
    mul_one, Real.norm_eq_abs,
    abs_of_pos (programPLL2HeatWeight_pos
      period hPeriod analytic time mode)]
  ring

theorem programPLL2HeatRankOne_norm_summable
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    Summable
      (fun mode =>
        ‖programPLL2HeatRankOne period hPeriod analytic time mode‖) := by
  simpa only [programPLL2HeatRankOne_norm] using
    programPLL2HeatWeight_summable period hPeriod analytic time

theorem programPLL2HeatRankOne_summable
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    Summable (programPLL2HeatRankOne period hPeriod analytic time) :=
  Summable.of_norm
    (programPLL2HeatRankOne_norm_summable
      period hPeriod analytic time)

/-- Nuclear positive-time LL heat operator. -/
def programPLL2HeatOperator
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    LLFluxL2 period hPeriod llData →L[Real]
      LLFluxL2 period hPeriod llData :=
  ∑' mode, programPLL2HeatRankOne period hPeriod analytic time mode

theorem programPLL2HeatRankOne_on_basis
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode other : Mode) :
    programPLL2HeatRankOne period hPeriod analytic time mode
        (analytic.basis other) =
      if mode = other then
        programPLL2HeatWeight period hPeriod analytic time other •
          analytic.basis other
      else 0 := by
  rw [programPLL2HeatRankOne, smul_apply,
    InnerProductSpace.rankOne_apply]
  have hInner :=
    (orthonormal_iff_ite.mp
      (HilbertBasis.orthonormal analytic.basis)) mode other
  rw [hInner]
  by_cases hMode : mode = other
  · subst mode
    simp
  · simp [hMode]

/-- The nuclear sum is the expected spectral Gaussian on every eigenmode. -/
theorem programPLL2HeatOperator_on_basis
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) :
    programPLL2HeatOperator period hPeriod analytic time
        (analytic.basis mode) =
      programPLL2HeatWeight period hPeriod analytic time mode •
        analytic.basis mode := by
  rw [programPLL2HeatOperator]
  rw [show
      (∑' other,
        programPLL2HeatRankOne period hPeriod analytic time other)
          (analytic.basis mode) =
        ∑' other,
          programPLL2HeatRankOne period hPeriod analytic time other
            (analytic.basis mode) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply Real
        (LLFluxL2 period hPeriod llData)
        (analytic.basis mode)).map_tsum
          (programPLL2HeatRankOne_summable
            period hPeriod analytic time)]
  rw [tsum_eq_single mode]
  · simp [programPLL2HeatRankOne_on_basis]
  · intro other hOther
    simp [programPLL2HeatRankOne_on_basis, hOther]

private theorem programPLL2HeatRankOne_isCompact
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) (mode : Mode) :
    IsCompactOperator
      (programPLL2HeatRankOne period hPeriod analytic time mode) := by
  rw [programPLL2HeatRankOne]
  have hCompact :
      IsCompactOperator
        (InnerProductSpace.rankOne Real
          (analytic.basis mode) (analytic.basis mode)) := by
    rw [InnerProductSpace.rankOne_def']
    exact
      (isCompactOperator_of_locallyCompactSpace_dom
        (innerSL Real (analytic.basis mode))).clm_comp
          (ContinuousLinearMap.toSpanSingleton Real (analytic.basis mode))
  exact hCompact.smul
    (programPLL2HeatWeight period hPeriod analytic time mode)

/-- Nuclear summability gives compactness, independently of the old
identity-Riesz LL no-go. -/
theorem programPLL2HeatOperator_isCompact
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    IsCompactOperator
      (programPLL2HeatOperator period hPeriod analytic time) := by
  refine isCompactOperator_of_tendsto
    (l := (SummationFilter.unconditional Mode).filter)
    (F := fun modes : Finset Mode =>
      ∑ mode ∈ modes,
        programPLL2HeatRankOne period hPeriod analytic time mode)
    (f := programPLL2HeatOperator period hPeriod analytic time)
    (programPLL2HeatRankOne_summable
      period hPeriod analytic time).hasSum ?_
  filter_upwards [] with modes
  refine Finset.sum_induction
    (fun mode =>
      programPLL2HeatRankOne period hPeriod analytic time mode)
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro mode _
  exact programPLL2HeatRankOne_isCompact
    period hPeriod analytic time mode

/-- Concrete trace of the rank-one LL heat expansion. -/
def programPLL2HeatNuclearTrace
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) : Real :=
  ∑' mode, programPLL2HeatWeight period hPeriod analytic time mode

/-- Explicit nuclear certificate used in the absence of a general Mathlib
trace-class operator API. -/
structure ProgramPLL2HeatNuclearCertificate
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) where
  components : Mode →
    (LLFluxL2 period hPeriod llData →L[Real]
      LLFluxL2 period hPeriod llData)
  summable_norm : Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    programPLL2HeatOperator period hPeriod analytic time =
      ∑' mode, components mode
  nuclear_norm_eq_trace :
    (∑' mode, ‖components mode‖) =
      programPLL2HeatNuclearTrace period hPeriod analytic time

def programPLL2HeatNuclearCertificate
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    ProgramPLL2HeatNuclearCertificate
      period hPeriod analytic time where
  components :=
    programPLL2HeatRankOne period hPeriod analytic time
  summable_norm :=
    programPLL2HeatRankOne_norm_summable
      period hPeriod analytic time
  operator_eq_tsum := rfl
  nuclear_norm_eq_trace := by
    unfold programPLL2HeatNuclearTrace
    apply tsum_congr
    intro mode
    exact programPLL2HeatRankOne_norm
      period hPeriod analytic time mode

/-- Conditional LL closure gate: the contract simultaneously records the
unchanged action Hessian, a genuine compact resolvent, and a compact nuclear
positive-time regulator on the natural `L2` realization. -/
theorem programPLL2EllipticNuclearHeat_regulator_gate
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    (∀ first second,
      inner Real (analytic.operator (analytic.smoothCore first))
          (llH1SmoothToFluxL2 period hPeriod llData second) =
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          llData.frame llData.fields first.toTest second.toTest llData.mu) ∧
      IsSelfAdjoint analytic.operator ∧
      IsCompactOperator analytic.resolvent ∧
      IsCompactOperator
        (programPLL2HeatOperator period hPeriod analytic time) ∧
      Summable
        (fun mode =>
          ‖programPLL2HeatRankOne
            period hPeriod analytic time mode‖) := by
  exact ⟨analytic.hessian_pairing, analytic.selfAdjoint,
    analytic.resolvent_compact,
    programPLL2HeatOperator_isCompact period hPeriod analytic time,
    programPLL2HeatRankOne_norm_summable period hPeriod analytic time⟩

end
end P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
end JanusFormal
