import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D

/-!
# Nuclear heat regulator for the D9 gauge--ghost block

The existing maximal D9 operator is the diagonal multiplier
`‖covector mode‖²` on eight complex coordinates per mode.  This gate applies
the positive-time Gaussian to that same spectrum and constructs its explicit
rank-one nuclear expansion.

Finite mode packets are nuclear unconditionally.  For an arbitrary continuum
mode type the exact remaining analytic input is isolated as summability of
the positive diagonal heat weights.  The existing D9 Fredholm gap controls
the low spectrum but does not imply this high-energy growth condition.
-/

namespace JanusFormal
namespace P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D
open scoped ENNReal lp

/-- The completed complex D9 coefficient Hilbert space already used by the
maximal Fredholm operator. -/
abbrev D9GaugeGhostHeatHilbert4D (ι : Type*) :=
  D9GaugeGhostUnboundedHilbert ι

/-- Positive-time Gaussian of the exact squared-covector D9 spectrum. -/
def d9GaugeGhostHeatWeight
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) : Real :=
  Real.exp
    (-time.1 * d9GaugeGhostUnboundedWeight covector index)

@[simp]
theorem d9GaugeGhostHeatWeight_apply
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    d9GaugeGhostHeatWeight covector time index =
      Real.exp (-time.1 * normSquared (covector index.1)) :=
  rfl

/-- The standalone D9 heat weight is exactly the D9 coordinate of the
already assembled physical heat regulator. -/
theorem d9GaugeGhostHeatWeight_eq_global
    {ι : Type*}
    (period : Real)
    (hPeriod : period ≠ 0)
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (index : ι × Fin 8) :
    d9GaugeGhostHeatWeight covector time index =
      programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time (.inl index) :=
  rfl

theorem d9GaugeGhostHeatWeight_nonnegative
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    0 ≤ d9GaugeGhostHeatWeight covector time index :=
  (Real.exp_pos _).le

theorem d9GaugeGhostHeatWeight_le_one
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    d9GaugeGhostHeatWeight covector time index ≤ 1 := by
  unfold d9GaugeGhostHeatWeight
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr time.2.le)
    (d9GaugeGhostUnboundedWeight_nonnegative covector index)

/-- Coordinatewise complex-linear D9 heat multiplication. -/
def d9GaugeGhostHeatLinearMap
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    D9GaugeGhostHeatHilbert4D ι →ₗ[Complex]
      D9GaugeGhostHeatHilbert4D ι where
  toFun state := ⟨fun index =>
    (d9GaugeGhostHeatWeight covector time index : Complex) * state index, by
      refine state.2.mono' ?_
      intro index
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (d9GaugeGhostHeatWeight_nonnegative covector time index)]
      simpa using mul_le_mul_of_nonneg_right
        (d9GaugeGhostHeatWeight_le_one covector time index)
        (norm_nonneg (state index))⟩
  map_add' := by
    intro first second
    ext index
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext index
    simp [mul_left_comm]

/-- Bounded D9 heat contraction on the existing maximal-operator Hilbert
space. -/
def d9GaugeGhostHeatOperator
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    D9GaugeGhostHeatHilbert4D ι →L[Complex]
      D9GaugeGhostHeatHilbert4D ι :=
  (d9GaugeGhostHeatLinearMap covector time).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
    intro index
    change ‖(d9GaugeGhostHeatWeight covector time index : Complex) *
      state index‖ ≤ ‖state index‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (d9GaugeGhostHeatWeight_nonnegative covector time index)]
    exact mul_le_of_le_one_left (norm_nonneg (state index))
      (d9GaugeGhostHeatWeight_le_one covector time index))

@[simp]
theorem d9GaugeGhostHeatOperator_apply
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (state : D9GaugeGhostHeatHilbert4D ι)
    (index : ι × Fin 8) :
    d9GaugeGhostHeatOperator covector time state index =
      (d9GaugeGhostHeatWeight covector time index : Complex) *
        state index :=
  rfl

theorem d9GaugeGhostHeatOperator_opNorm_le_one
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    ‖d9GaugeGhostHeatOperator covector time‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Exact continuum regularity condition.  Unlike the already proved
finite-kernel Fredholm gap, this controls the high-energy multiplicity and
growth needed for trace class. -/
def D9GaugeGhostHeatSummability4D
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime) : Prop :=
  Summable (d9GaugeGhostHeatWeight covector time)

/-- The regulated D9 diagonal trace under its exact convergence condition. -/
def d9GaugeGhostHeatTrace
    {ι : Type*}
    (covector : ι → TangentVector3)
    (time : HeatTime) : Real :=
  ∑' index : ι × Fin 8,
    d9GaugeGhostHeatWeight covector time index

/-- Canonical coordinate Hilbert basis of the D9 heat space. -/
def d9GaugeGhostHeatBasis
    (ι : Type*) [DecidableEq ι] :
    HilbertBasis (ι × Fin 8) Complex
      (D9GaugeGhostHeatHilbert4D ι) :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl Complex
      (D9GaugeGhostHeatHilbert4D ι))

@[simp]
theorem d9GaugeGhostHeatBasis_eq_single
    (ι : Type*) [DecidableEq ι]
    (index : ι × Fin 8) :
    d9GaugeGhostHeatBasis ι index =
      lp.single 2 index (1 : Complex) := by
  rw [← HilbertBasis.repr_symm_single
    (d9GaugeGhostHeatBasis ι) index]
  change (d9GaugeGhostHeatBasis ι).repr.symm
    (lp.single 2 index (1 : Complex)) =
      lp.single 2 index (1 : Complex)
  rw [show (d9GaugeGhostHeatBasis ι).repr =
      LinearIsometryEquiv.refl Complex
        (D9GaugeGhostHeatHilbert4D ι) by rfl]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.refl Complex
      (D9GaugeGhostHeatHilbert4D ι)).symm_apply_apply
        (lp.single 2 index (1 : Complex))

theorem d9GaugeGhostHeatBasis_norm
    (ι : Type*) [DecidableEq ι]
    (index : ι × Fin 8) :
    ‖d9GaugeGhostHeatBasis ι index‖ = 1 :=
  (HilbertBasis.orthonormal
    (d9GaugeGhostHeatBasis ι)).1 index

/-- One rank-one coordinate component of the D9 heat operator. -/
def d9GaugeGhostHeatRankOne
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    D9GaugeGhostHeatHilbert4D ι →L[Complex]
      D9GaugeGhostHeatHilbert4D ι :=
  (lp.evalCLM Complex
      (fun _ : ι × Fin 8 => Complex) 2 index).smulRight
    ((d9GaugeGhostHeatWeight covector time index : Complex) •
      d9GaugeGhostHeatBasis ι index)

@[simp]
theorem d9GaugeGhostHeatRankOne_apply
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8)
    (state : D9GaugeGhostHeatHilbert4D ι) :
    d9GaugeGhostHeatRankOne covector time index state =
      state index •
        ((d9GaugeGhostHeatWeight covector time index : Complex) •
          d9GaugeGhostHeatBasis ι index) :=
  rfl

theorem d9GaugeGhostHeatRankOne_isCompact
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    IsCompactOperator
      (d9GaugeGhostHeatRankOne covector time index) := by
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM Complex
        (fun _ : ι × Fin 8 => Complex) 2 index)).clm_comp
      (ContinuousLinearMap.toSpanSingleton Complex
        ((d9GaugeGhostHeatWeight covector time index : Complex) •
          d9GaugeGhostHeatBasis ι index))

private theorem d9GaugeGhostEvalCLM_opNorm_le_one
    (ι : Type*) [DecidableEq ι]
    (index : ι × Fin 8) :
    ‖lp.evalCLM Complex
      (fun _ : ι × Fin 8 => Complex) 2 index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state index‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm
    (by norm_num : (2 : ENNReal) ≠ 0) state index

theorem d9GaugeGhostHeatRankOne_opNorm_le
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index : ι × Fin 8) :
    ‖d9GaugeGhostHeatRankOne covector time index‖ ≤
      d9GaugeGhostHeatWeight covector time index := by
  rw [d9GaugeGhostHeatRankOne,
    ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, d9GaugeGhostHeatBasis_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (d9GaugeGhostHeatWeight_nonnegative covector time index)]
  exact mul_le_of_le_one_left
    (d9GaugeGhostHeatWeight_nonnegative covector time index)
    (d9GaugeGhostEvalCLM_opNorm_le_one ι index)

theorem d9GaugeGhostHeatRankOne_norm_summable
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    Summable (fun index : ι × Fin 8 =>
      ‖d9GaugeGhostHeatRankOne covector time index‖) :=
  hSummable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (d9GaugeGhostHeatRankOne_opNorm_le covector time)

theorem d9GaugeGhostHeatRankOne_summable
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    Summable (d9GaugeGhostHeatRankOne covector time) :=
  Summable.of_norm
    (d9GaugeGhostHeatRankOne_norm_summable
      covector time hSummable)

/-- Arbitrary finite D9 heat truncation. -/
def d9GaugeGhostHeatFiniteTruncation
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (cutoff : Finset (ι × Fin 8)) :
    D9GaugeGhostHeatHilbert4D ι →L[Complex]
      D9GaugeGhostHeatHilbert4D ι :=
  ∑ index ∈ cutoff,
    d9GaugeGhostHeatRankOne covector time index

theorem d9GaugeGhostHeatFiniteTruncation_isCompact
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (cutoff : Finset (ι × Fin 8)) :
    IsCompactOperator
      (d9GaugeGhostHeatFiniteTruncation
        covector time cutoff) := by
  classical
  unfold d9GaugeGhostHeatFiniteTruncation
  refine Finset.sum_induction
    (d9GaugeGhostHeatRankOne covector time)
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro index _
  exact d9GaugeGhostHeatRankOne_isCompact
    covector time index

/-- Operator-norm sum of the explicit rank-one D9 heat components. -/
def d9GaugeGhostHeatNuclearSum
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    D9GaugeGhostHeatHilbert4D ι →L[Complex]
      D9GaugeGhostHeatHilbert4D ι :=
  ∑' index : ι × Fin 8,
    d9GaugeGhostHeatRankOne covector time index

theorem d9GaugeGhostHeatRankOne_on_basis
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (index other : ι × Fin 8) :
    d9GaugeGhostHeatRankOne covector time index
        (d9GaugeGhostHeatBasis ι other) =
      if index = other then
        (d9GaugeGhostHeatWeight covector time other : Complex) •
          d9GaugeGhostHeatBasis ι other
      else 0 := by
  by_cases hIndex : index = other
  · subst index
    simp [d9GaugeGhostHeatRankOne_apply,
      d9GaugeGhostHeatBasis_eq_single]
  · simp [d9GaugeGhostHeatRankOne_apply,
      d9GaugeGhostHeatBasis_eq_single,
      lp.single_apply, hIndex]

theorem d9GaugeGhostHeatNuclearSum_on_basis
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time)
    (index : ι × Fin 8) :
    d9GaugeGhostHeatNuclearSum covector time
        (d9GaugeGhostHeatBasis ι index) =
      (d9GaugeGhostHeatWeight covector time index : Complex) •
        d9GaugeGhostHeatBasis ι index := by
  rw [d9GaugeGhostHeatNuclearSum]
  rw [show
      (∑' other : ι × Fin 8,
        d9GaugeGhostHeatRankOne covector time other)
          (d9GaugeGhostHeatBasis ι index) =
        ∑' other : ι × Fin 8,
          d9GaugeGhostHeatRankOne covector time other
            (d9GaugeGhostHeatBasis ι index) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply Complex
        (D9GaugeGhostHeatHilbert4D ι)
        (d9GaugeGhostHeatBasis ι index)).map_tsum
          (d9GaugeGhostHeatRankOne_summable
            covector time hSummable)]
  rw [tsum_eq_single index]
  · simp
  · intro other hOther
    simp [hOther]

/-- The nuclear rank-one sum is exactly the bounded D9 heat operator. -/
theorem d9GaugeGhostHeatNuclearSum_eq_operator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    d9GaugeGhostHeatNuclearSum covector time =
      d9GaugeGhostHeatOperator covector time := by
  have hDense : Dense
      (Submodule.span Complex
        (Set.range (d9GaugeGhostHeatBasis ι)) :
          Set (D9GaugeGhostHeatHilbert4D ι)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span
      (d9GaugeGhostHeatBasis ι)
  apply ContinuousLinearMap.ext_on
    (s := Set.range (d9GaugeGhostHeatBasis ι)) hDense
  rintro _ ⟨index, rfl⟩
  rw [d9GaugeGhostHeatNuclearSum_on_basis
    covector time hSummable]
  ext other
  rw [d9GaugeGhostHeatOperator_apply,
    d9GaugeGhostHeatBasis_eq_single]
  by_cases hOther : other = index
  · subst other
    rfl
  · rw [lp.single_apply]
    simp [hOther]

theorem d9GaugeGhostHeatFiniteTruncation_tendsto_operator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    Filter.Tendsto
      (d9GaugeGhostHeatFiniteTruncation covector time)
      Filter.atTop
      (nhds (d9GaugeGhostHeatOperator covector time)) := by
  rw [← d9GaugeGhostHeatNuclearSum_eq_operator
    covector time hSummable]
  exact
    (d9GaugeGhostHeatRankOne_summable
      covector time hSummable).hasSum

theorem d9GaugeGhostHeatOperator_isCompact
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    IsCompactOperator
      (d9GaugeGhostHeatOperator covector time) := by
  apply isCompactOperator_of_tendsto
    (d9GaugeGhostHeatFiniteTruncation_tendsto_operator
      covector time hSummable)
  exact Filter.Eventually.of_forall fun cutoff =>
    d9GaugeGhostHeatFiniteTruncation_isCompact
      covector time cutoff

/-- Explicit nuclear certificate for the actual completed D9 heat operator. -/
structure D9GaugeGhostHeatNuclearCertificate4D
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime) where
  components :
    ι × Fin 8 →
      (D9GaugeGhostHeatHilbert4D ι →L[Complex]
        D9GaugeGhostHeatHilbert4D ι)
  summable_norm :
    Summable (fun index => ‖components index‖)
  operator_eq_tsum :
    d9GaugeGhostHeatOperator covector time =
      ∑' index, components index
  operator_compact :
    IsCompactOperator
      (d9GaugeGhostHeatOperator covector time)
  trace_eq :
    (∑' index : ι × Fin 8,
      d9GaugeGhostHeatWeight covector time index) =
        d9GaugeGhostHeatTrace covector time

def d9GaugeGhostHeatNuclearCertificate4D
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    D9GaugeGhostHeatNuclearCertificate4D
      covector time where
  components := d9GaugeGhostHeatRankOne covector time
  summable_norm :=
    d9GaugeGhostHeatRankOne_norm_summable
      covector time hSummable
  operator_eq_tsum :=
    (d9GaugeGhostHeatNuclearSum_eq_operator
      covector time hSummable).symm
  operator_compact :=
    d9GaugeGhostHeatOperator_isCompact
      covector time hSummable
  trace_eq := rfl

/-- Every already existing finite D9 packet satisfies the exact heat
summability condition without further ellipticity or growth assumptions. -/
theorem d9GaugeGhostHeatSummability_of_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    D9GaugeGhostHeatSummability4D covector time := by
  apply summable_of_hasFiniteSupport
  exact Set.finite_univ.subset
    (fun _ _ => Set.mem_univ _)

/-- Unconditional nuclear/compact heat gate on every finite D9 packet. -/
theorem d9GaugeGhostFiniteHeat_nuclear_gate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime) :
    Nonempty
      (D9GaugeGhostHeatNuclearCertificate4D
        covector time) :=
  ⟨d9GaugeGhostHeatNuclearCertificate4D
    covector time
    (d9GaugeGhostHeatSummability_of_finite
      covector time)⟩

/-- Continuum D9 heat gate with the precise remaining high-energy growth
input exposed as a single hypothesis. -/
theorem d9GaugeGhostContinuumHeat_nuclear_gate
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable :
      D9GaugeGhostHeatSummability4D covector time) :
    Nonempty
      (D9GaugeGhostHeatNuclearCertificate4D
        covector time) :=
  ⟨d9GaugeGhostHeatNuclearCertificate4D
    covector time hSummable⟩

end
end P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D
end JanusFormal
