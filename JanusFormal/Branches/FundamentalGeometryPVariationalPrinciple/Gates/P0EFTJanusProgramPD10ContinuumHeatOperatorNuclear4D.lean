import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D

/-!
# Nuclear heat operator on the complete D10 spectrum

The summable continuum D10 Gaussian acts diagonally on the genuine complex
`ℓ²` mode space.  It is a contraction and is the operator-norm sum of explicit
rank-one spectral projections whose norm series is summable.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open scoped ENNReal lp

/-- Complex Hilbert space of all multiplicity-aware D10 coefficients. -/
abbrev ProgramPD10HeatHilbert4D (data : ProductThroatSpectralData) :=
  lp (fun _ : ProgramPD10Mode4D data => Complex) 2

theorem programPD10HeatWeight_le_one
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    programPD10HeatWeight data time mode ≤ 1 := by
  unfold programPD10HeatWeight
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.2.le)
    (product_spectrum_has_positive_gap data mode.separatedMode).le

/-- Coordinatewise D10 Gaussian multiplication. -/
def programPD10HeatLinearMap
    (data : ProductThroatSpectralData) (time : HeatTime) :
    ProgramPD10HeatHilbert4D data →ₗ[Complex]
      ProgramPD10HeatHilbert4D data where
  toFun state := ⟨fun mode =>
    (programPD10HeatWeight data time mode : Complex) * state mode, by
      refine state.2.mono' ?_
      intro mode
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
      simpa using mul_le_mul_of_nonneg_right
        (programPD10HeatWeight_le_one data time mode)
        (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- Bounded heat contraction on the complete D10 Hilbert space. -/
def programPD10HeatOperator
    (data : ProductThroatSpectralData) (time : HeatTime) :
    ProgramPD10HeatHilbert4D data →L[Complex]
      ProgramPD10HeatHilbert4D data :=
  (programPD10HeatLinearMap data time).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
    intro mode
    change ‖(programPD10HeatWeight data time mode : Complex) *
      state mode‖ ≤ ‖state mode‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
    exact mul_le_of_le_one_left (norm_nonneg (state mode))
      (programPD10HeatWeight_le_one data time mode))

@[simp]
theorem programPD10HeatOperator_apply
    (data : ProductThroatSpectralData) (time : HeatTime)
    (state : ProgramPD10HeatHilbert4D data)
    (mode : ProgramPD10Mode4D data) :
    programPD10HeatOperator data time state mode =
      (programPD10HeatWeight data time mode : Complex) * state mode :=
  rfl

theorem programPD10HeatOperator_opNorm_le_one
    (data : ProductThroatSpectralData) (time : HeatTime) :
    ‖programPD10HeatOperator data time‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Canonical Hilbert basis of the complete D10 coefficient space. -/
def programPD10HeatBasis (data : ProductThroatSpectralData) :
    HilbertBasis (ProgramPD10Mode4D data) Complex
      (ProgramPD10HeatHilbert4D data) :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl Complex (ProgramPD10HeatHilbert4D data))

@[simp]
theorem programPD10HeatBasis_eq_single
    (data : ProductThroatSpectralData) (mode : ProgramPD10Mode4D data) :
    programPD10HeatBasis data mode = lp.single 2 mode (1 : Complex) := by
  rw [← HilbertBasis.repr_symm_single (programPD10HeatBasis data) mode]
  change (programPD10HeatBasis data).repr.symm
    (lp.single 2 mode (1 : Complex)) = lp.single 2 mode (1 : Complex)
  rw [show (programPD10HeatBasis data).repr =
      LinearIsometryEquiv.refl Complex (ProgramPD10HeatHilbert4D data) by rfl]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.refl Complex
      (ProgramPD10HeatHilbert4D data)).symm_apply_apply
        (lp.single 2 mode (1 : Complex))

theorem programPD10HeatBasis_norm
    (data : ProductThroatSpectralData) (mode : ProgramPD10Mode4D data) :
    ‖programPD10HeatBasis data mode‖ = 1 :=
  (HilbertBasis.orthonormal (programPD10HeatBasis data)).1 mode

/-- One rank-one summand of the complete D10 heat operator. -/
def programPD10HeatRankOne
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    ProgramPD10HeatHilbert4D data →L[Complex]
      ProgramPD10HeatHilbert4D data :=
  (lp.evalCLM Complex
      (fun _ : ProgramPD10Mode4D data => Complex) 2 mode).smulRight
    ((programPD10HeatWeight data time mode : Complex) •
      programPD10HeatBasis data mode)

@[simp]
theorem programPD10HeatRankOne_apply
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data)
    (state : ProgramPD10HeatHilbert4D data) :
    programPD10HeatRankOne data time mode state =
      state mode •
        ((programPD10HeatWeight data time mode : Complex) •
          programPD10HeatBasis data mode) :=
  rfl

/-- Every spectral summand is compact because it factors through `ℂ`. -/
theorem programPD10HeatRankOne_isCompact
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    IsCompactOperator (programPD10HeatRankOne data time mode) := by
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM Complex
        (fun _ : ProgramPD10Mode4D data => Complex) 2 mode)).clm_comp
      (ContinuousLinearMap.toSpanSingleton Complex
        ((programPD10HeatWeight data time mode : Complex) •
          programPD10HeatBasis data mode))

private theorem programPD10EvalCLM_opNorm_le_one
    (data : ProductThroatSpectralData) (mode : ProgramPD10Mode4D data) :
    ‖lp.evalCLM Complex
      (fun _ : ProgramPD10Mode4D data => Complex) 2 mode‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state mode‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    state mode

theorem programPD10HeatRankOne_opNorm_le
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    ‖programPD10HeatRankOne data time mode‖ ≤
      programPD10HeatWeight data time mode := by
  rw [programPD10HeatRankOne, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, programPD10HeatBasis_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
  exact mul_le_of_le_one_left
    (programPD10HeatWeight_nonnegative data time mode)
    (programPD10EvalCLM_opNorm_le_one data mode)

theorem programPD10HeatRankOne_norm_summable
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Summable (fun mode : ProgramPD10Mode4D data =>
      ‖programPD10HeatRankOne data time mode‖) :=
  (programPD10HeatWeight_summable data time).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (programPD10HeatRankOne_opNorm_le data time)

theorem programPD10HeatRankOne_summable
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Summable (programPD10HeatRankOne data time) :=
  Summable.of_norm (programPD10HeatRankOne_norm_summable data time)

/-- Arbitrary finite D10 heat truncation. -/
def programPD10HeatFiniteTruncation
    (data : ProductThroatSpectralData) (time : HeatTime)
    (cutoff : Finset (ProgramPD10Mode4D data)) :
    ProgramPD10HeatHilbert4D data →L[Complex]
      ProgramPD10HeatHilbert4D data :=
  ∑ mode ∈ cutoff, programPD10HeatRankOne data time mode

theorem programPD10HeatFiniteTruncation_isCompact
    (data : ProductThroatSpectralData) (time : HeatTime)
    (cutoff : Finset (ProgramPD10Mode4D data)) :
    IsCompactOperator (programPD10HeatFiniteTruncation data time cutoff) := by
  classical
  unfold programPD10HeatFiniteTruncation
  refine Finset.sum_induction
    (programPD10HeatRankOne data time)
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro mode _
  exact programPD10HeatRankOne_isCompact data time mode

/-- Operator-norm sum of all complete D10 rank-one heat components. -/
def programPD10HeatNuclearSum
    (data : ProductThroatSpectralData) (time : HeatTime) :
    ProgramPD10HeatHilbert4D data →L[Complex]
      ProgramPD10HeatHilbert4D data :=
  ∑' mode : ProgramPD10Mode4D data,
    programPD10HeatRankOne data time mode

theorem programPD10HeatRankOne_on_basis
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode other : ProgramPD10Mode4D data) :
    programPD10HeatRankOne data time mode
        (programPD10HeatBasis data other) =
      if mode = other then
        (programPD10HeatWeight data time other : Complex) •
          programPD10HeatBasis data other
      else 0 := by
  by_cases hMode : mode = other
  · subst mode
    simp [programPD10HeatRankOne_apply, programPD10HeatBasis_eq_single]
  · simp [programPD10HeatRankOne_apply, programPD10HeatBasis_eq_single,
      lp.single_apply, hMode]

theorem programPD10HeatNuclearSum_on_basis
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    programPD10HeatNuclearSum data time (programPD10HeatBasis data mode) =
      (programPD10HeatWeight data time mode : Complex) •
        programPD10HeatBasis data mode := by
  rw [programPD10HeatNuclearSum]
  rw [show
      (∑' other : ProgramPD10Mode4D data,
        programPD10HeatRankOne data time other)
          (programPD10HeatBasis data mode) =
        ∑' other : ProgramPD10Mode4D data,
          programPD10HeatRankOne data time other
            (programPD10HeatBasis data mode) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply Complex (ProgramPD10HeatHilbert4D data)
        (programPD10HeatBasis data mode)).map_tsum
          (programPD10HeatRankOne_summable data time)]
  rw [tsum_eq_single mode]
  · simp
  · intro other hOther
    simp [hOther]

/-- The rank-one nuclear series is exactly the bounded D10 heat operator. -/
theorem programPD10HeatNuclearSum_eq_operator
    (data : ProductThroatSpectralData) (time : HeatTime) :
    programPD10HeatNuclearSum data time =
      programPD10HeatOperator data time := by
  have hDense : Dense
      (Submodule.span Complex (Set.range (programPD10HeatBasis data)) :
        Set (ProgramPD10HeatHilbert4D data)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span (programPD10HeatBasis data)
  apply ContinuousLinearMap.ext_on
    (s := Set.range (programPD10HeatBasis data)) hDense
  rintro _ ⟨mode, rfl⟩
  rw [programPD10HeatNuclearSum_on_basis]
  ext other
  rw [programPD10HeatOperator_apply, programPD10HeatBasis_eq_single]
  by_cases hOther : other = mode
  · subst other
    change (programPD10HeatWeight data time mode : Complex) *
      ((lp.single 2 mode (1 : Complex) :
        ProgramPD10HeatHilbert4D data) mode) =
        (programPD10HeatWeight data time mode : Complex) *
          ((lp.single 2 mode (1 : Complex) :
            ProgramPD10HeatHilbert4D data) mode)
    rfl
  · change (programPD10HeatWeight data time mode : Complex) *
      ((lp.single 2 mode (1 : Complex) :
        ProgramPD10HeatHilbert4D data) other) =
        (programPD10HeatWeight data time other : Complex) *
          ((lp.single 2 mode (1 : Complex) :
            ProgramPD10HeatHilbert4D data) other)
    rw [lp.single_apply]
    simp [hOther]

/-- Finite spectral truncations converge in operator norm to the full D10 heat
operator. -/
theorem programPD10HeatFiniteTruncation_tendsto_operator
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Filter.Tendsto (programPD10HeatFiniteTruncation data time)
      Filter.atTop (nhds (programPD10HeatOperator data time)) := by
  rw [← programPD10HeatNuclearSum_eq_operator data time]
  exact (programPD10HeatRankOne_summable data time).hasSum

/-- The complete positive-time D10 heat operator is compact. -/
theorem programPD10HeatOperator_isCompact
    (data : ProductThroatSpectralData) (time : HeatTime) :
    IsCompactOperator (programPD10HeatOperator data time) := by
  apply isCompactOperator_of_tendsto
    (programPD10HeatFiniteTruncation_tendsto_operator data time)
  exact Filter.Eventually.of_forall fun cutoff =>
    programPD10HeatFiniteTruncation_isCompact data time cutoff

/-- Concrete nuclear certificate for the complete D10 heat operator. -/
structure ProgramPD10HeatNuclearCertificate4D
    (data : ProductThroatSpectralData) (time : HeatTime) where
  components :
    ProgramPD10Mode4D data →
      (ProgramPD10HeatHilbert4D data →L[Complex]
        ProgramPD10HeatHilbert4D data)
  summable_norm : Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    programPD10HeatOperator data time = ∑' mode, components mode
  operator_compact :
    IsCompactOperator (programPD10HeatOperator data time)
  trace_eq :
    (∑' mode : ProgramPD10Mode4D data,
      programPD10HeatWeight data time mode) =
        programPD10InfiniteHeatTrace data time

def programPD10HeatNuclearCertificate4D
    (data : ProductThroatSpectralData) (time : HeatTime) :
    ProgramPD10HeatNuclearCertificate4D data time where
  components := programPD10HeatRankOne data time
  summable_norm := programPD10HeatRankOne_norm_summable data time
  operator_eq_tsum :=
    (programPD10HeatNuclearSum_eq_operator data time).symm
  operator_compact :=
    programPD10HeatOperator_isCompact data time
  trace_eq := rfl

theorem programPD10HeatNuclearNormSum_le_trace
    (data : ProductThroatSpectralData) (time : HeatTime) :
    (∑' mode : ProgramPD10Mode4D data,
      ‖programPD10HeatRankOne data time mode‖) ≤
        programPD10InfiniteHeatTrace data time := by
  unfold programPD10InfiniteHeatTrace
  exact Summable.tsum_le_tsum
    (programPD10HeatRankOne_opNorm_le data time)
    (programPD10HeatRankOne_norm_summable data time)
    (programPD10HeatWeight_summable data time)

end

end P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
end JanusFormal
