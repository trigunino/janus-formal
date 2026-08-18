import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRenormalizedNuclearDuhamelBochnerOperatorIntegral4D

/-!
# Countable rank-one construction of the nuclear trace Bochner bridge

An operator-valued integrand is expanded into a countable series of rank-one
summands.  Summability of their integrated operator norms justifies integrating
the operator series term by term.  The existing scalar interchange packet does
the same for the trace series.  Consequently both nuclearity of the Bochner
integral and commutation of intrinsic trace with that integral are outputs.

The only trace-specific input is the reusable ambient theorem that nuclear
rank-one trace is presentation-independent; neither final bridge conclusion
is assumed.  In finite dimension that theorem is constructed canonically from
`LinearMap.trace`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCountableRankOneNuclearTraceBochnerBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D
open P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelBochnerOperatorIntegral4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Rank-one summand data sufficient to construct the intrinsic nuclear trace
of one operator-valued Bochner integral. -/
structure CountableRankOneNuclearTraceBochnerBridgeData
    (timeRegion : Set Real)
    (integrand : Real → E →L[Real] E)
    (pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)) where
  Index : Type v
  index_countable : Countable Index
  coefficient : Index → Real → Real
  leftVector : Index → E
  rightVector : Index → E
  pointwise_nuclearNorm_summable : ∀ time,
    Summable (fun index ↦
      |coefficient index time| * ‖leftVector index‖ * ‖rightVector index‖)
  integrand_eq_tsum : ∀ time,
    integrand time = ∑' index,
      coefficient index time •
        InnerProductSpace.rankOne Real
          (leftVector index) (rightVector index)
  operatorSummand_integrable : ∀ index,
    Integrable
      (fun time ↦ coefficient index time •
        InnerProductSpace.rankOne Real
          (leftVector index) (rightVector index))
      (volume.restrict timeRegion)
  operatorSummand_integral_norm_summable :
    Summable (fun index ↦
      ∫ time in timeRegion,
        ‖coefficient index time •
          InnerProductSpace.rankOne Real
            (leftVector index) (rightVector index)‖)
  traceInterchange :
    CountableTraceIntegralInterchangeData
      (volume.restrict timeRegion)
      (fun index time ↦ coefficient index time *
        inner Real (leftVector index) (rightVector index))
  traceUniqueness : NuclearRankOneTraceUniquenessData.{u, v} (E := E)

namespace CountableRankOneNuclearTraceBochnerBridgeData

/-- One operator-valued rank-one summand. -/
def operatorSummand
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (index : data.Index) (time : Real) : E →L[Real] E :=
  data.coefficient index time •
    InnerProductSpace.rankOne Real
      (data.leftVector index) (data.rightVector index)

/-- Scalar trace of one rank-one summand. -/
def traceSummand
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (index : data.Index) (time : Real) : Real :=
  data.coefficient index time *
    inner Real (data.leftVector index) (data.rightVector index)

/-- Coefficient obtained by scalar Bochner integration. -/
def integratedCoefficient
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (index : data.Index) : Real :=
  ∫ time in timeRegion, data.coefficient index time

/-- Nuclear summability implies summability of every pointwise scalar trace
series. -/
theorem pointwise_trace_summable
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (time : Real) :
    Summable (fun index ↦ data.traceSummand index time) := by
  apply (data.pointwise_nuclearNorm_summable time).of_norm_bounded
  intro index
  calc
    ‖data.traceSummand index time‖ =
        |data.coefficient index time| *
          |inner Real (data.leftVector index) (data.rightVector index)| := by
      simp [traceSummand]
    _ ≤ |data.coefficient index time| *
          (‖data.leftVector index‖ * ‖data.rightVector index‖) :=
      mul_le_mul_of_nonneg_left
        (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = |data.coefficient index time| *
          ‖data.leftVector index‖ * ‖data.rightVector index‖ := by
      ring

/-- Certified rank-one expansion at each time. -/
def pointwiseExpansion
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (time : Real) :
    SummableRankOneOperatorExpansion.{v} (integrand time) where
  Index := data.Index
  coefficient := fun index ↦ data.coefficient index time
  leftVector := data.leftVector
  rightVector := data.rightVector
  summable_nuclearNorm := data.pointwise_nuclearNorm_summable time
  trace_summable := data.pointwise_trace_summable time
  operator_eq_tsum := data.integrand_eq_tsum time

/-- Pointwise intrinsic trace is computed by the given spectral series. -/
theorem pointwiseTrace_eq_tsum
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (time : Real) :
    intrinsicNuclearTrace (pointwiseTraceClass time) =
      ∑' index, data.traceSummand index time := by
  exact ((pointwiseTraceClass time).expansionTrace_eq
    (data.pointwiseExpansion time)).symm

/-- Integrated operator-norm summability justifies termwise integration of
the operator series. -/
theorem operatorIntegral_eq_integratedSeries
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    (∫ time in timeRegion, integrand time) =
      ∑' index,
        data.integratedCoefficient index •
          InnerProductSpace.rankOne Real
            (data.leftVector index) (data.rightVector index) := by
  letI : Countable data.Index := data.index_countable
  calc
    (∫ time in timeRegion, integrand time) =
        ∫ time in timeRegion, ∑' index, data.operatorSummand index time := by
      apply integral_congr_ae
      filter_upwards [] with time
      exact data.integrand_eq_tsum time
    _ = ∑' index,
        ∫ time in timeRegion, data.operatorSummand index time :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm
        data.operatorSummand_integrable
        data.operatorSummand_integral_norm_summable).symm
    _ = ∑' index,
        data.integratedCoefficient index •
          InnerProductSpace.rankOne Real
            (data.leftVector index) (data.rightVector index) := by
      apply tsum_congr
      intro index
      simpa [operatorSummand, integratedCoefficient] using
        (integral_smul_const
          (fun time ↦ data.coefficient index time)
          (InnerProductSpace.rankOne Real
            (data.leftVector index) (data.rightVector index)) :
          (∫ time in timeRegion,
            data.coefficient index time •
              InnerProductSpace.rankOne Real
                (data.leftVector index) (data.rightVector index)) = _)

/-- The integrated coefficients satisfy the nuclear norm summability needed
for an intrinsic rank-one expansion. -/
theorem integrated_nuclearNorm_summable
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    Summable (fun index ↦
      |data.integratedCoefficient index| *
        ‖data.leftVector index‖ * ‖data.rightVector index‖) := by
  apply data.operatorSummand_integral_norm_summable.of_nonneg_of_le
  · intro index
    positivity
  · intro index
    calc
      |data.integratedCoefficient index| *
          ‖data.leftVector index‖ * ‖data.rightVector index‖ =
        ‖data.integratedCoefficient index •
          InnerProductSpace.rankOne Real
            (data.leftVector index) (data.rightVector index)‖ := by
        rw [norm_smul, InnerProductSpace.norm_rankOne, Real.norm_eq_abs]
        ring
      _ = ‖∫ time in timeRegion, data.operatorSummand index time‖ := by
        change
          ‖data.integratedCoefficient index •
              InnerProductSpace.rankOne Real
                (data.leftVector index) (data.rightVector index)‖ =
            ‖∫ time in timeRegion,
              data.coefficient index time •
                InnerProductSpace.rankOne Real
                  (data.leftVector index) (data.rightVector index)‖
        rw [integral_smul_const]
        rfl
      _ ≤ ∫ time in timeRegion,
          ‖data.operatorSummand index time‖ :=
        norm_integral_le_integral_norm _

/-- The scalar interchange certificate implies summability of the integrated
trace coefficients. -/
theorem integrated_trace_summable
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    Summable (fun index ↦
      data.integratedCoefficient index *
        inner Real (data.leftVector index) (data.rightVector index)) := by
  have hIntegralSummable : Summable (fun index ↦
      ∫ time in timeRegion, data.traceSummand index time) :=
    data.traceInterchange.integral_norm_summable.of_norm_bounded
      (fun index ↦ norm_integral_le_integral_norm _)
  simpa [integratedCoefficient, traceSummand,
    MeasureTheory.integral_mul_const] using hIntegralSummable

/-- Rank-one expansion of the Bochner integral, constructed from the
integrated coefficients. -/
def integratedExpansion
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    SummableRankOneOperatorExpansion.{v}
      (∫ time in timeRegion, integrand time) where
  Index := data.Index
  coefficient := data.integratedCoefficient
  leftVector := data.leftVector
  rightVector := data.rightVector
  summable_nuclearNorm := data.integrated_nuclearNorm_summable
  trace_summable := data.integrated_trace_summable
  operator_eq_tsum := data.operatorIntegral_eq_integratedSeries

/-- Presentation independence for the integrated series is now a theorem,
derived from the single reusable ambient uniqueness certificate. -/
theorem integrated_presentation_independent
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass)
    (other : SummableRankOneOperatorExpansion.{v}
      (∫ time in timeRegion, integrand time)) :
    other.expansionTrace =
      ∑' index,
        (∫ time in timeRegion, data.coefficient index time) *
          inner Real (data.leftVector index) (data.rightVector index) := by
  simpa [integratedExpansion,
    SummableRankOneOperatorExpansion.expansionTrace,
    integratedCoefficient] using
      data.traceUniqueness.expansionTrace_eq other data.integratedExpansion

/-- Intrinsic nuclearity of the Bochner integral is constructed from the
integrated expansion and the reusable ambient trace-uniqueness theorem. -/
def integratedTraceClass
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    IntrinsicNuclearTraceData.{u, v}
      (∫ time in timeRegion, integrand time) :=
  data.traceUniqueness.intrinsicTraceData data.integratedExpansion

/-- The scalar trace series may be integrated term by term. -/
theorem integral_pointwiseTrace_eq_intrinsicTrace
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    (∫ time in timeRegion,
      intrinsicNuclearTrace (pointwiseTraceClass time)) =
        intrinsicNuclearTrace data.integratedTraceClass := by
  letI : Countable data.Index := data.index_countable
  calc
    (∫ time in timeRegion,
        intrinsicNuclearTrace (pointwiseTraceClass time)) =
      ∫ time in timeRegion,
        ∑' index, data.traceSummand index time := by
      apply integral_congr_ae
      filter_upwards [] with time
      exact data.pointwiseTrace_eq_tsum time
    _ = ∑' index,
        ∫ time in timeRegion, data.traceSummand index time :=
      data.traceInterchange.integral_tsum_eq_tsum_integral
    _ = ∑' index,
        data.integratedCoefficient index *
          inner Real (data.leftVector index) (data.rightVector index) := by
      apply tsum_congr
      intro index
      change
        (∫ time in timeRegion,
          data.coefficient index time *
            inner Real (data.leftVector index) (data.rightVector index)) = _
      rw [MeasureTheory.integral_mul_const]
      rfl
    _ = data.integratedExpansion.expansionTrace := rfl
    _ = intrinsicNuclearTrace data.integratedTraceClass :=
      data.integratedTraceClass.expansionTrace_eq data.integratedExpansion

/-- Construction of the exact bridge required by the renormalized short-time
Bochner packet. -/
def toIntrinsicNuclearTraceBochnerBridge
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    IntrinsicNuclearTraceBochnerBridgeData.{u, v}
      timeRegion integrand pointwiseTraceClass where
  integralTraceClass := data.integratedTraceClass
  trace_integral_commutes := data.integral_pointwiseTrace_eq_intrinsicTrace.symm

/-- Public countable rank-one bridge checkpoint. -/
theorem countable_rank_one_nuclear_trace_bochner_bridge_gate
    {timeRegion : Set Real} {integrand : Real → E →L[Real] E}
    {pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)}
    (data : CountableRankOneNuclearTraceBochnerBridgeData
      timeRegion integrand pointwiseTraceClass) :
    ((∫ time in timeRegion, integrand time) =
      ∑' index,
        data.integratedCoefficient index •
          InnerProductSpace.rankOne Real
            (data.leftVector index) (data.rightVector index)) ∧
    ((∫ time in timeRegion,
      intrinsicNuclearTrace (pointwiseTraceClass time)) =
        intrinsicNuclearTrace
          data.toIntrinsicNuclearTraceBochnerBridge.integralTraceClass) :=
  ⟨data.operatorIntegral_eq_integratedSeries,
    data.integral_pointwiseTrace_eq_intrinsicTrace⟩

end CountableRankOneNuclearTraceBochnerBridgeData

end
end P0EFTJanusProgramPCountableRankOneNuclearTraceBochnerBridge4D
end JanusFormal
