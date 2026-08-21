import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D

/-!
# Generated product-throat Bochner operator integrability

Termwise local uniform convergence generates continuity of the countable
rank-one operator series.  An integrable scalar bound on the sum of the
summand norms then generates Bochner integrability of the full series.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPCountableRankOneNuclearTraceBochnerBridge4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Rank-one long-time data in which Bochner integrability of the complete
operator series is generated rather than assumed. -/
structure ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (start : Real) where
  weighted : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear start
  operatorIntegrand : Real → Real → E →L[Real] E
  pointwiseTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{u, v} (operatorIntegrand parameter time)
  pointwiseTrace_eq_extendedDuhamelTrace : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      intrinsicNuclearTrace (pointwiseTraceClass parameter time) =
        extendedDuhamelTrace nuclear parameter time
  rankOne : ∀ parameter,
    CountableRankOneNuclearTraceBochnerBridgeData.{u, v}
      (Set.Ioi start) (operatorIntegrand parameter)
        (pointwiseTraceClass parameter)
  uniformMajorant : ∀ parameter, (rankOne parameter).Index → Real
  uniformMajorant_summable : ∀ parameter,
    Summable (uniformMajorant parameter)
  summand_continuousOn : ∀ parameter index,
    ContinuousOn ((rankOne parameter).operatorSummand index)
      (Set.Ici start)
  summand_norm_le_uniform : ∀ parameter index time,
    time ∈ Set.Ici start →
      ‖(rankOne parameter).operatorSummand index time‖ ≤
        uniformMajorant parameter index
  integrableMajorant : Real → Real → Real
  integrableMajorant_integrable : ∀ parameter,
    Integrable (integrableMajorant parameter)
      (volume.restrict (Set.Ioi start))
  nuclearNorm_tsum_le_integrableMajorant : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      (∑' index,
        |(rankOne parameter).coefficient index time| *
          ‖(rankOne parameter).leftVector index‖ *
          ‖(rankOne parameter).rightVector index‖) ≤
        integrableMajorant parameter time

namespace ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData

/-- Nuclear norm summability controls the operator norms of all rank-one
summands at each time. -/
theorem operatorSummand_norm_summable
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start)
    (parameter time : Real) :
    Summable (fun index ↦
      ‖(data.rankOne parameter).operatorSummand index time‖) := by
  simpa [CountableRankOneNuclearTraceBochnerBridgeData.operatorSummand,
    norm_smul, InnerProductSpace.norm_rankOne, Real.norm_eq_abs,
    mul_assoc] using
      (data.rankOne parameter).pointwise_nuclearNorm_summable time

/-- For rank-one summands, the sum of operator norms is exactly the nuclear
coefficient sum appearing in the spectral expansion. -/
theorem operatorSummand_norm_tsum_eq_nuclearNorm
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start)
    (parameter time : Real) :
    (∑' index, ‖(data.rankOne parameter).operatorSummand index time‖) =
      ∑' index,
        |(data.rankOne parameter).coefficient index time| *
          ‖(data.rankOne parameter).leftVector index‖ *
          ‖(data.rankOne parameter).rightVector index‖ := by
  apply tsum_congr
  intro index
  simp [CountableRankOneNuclearTraceBochnerBridgeData.operatorSummand,
    norm_smul, InnerProductSpace.norm_rankOne, Real.norm_eq_abs,
    mul_assoc]

/-- Local uniform convergence gives continuity of the complete operator
series on the closed long-time half-line. -/
theorem operatorIntegrand_continuousOn
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start)
    (parameter : Real) :
    ContinuousOn (data.operatorIntegrand parameter) (Set.Ici start) :=
  countableRankOne_integrand_continuousOn_of_uniform
    (data.rankOne parameter) (data.uniformMajorant parameter)
    (data.uniformMajorant_summable parameter)
    (data.summand_continuousOn parameter)
    (data.summand_norm_le_uniform parameter)

/-- The scalar bound on the sum of rank-one norms generates Bochner
integrability of the complete operator series. -/
theorem operatorIntegrable
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start)
    (parameter : Real) :
    Integrable (data.operatorIntegrand parameter)
      (volume.restrict (Set.Ioi start)) := by
  apply (data.integrableMajorant_integrable parameter).mono'
  · exact ((data.operatorIntegrand_continuousOn parameter).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards
      [data.nuclearNorm_tsum_le_integrableMajorant parameter] with time htime
    rw [(data.rankOne parameter).integrand_eq_tsum time]
    exact (norm_tsum_le_tsum_norm
      (data.operatorSummand_norm_summable parameter time)).trans
        ((data.operatorSummand_norm_tsum_eq_nuclearNorm parameter time).le.trans
          htime)

/-- Adapter to the existing countable product-throat Bochner packet. -/
def toCountableRankOneBochnerOperatorIntegral
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start) :
    ProductThroatNuclearDuhamelCountableRankOneBochnerOperatorIntegralData
      productData fold twist nuclear start where
  weighted := data.weighted
  operatorIntegrand := data.operatorIntegrand
  operatorIntegrable := data.operatorIntegrable
  pointwiseTraceClass := data.pointwiseTraceClass
  pointwiseTrace_eq_extendedDuhamelTrace :=
    data.pointwiseTrace_eq_extendedDuhamelTrace
  rankOne := data.rankOne

/-- Public checkpoint: full operator continuity and Bochner integrability are
both generated by the rank-one bounds. -/
theorem product_throat_locally_uniform_bochner_operator_gate
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear start) :
    (∀ parameter, ContinuousOn (data.operatorIntegrand parameter)
      (Set.Ici start)) ∧
    (∀ parameter, Integrable (data.operatorIntegrand parameter)
      (volume.restrict (Set.Ioi start))) :=
  ⟨data.operatorIntegrand_continuousOn, data.operatorIntegrable⟩

end ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData

/-- Complete terminal-boundary input whose long operator integrability is
generated by the locally uniform rank-one packet. -/
structure ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1) where
  shortFrontend :
    RenormalizedNuclearDuhamelCountableRankOneBochnerFrontendData
      nuclear shortTime
  longTime :
    ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      productData fold twist nuclear 1
  finitePartOperator : Real → E →L[Real] E
  finitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (finitePartOperator parameter)
  finitePartDerivative_eq_trace : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      intrinsicNuclearTrace (finitePartTraceClass parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    (shortFrontend.toRenormalizedOperatorIntegral.integratedOperator parameter -
        finitePartOperator parameter) +
      (longTime.toCountableRankOneBochnerOperatorIntegral
        |>.toCountableRankOneBochnerOperatorIntegral).integratedOperator
          parameter =
      logarithmicDerivativeOperator parameter

namespace ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData

/-- Adapter to the established locally uniform complete boundary. -/
def toLocallyUniformFullyCountableTerminalBoundary
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData
      Index productData fold twist nuclear finiteCounterterm shortTime) :
    ProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundaryData
      Index productData fold twist nuclear finiteCounterterm shortTime where
  shortFrontend := data.shortFrontend
  longTime := data.longTime.toCountableRankOneBochnerOperatorIntegral
  longMajorant := data.longTime.uniformMajorant
  longMajorant_summable := data.longTime.uniformMajorant_summable
  longSummand_continuousOn := data.longTime.summand_continuousOn
  longSummand_norm_le := data.longTime.summand_norm_le_uniform
  finitePartOperator := data.finitePartOperator
  finitePartTraceClass := data.finitePartTraceClass
  finitePartDerivative_eq_trace := data.finitePartDerivative_eq_trace
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity

/-- Public checkpoint: the generated boundary provides the complete terminal
integral identity without assuming Bochner integrability of the full series. -/
theorem product_throat_generated_bochner_terminal_boundary_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData
      Index productData fold twist nuclear finiteCounterterm shortTime) :
    (∀ parameter, Integrable (data.longTime.operatorIntegrand parameter)
      (volume.restrict (Set.Ioi (1 : Real)))) ∧
    (∀ parameter,
      IntegrableOn
        (data.toLocallyUniformFullyCountableTerminalBoundary
          |>.toFullyCountableTerminalBoundary
          |>.toFullyCountableTerminalBoundaryFrontend.terminalTail parameter
          |>.integrand)
        (Set.Ioi (1 : Real))) := by
  exact ⟨data.longTime.operatorIntegrable,
    fun parameter ↦
      data.toLocallyUniformFullyCountableTerminalBoundary
        |>.toFullyCountableTerminalBoundary
        |>.toFullyCountableTerminalBoundaryFrontend.terminalTail parameter
        |>.integrableOn_tail⟩

end ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData

end
end P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D
end JanusFormal
