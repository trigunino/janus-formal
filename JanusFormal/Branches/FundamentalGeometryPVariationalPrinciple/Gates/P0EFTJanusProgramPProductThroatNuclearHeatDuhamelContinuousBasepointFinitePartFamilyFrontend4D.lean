import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

/-!
# Continuous short-time basepoint ProductThroat frontend

Time continuity generates strong measurability, while one integrable majorant
generates basepoint integrability.  Mean-value propagation then constructs the
complete short-time family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Short-time input stated with time continuity and one explicit basepoint
majorant. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeContinuousBasepointData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), weight time * time = 1
  counterterm : Real → Real → Real
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  weightedRemainder_continuousOn : ∀ parameter,
    ContinuousOn
      (fun time => weight time *
        (extendedHeatTrace nuclear parameter time - counterterm parameter time))
      (Set.Ioo 0 cutoff)
  basepoint : Real
  basepointMajorant : Real → Real
  basepointMajorant_integrable :
    Integrable basepointMajorant (volume.restrict (Set.Ioo 0 cutoff))
  basepoint_norm_le : ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
    ‖weight time *
      (extendedHeatTrace nuclear basepoint time - counterterm basepoint time)‖ ≤
      basepointMajorant time
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), ∀ parameter,
      ‖weight time *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeContinuousBasepointData

/-- Convert continuity and domination into the existing basepoint packet. -/
def toBasepointQuadratic
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeContinuousBasepointData
      nuclear cutoff) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
      nuclear cutoff where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  counterterm := data.counterterm
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  integrand_aeStronglyMeasurable := fun parameter =>
    (data.weightedRemainder_continuousOn parameter).aestronglyMeasurable
      measurableSet_Ioo
  basepoint := data.basepoint
  basepoint_integrable := by
    apply data.basepointMajorant_integrable.mono'
    · exact (data.weightedRemainder_continuousOn data.basepoint).aestronglyMeasurable
        measurableSet_Ioo
    · exact data.basepoint_norm_le
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le

end NuclearHeatDuhamelCountertermSubtractedShortTimeContinuousBasepointData

/-- Factorized continuity input: continuity is supplied separately for the
weight, heat trace and counterterm, rather than for their combined remainder. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), weight time * time = 1
  weight_continuousOn : ContinuousOn weight (Set.Ioo 0 cutoff)
  heatTrace_continuousOn : ∀ parameter,
    ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
      (Set.Ioo 0 cutoff)
  counterterm : Real → Real → Real
  counterterm_continuousOn : ∀ parameter,
    ContinuousOn (fun time => counterterm parameter time) (Set.Ioo 0 cutoff)
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  basepoint : Real
  basepointMajorant : Real → Real
  basepointMajorant_integrable :
    Integrable basepointMajorant (volume.restrict (Set.Ioo 0 cutoff))
  basepoint_norm_le : ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
    ‖weight time *
      (extendedHeatTrace nuclear basepoint time - counterterm basepoint time)‖ ≤
      basepointMajorant time
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), ∀ parameter,
      ‖weight time *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData

/-- Assemble continuity of the weighted subtracted remainder from its three
elementary continuous factors. -/
def toContinuousBasepoint
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData
        nuclear cutoff) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeContinuousBasepointData
      nuclear cutoff where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  counterterm := data.counterterm
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  weightedRemainder_continuousOn := fun parameter =>
    data.weight_continuousOn.mul
      ((data.heatTrace_continuousOn parameter).sub
        (data.counterterm_continuousOn parameter))
  basepoint := data.basepoint
  basepointMajorant := data.basepointMajorant
  basepointMajorant_integrable := data.basepointMajorant_integrable
  basepoint_norm_le := data.basepoint_norm_le
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le

end NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData

/-- Short-time input with the canonical Mellin weight `time⁻¹`. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeCanonicalWeightContinuousBasepointData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  heatTrace_continuousOn : ∀ parameter,
    ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
      (Set.Ioo 0 cutoff)
  counterterm : Real → Real → Real
  counterterm_continuousOn : ∀ parameter,
    ContinuousOn (fun time => counterterm parameter time) (Set.Ioo 0 cutoff)
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  basepoint : Real
  basepointMajorant : Real → Real
  basepointMajorant_integrable :
    Integrable basepointMajorant (volume.restrict (Set.Ioo 0 cutoff))
  basepoint_norm_le : ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
    ‖time⁻¹ *
      (extendedHeatTrace nuclear basepoint time - counterterm basepoint time)‖ ≤
      basepointMajorant time
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeCanonicalWeightContinuousBasepointData

/-- Generate the factorized packet using the canonical Mellin weight. -/
def toFactorizedContinuousBasepoint
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeCanonicalWeightContinuousBasepointData
        nuclear cutoff) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData
      nuclear cutoff where
  weight := fun time => time⁻¹
  weight_mul_time_eq_one := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    exact inv_mul_cancel₀ (ne_of_gt hTime.1)
  weight_continuousOn :=
    continuousOn_id.inv₀ fun time hTime => ne_of_gt hTime.1
  heatTrace_continuousOn := data.heatTrace_continuousOn
  counterterm := data.counterterm
  counterterm_continuousOn := data.counterterm_continuousOn
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  basepoint := data.basepoint
  basepointMajorant := data.basepointMajorant
  basepointMajorant_integrable := data.basepointMajorant_integrable
  basepoint_norm_le := data.basepoint_norm_le
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le

end NuclearHeatDuhamelCountertermSubtractedShortTimeCanonicalWeightContinuousBasepointData

/-- Canonical-weight short-time data after removing the heat-trace continuity
field generated by a product spectral identification. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeSpectralCanonicalWeightBasepointData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  counterterm : Real → Real → Real
  counterterm_continuousOn : ∀ parameter,
    ContinuousOn (fun time => counterterm parameter time) (Set.Ioo 0 cutoff)
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  basepoint : Real
  basepointMajorant : Real → Real
  basepointMajorant_integrable :
    Integrable basepointMajorant (volume.restrict (Set.Ioo 0 cutoff))
  basepoint_norm_le : ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
    ‖time⁻¹ *
      (extendedHeatTrace nuclear basepoint time - counterterm basepoint time)‖ ≤
      basepointMajorant time
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeSpectralCanonicalWeightBasepointData

/-- Generate heat-trace continuity from the product spectral trace. -/
def toCanonicalWeightContinuousBasepoint
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeSpectralCanonicalWeightBasepointData
        nuclear cutoff)
    (identification : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeCanonicalWeightContinuousBasepointData
      nuclear cutoff where
  heatTrace_continuousOn := fun parameter =>
    identification.extendedHeatTrace_continuousOn_Ioo parameter cutoff
  counterterm := data.counterterm
  counterterm_continuousOn := data.counterterm_continuousOn
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  basepoint := data.basepoint
  basepointMajorant := data.basepointMajorant
  basepointMajorant_integrable := data.basepointMajorant_integrable
  basepoint_norm_le := data.basepoint_norm_le
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le

end NuclearHeatDuhamelCountertermSubtractedShortTimeSpectralCanonicalWeightBasepointData

/-- Product-throat finite-part input using the continuous basepoint packet. -/
structure ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeFactorizedContinuousBasepointData
    nuclear 1
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData

/-- Adapter to the generated basepoint finite-part frontend. -/
def toBasepointFinitePartFamilyFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData
        Index productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData
      Index productData fold twist nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTimeBasepoint := data.shortTime.toContinuousBasepoint.toBasepointQuadratic
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  longTime := data.longTime

/-- Public continuity-to-finite-part checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_continuous_basepoint_finite_part_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData
        Index productData fold twist nuclear) :
    (∀ parameter,
      AEStronglyMeasurable
        (fun time => data.shortTime.weight time *
          (extendedHeatTrace nuclear parameter time -
            data.shortTime.counterterm parameter time))
        (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    Integrable
      (fun time => data.shortTime.weight time *
        (extendedHeatTrace nuclear data.shortTime.basepoint time -
          data.shortTime.counterterm data.shortTime.basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1)) := by
  exact ⟨fun parameter =>
      data.toBasepointFinitePartFamilyFrontend.shortTimeBasepoint.integrand_aeStronglyMeasurable
        parameter,
    data.toBasepointFinitePartFamilyFrontend.shortTimeBasepoint.basepoint_integrable⟩

end ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData

/-- Product-throat frontend with the canonical short-time Mellin weight. -/
structure ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  realHeatTraceIdentification :
    ReferenceProductThroatRealHeatTraceIdentificationData productData fold
      twist nuclear
  shortTime :
    NuclearHeatDuhamelCountertermSubtractedShortTimeSpectralCanonicalWeightBasepointData
      nuclear 1
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData

/-- Forget only the canonical presentation of the short-time weight. -/
def toContinuousBasepointFinitePartFamilyFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData
        Index productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontendData
      Index productData fold twist nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTime :=
    (data.shortTime.toCanonicalWeightContinuousBasepoint
      data.realHeatTraceIdentification).toFactorizedContinuousBasepoint
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  longTime := data.longTime

/-- Public canonical-weight finite-part checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_canonical_weight_continuous_basepoint_finite_part_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData
        Index productData fold twist nuclear) :
    (∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1), time⁻¹ * time = 1) ∧
    (∀ parameter,
      Integrable
        (data.toContinuousBasepointFinitePartFamilyFrontend
          |>.toBasepointFinitePartFamilyFrontend
          |>.shortTimeBasepoint.weightedRemainder parameter)
        (volume.restrict (Set.Ioo (0 : Real) 1))) := by
  exact
    ⟨(data.shortTime.toCanonicalWeightContinuousBasepoint
        data.realHeatTraceIdentification).toFactorizedContinuousBasepoint.weight_mul_time_eq_one,
      data.toContinuousBasepointFinitePartFamilyFrontend
        |>.toBasepointFinitePartFamilyFrontend
        |>.toFinitePartFamilyFrontend.shortTime.integrand_integrable⟩

end ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData

/-- Strong ProductThroat frontend in which the finite counterterm itself
generates its time continuity and parameter derivative. -/
structure ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  basis_continuousOn : ∀ index,
    ContinuousOn (finiteCounterterm.variation.basis index)
      (Set.Ioo (0 : Real) 1)
  realHeatTraceIdentification :
    ReferenceProductThroatRealHeatTraceIdentificationData productData fold
      twist nuclear
  basepoint : Real
  basepoint_integrable :
    Integrable (fun time => time⁻¹ *
      (extendedHeatTrace nuclear basepoint time -
        counterterm finiteCounterterm.variation basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1))
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative finiteCounterterm.variation parameter time)‖ ≤
        shortTimeQuadraticBound scale time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData

/-- A finite counterterm is continuous in time when each fixed basis profile
is continuous. -/
theorem counterterm_continuousOn
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
        Index productData fold twist nuclear)
    (parameter : Real) :
    ContinuousOn
      (fun time => counterterm data.finiteCounterterm.variation parameter time)
      (Set.Ioo (0 : Real) 1) := by
  unfold counterterm
  apply continuousOn_finsetSum data.finiteCounterterm.variation.support
  intro index _
  exact continuousOn_const.mul (data.basis_continuousOn index)

/-- Generate the preceding canonical-weight frontend without duplicating the
finite counterterm or its derivative. -/
def toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
        Index productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelCanonicalWeightContinuousBasepointFinitePartFamilyFrontendData
      Index productData fold twist nuclear where
  finiteCounterterm := data.finiteCounterterm
  realHeatTraceIdentification := data.realHeatTraceIdentification
  shortTime := {
    counterterm := counterterm data.finiteCounterterm.variation
    counterterm_continuousOn := data.counterterm_continuousOn
    countertermDerivative := countertermDerivative data.finiteCounterterm.variation
    counterterm_hasDerivAt :=
      counterterm_hasDerivAt data.finiteCounterterm.variation
    basepoint := data.basepoint
    basepointMajorant := fun time =>
      ‖time⁻¹ *
        (extendedHeatTrace nuclear data.basepoint time -
          counterterm data.finiteCounterterm.variation data.basepoint time)‖
    basepointMajorant_integrable := data.basepoint_integrable.norm
    basepoint_norm_le := ae_of_all _ fun _ => le_rfl
    scale := data.scale
    derivative_norm_le := data.derivative_norm_le }
  shortTime_counterterm_eq := fun _ _ => rfl
  longTime := data.longTime

/-- Public finite-counterterm-generated short-time checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_finite_counterterm_spectral_basepoint_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
        Index productData fold twist nuclear) :
    (∀ parameter,
      ContinuousOn
        (fun time => counterterm data.finiteCounterterm.variation parameter time)
        (Set.Ioo (0 : Real) 1)) ∧
    (∀ parameter time,
      HasDerivAt
        (fun current =>
          counterterm data.finiteCounterterm.variation current time)
        (countertermDerivative data.finiteCounterterm.variation parameter time)
        parameter) :=
  ⟨data.counterterm_continuousOn,
    counterterm_hasDerivAt data.finiteCounterterm.variation⟩

end ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
end JanusFormal
