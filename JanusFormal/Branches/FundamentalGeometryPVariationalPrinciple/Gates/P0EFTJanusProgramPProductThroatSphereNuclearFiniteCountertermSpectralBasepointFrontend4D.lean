import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D

/-!
# Spherical basepoint to ProductThroat spectral frontend

The already proved spherical remainder supplies basepoint integrability and
the quadratic derivative bound.  Exact counterterm compatibility transports
those results to the finite counterterm packet used by the generated atlas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearFiniteCountertermSpectralBasepointFrontend4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The three explicit reduced-sphere counterterm profiles are continuous on
the positive short-time interval. -/
theorem reducedSphereFiniteCounterterm_basis_continuousOn
    (sphereData : ProductThroatSpectralData) :
    ∀ index,
      ContinuousOn
        ((reducedSphereFiniteCountertermVariation sphereData).variation.basis
          index)
        (Set.Ioo (0 : Real) 1) := by
  intro index
  cases index with
  | inverse =>
      exact continuousOn_const.div continuousOn_id
        (fun time hTime => ne_of_gt hTime.1)
  | constant => exact continuousOn_const
  | linear => exact continuousOn_id

/-- Exact derivative compatibility follows from equality of the two
counterterm families and uniqueness of the derivative. -/
theorem countertermDerivative_eq_of_counterterm_eq
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : ProductThroatSphereNuclearShortTimeBasepointQuadraticData
      sphereData nuclear)
    (counterterm_eq : ∀ parameter time,
      shortTime.counterterm parameter time =
        counterterm finiteCounterterm.variation parameter time)
    (parameter time : Real) :
    shortTime.countertermDerivative parameter time =
      countertermDerivative finiteCounterterm.variation parameter time := by
  have hShort := shortTime.counterterm_hasDerivAt parameter time
  have hFunction :
      (fun current => shortTime.counterterm current time) =
        fun current => counterterm finiteCounterterm.variation current time :=
    funext fun current => counterterm_eq current time
  rw [hFunction] at hShort
  exact hShort.unique
    (counterterm_hasDerivAt finiteCounterterm.variation parameter time)

/-- Build the strongest generic short/long ProductThroat frontend from the
existing spherical basepoint packet. -/
def productThroatFiniteCountertermSpectralBasepointFrontendOfSphere
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (basis_continuousOn : ∀ index,
      ContinuousOn (finiteCounterterm.variation.basis index)
        (Set.Ioo (0 : Real) 1))
    (realHeatTraceIdentification :
      ReferenceProductThroatRealHeatTraceIdentificationData sphereData fold
        twist nuclear)
    (shortTime : ProductThroatSphereNuclearShortTimeBasepointQuadraticData
      sphereData nuclear)
    (shortTime_counterterm_eq : ∀ parameter time,
      shortTime.counterterm parameter time =
        counterterm finiteCounterterm.variation parameter time)
    (longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      sphereData fold twist nuclear 1) :
    ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
      Index sphereData fold twist nuclear where
  finiteCounterterm := finiteCounterterm
  basis_continuousOn := basis_continuousOn
  realHeatTraceIdentification := realHeatTraceIdentification
  basepoint := shortTime.basepoint
  basepoint_integrable := by
    exact shortTime.basepoint_integrable.congr
      (ae_of_all _ fun time => by
        change time⁻¹ *
            (extendedHeatTrace nuclear shortTime.basepoint time -
              shortTime.counterterm shortTime.basepoint time) =
          time⁻¹ *
            (extendedHeatTrace nuclear shortTime.basepoint time -
              counterterm finiteCounterterm.variation shortTime.basepoint time)
        rw [shortTime_counterterm_eq shortTime.basepoint time])
  scale := shortTime.scale
  derivative_norm_le := by
    filter_upwards [shortTime.derivative_norm_le] with time hBound
    intro parameter
    rw [← countertermDerivative_eq_of_counterterm_eq finiteCounterterm shortTime
      shortTime_counterterm_eq parameter time]
    exact hBound parameter
  longTime := longTime

/-- Specialization to the canonical three-profile reduced-sphere
counterterm. -/
def productThroatReducedSphereSpectralBasepointFrontend
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (realHeatTraceIdentification :
      ReferenceProductThroatRealHeatTraceIdentificationData sphereData fold
        twist nuclear)
    (shortTime : ProductThroatSphereNuclearShortTimeBasepointQuadraticData
      sphereData nuclear)
    (shortTime_counterterm_eq : ∀ parameter time,
      shortTime.counterterm parameter time =
        counterterm (reducedSphereFiniteCountertermVariation sphereData).variation
          parameter time)
    (longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      sphereData fold twist nuclear 1) :
    ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
      ReducedSphereCountertermProfile sphereData fold twist nuclear :=
  productThroatFiniteCountertermSpectralBasepointFrontendOfSphere
    (reducedSphereFiniteCountertermVariation sphereData)
    (reducedSphereFiniteCounterterm_basis_continuousOn sphereData)
    realHeatTraceIdentification shortTime shortTime_counterterm_eq longTime

/-- Public spherical-to-generated-frontend checkpoint. -/
theorem product_throat_sphere_nuclear_finite_counterterm_spectral_basepoint_gate
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (basis_continuousOn : ∀ index,
      ContinuousOn (finiteCounterterm.variation.basis index)
        (Set.Ioo (0 : Real) 1))
    (realHeatTraceIdentification :
      ReferenceProductThroatRealHeatTraceIdentificationData sphereData fold
        twist nuclear)
    (shortTime : ProductThroatSphereNuclearShortTimeBasepointQuadraticData
      sphereData nuclear)
    (shortTime_counterterm_eq : ∀ parameter time,
      shortTime.counterterm parameter time =
        counterterm finiteCounterterm.variation parameter time)
    (longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      sphereData fold twist nuclear 1) :
    let frontend :=
      productThroatFiniteCountertermSpectralBasepointFrontendOfSphere
        finiteCounterterm basis_continuousOn realHeatTraceIdentification
          shortTime shortTime_counterterm_eq longTime
    Integrable
      (fun time => time⁻¹ *
        (extendedHeatTrace nuclear frontend.basepoint time -
          counterterm frontend.finiteCounterterm.variation
            frontend.basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1)) ∧
    (∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative frontend.finiteCounterterm.variation
            parameter time)‖ ≤
        shortTimeQuadraticBound frontend.scale time) := by
  dsimp only
  exact
    ⟨(productThroatFiniteCountertermSpectralBasepointFrontendOfSphere
        finiteCounterterm basis_continuousOn realHeatTraceIdentification
          shortTime shortTime_counterterm_eq longTime).basepoint_integrable,
      (productThroatFiniteCountertermSpectralBasepointFrontendOfSphere
        finiteCounterterm basis_continuousOn realHeatTraceIdentification
          shortTime shortTime_counterterm_eq longTime).derivative_norm_le⟩

end
end P0EFTJanusProgramPProductThroatSphereNuclearFiniteCountertermSpectralBasepointFrontend4D
end JanusFormal
