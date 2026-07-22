import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D

/-!
# Component energy of the first-jet `H¹` graph

The `H¹` graph completion is the closure of the `L²` first jet

`u ↦ (u, (X_i u)_i)`.

This file exposes the derivative projection and decomposes every smooth first
jet as the sum of its value and derivative injections.  The triangle inequality
then gives a universal squared bound for the graph norm in terms of the two
component `L²` norms.

Consequently the elementary `H¹ ≤ L² + derivative energy` part of Gårding does
not need to be supplied as a PDE hypothesis.  Only the estimate of that explicit
component energy by the Euler quadratic form remains analytic.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphComponentEnergy4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D

universe u

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Derivative projection from the completed first-jet graph. -/
def h1GraphToDerivativeL2
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    H1GraphSpace period hPeriod Fiber frame mu →L[Real]
      Lp (Fin frame.count → Fiber) (2 : ENNReal) mu :=
  ((ContinuousLinearMap.snd Real Fiber (Fin frame.count → Fiber)).compLpL
      (2 : ENNReal) mu).comp
    (h1GraphSubmodule period hPeriod Fiber frame mu).subtypeL

/-- Smooth derivative component as an `L²` vector. -/
def smoothFrameDerivativeToL2
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    Lp (Fin frame.count → Fiber) (2 : ENNReal) mu :=
  h1GraphToDerivativeL2 period hPeriod Fiber frame mu
    (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field)

/-- Almost-everywhere representative of the smooth derivative component. -/
theorem smoothFrameDerivativeToL2_ae
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    (smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field :
      EffectiveQuotient period hPeriod → Fin frame.count → Fiber) =ᵐ[mu]
      frameDerivative period hPeriod Fiber frame field := by
  have hProjection :=
    (ContinuousLinearMap.snd Real Fiber
      (Fin frame.count → Fiber)).coeFn_compLpL
      (p := (2 : ENNReal)) (μ := mu)
      (smoothFirstJetToL2 period hPeriod Fiber frame mu field)
  have hJet :
      (smoothFirstJetToL2 period hPeriod Fiber frame mu field :
        EffectiveQuotient period hPeriod →
          Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame field := by
    simpa only [smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Fiber frame mu field).coeFn_toLp
  filter_upwards [hProjection, hJet]
    with point hProjection hJet
  change
    (smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field :
      EffectiveQuotient period hPeriod → Fin frame.count → Fiber) point = _
  simpa [smoothFrameDerivativeToL2, h1GraphToDerivativeL2,
    smoothToH1GraphLinearMap, smoothFirstJetL2LinearMap,
    smoothFirstJet, hJet] using hProjection

/-- `L²` value injection into first-jet `L²`. -/
def valueJetInjection
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    Lp Fiber (2 : ENNReal) mu →L[Real]
      Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu :=
  (ContinuousLinearMap.inl Real Fiber (Fin frame.count → Fiber)).compLpL
    (2 : ENNReal) mu

/-- `L²` derivative injection into first-jet `L²`. -/
def derivativeJetInjection
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    Lp (Fin frame.count → Fiber) (2 : ENNReal) mu →L[Real]
      Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu :=
  (ContinuousLinearMap.inr Real Fiber (Fin frame.count → Fiber)).compLpL
    (2 : ENNReal) mu

/-- Exact decomposition of the smooth first jet into its two injected
components. -/
theorem smoothFirstJetToL2_eq_component_sum
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothFirstJetToL2 period hPeriod Fiber frame mu field =
      valueJetInjection period hPeriod Fiber frame mu
          (smoothFieldToL2 period hPeriod Fiber mu field) +
        derivativeJetInjection period hPeriod Fiber frame mu
          (smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field) := by
  apply Lp.ext
  filter_upwards
    [(smoothFirstJet_memLp period hPeriod Fiber frame mu field).coeFn_toLp,
     smoothFieldToL2_ae period hPeriod Fiber mu field,
     smoothFrameDerivativeToL2_ae period hPeriod Fiber frame mu field,
     (ContinuousLinearMap.inl Real Fiber
        (Fin frame.count → Fiber)).coeFn_compLpL
        (p := (2 : ENNReal)) (μ := mu)
        (smoothFieldToL2 period hPeriod Fiber mu field),
     (ContinuousLinearMap.inr Real Fiber
        (Fin frame.count → Fiber)).coeFn_compLpL
        (p := (2 : ENNReal)) (μ := mu)
        (smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field),
     Lp.coeFn_add
       (valueJetInjection period hPeriod Fiber frame mu
        (smoothFieldToL2 period hPeriod Fiber mu field))
       (derivativeJetInjection period hPeriod Fiber frame mu
        (smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field))]
    with point hJet hValue hDerivative hInl hInr hAdd
  rw [hJet, hAdd, hInl, hInr, hValue, hDerivative]
  rfl

/-- Operator-norm weighted value coefficient. -/
def valueJetWeight
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] : Real :=
  ‖valueJetInjection period hPeriod Fiber frame mu‖

/-- Operator-norm weighted derivative coefficient. -/
def derivativeJetWeight
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] : Real :=
  ‖derivativeJetInjection period hPeriod Fiber frame mu‖

/-- Universal first-jet norm estimate. -/
theorem smoothToH1Graph_norm_le_components
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    ‖smoothToH1GraphLinearMap period hPeriod Fiber frame mu field‖ ≤
      valueJetWeight period hPeriod Fiber frame mu *
          ‖smoothFieldToL2 period hPeriod Fiber mu field‖ +
        derivativeJetWeight period hPeriod Fiber frame mu *
          ‖smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field‖ := by
  change ‖smoothFirstJetToL2 period hPeriod Fiber frame mu field‖ ≤ _
  rw [smoothFirstJetToL2_eq_component_sum]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((valueJetInjection period hPeriod Fiber frame mu).le_opNorm _)
      ((derivativeJetInjection period hPeriod Fiber frame mu).le_opNorm _))

/-- Explicit component energy dominating the squared first-jet graph norm. -/
def smoothFirstJetComponentEnergy
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) : Real :=
  2 * valueJetWeight period hPeriod Fiber frame mu ^ 2 *
      ‖smoothFieldToL2 period hPeriod Fiber mu field‖ ^ 2 +
    2 * derivativeJetWeight period hPeriod Fiber frame mu ^ 2 *
      ‖smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field‖ ^ 2

/-- Nonnegativity of the explicit component energy. -/
theorem smoothFirstJetComponentEnergy_nonnegative
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    0 ≤ smoothFirstJetComponentEnergy
      period hPeriod Fiber frame mu field := by
  unfold smoothFirstJetComponentEnergy
  positivity

/-- The explicit component energy dominates the squared `H¹` graph norm. -/
theorem smoothToH1Graph_norm_sq_le_componentEnergy
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    ‖smoothToH1GraphLinearMap period hPeriod Fiber frame mu field‖ ^ 2 ≤
      smoothFirstJetComponentEnergy period hPeriod Fiber frame mu field := by
  have hNorm := smoothToH1Graph_norm_le_components
    period hPeriod Fiber frame mu field
  have hLeft := norm_nonneg
    (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field)
  have hValue : 0 ≤ valueJetWeight period hPeriod Fiber frame mu *
      ‖smoothFieldToL2 period hPeriod Fiber mu field‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hDerivative : 0 ≤ derivativeJetWeight period hPeriod Fiber frame mu *
      ‖smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  unfold smoothFirstJetComponentEnergy
  nlinarith [sq_nonneg
    (valueJetWeight period hPeriod Fiber frame mu *
      ‖smoothFieldToL2 period hPeriod Fiber mu field‖ -
     derivativeJetWeight period hPeriod Fiber frame mu *
      ‖smoothFrameDerivativeToL2 period hPeriod Fiber frame mu field‖)]

/-- First-jet component-energy certificate. -/
theorem certificate
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    0 ≤ smoothFirstJetComponentEnergy period hPeriod Fiber frame mu field ∧
      ‖smoothToH1GraphLinearMap period hPeriod Fiber frame mu field‖ ^ 2 ≤
        smoothFirstJetComponentEnergy period hPeriod Fiber frame mu field :=
  ⟨smoothFirstJetComponentEnergy_nonnegative
      period hPeriod Fiber frame mu field,
    smoothToH1Graph_norm_sq_le_componentEnergy
      period hPeriod Fiber frame mu field⟩

end
end P0EFTJanusMappingTorusH1GraphComponentEnergy4D
end JanusFormal
