import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHolonomicMetricScalarVariation4D

/-!
# Integrated simultaneous metric and holonomic scalar variation

The pointwise same-metric/same-field derivative is promoted to a genuine
derivative of a spacetime integral under the standard dominated local
differentiation contract.  The base remains the flat `R^4` chart and the
domination hypotheses remain explicit.
-/

namespace JanusFormal
namespace P0EFTJanusIntegratedHolonomicMetricScalarVariation4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusHolonomicScalarFieldVariation4D
open P0EFTJanusHolonomicMetricScalarVariation4D

abbrev Coordinate4 := P0EFTJanusHolonomicScalarFieldVariation4D.Coordinate4

/-- One integrated sector with metric and scalar varied on the same parameter. -/
structure IntegratedHolonomicMetricScalarSector4 where
  metric : Coordinate4 → FixedSignMetric4
  metricVariation : Coordinate4 → SymmetricMetricVariation4
  field : Coordinate4 → Real
  fieldVariation : Coordinate4 → Real
  field_differentiable : Differentiable Real field
  fieldVariation_differentiable : Differentiable Real fieldVariation
  massSquared : Real
  source : Real

def integratedHolonomicMetricScalarAction
    (mu : Measure Coordinate4)
    (sector : IntegratedHolonomicMetricScalarSector4)
    (epsilon : Real) : Real :=
  integral mu fun point ↦
    holonomicMetricScalarDensityCurve
      (sector.metric point) (sector.metricVariation point)
      sector.massSquared sector.source sector.field sector.fieldVariation
      point epsilon

def integratedHolonomicMetricScalarFirstVariation
    (mu : Measure Coordinate4)
    (sector : IntegratedHolonomicMetricScalarSector4) : Real :=
  integral mu fun point ↦
    holonomicMetricScalarDensityFirstVariation
      (sector.metric point) (sector.metricVariation point)
      sector.massSquared sector.source sector.field sector.fieldVariation point

/-- Standard scalar derivative wrapper for the explicit Frobenius composition
used by the pointwise gate. -/
theorem pointwiseHolonomicMetricScalarDensity_hasDerivAt
    (sector : IntegratedHolonomicMetricScalarSector4)
    (point : Coordinate4) :
    HasDerivAt
      (holonomicMetricScalarDensityCurve
        (sector.metric point) (sector.metricVariation point)
        sector.massSquared sector.source sector.field sector.fieldVariation point)
      (holonomicMetricScalarDensityFirstVariation
        (sector.metric point) (sector.metricVariation point)
        sector.massSquared sector.source sector.field sector.fieldVariation point) 0 := by
  have h := holonomicMetricScalarDensityCurve_hasDerivAt
    (sector.metric point) (sector.metricVariation point)
    sector.massSquared sector.source sector.field sector.fieldVariation point
    (sector.field_differentiable point)
    (sector.fieldVariation_differentiable point)
  unfold FrobeniusScalarHasDerivAt at h
  exact h.hasDerivAt.congr_deriv (by simp)

/-- Derivative of the genuine spacetime integral, with no interchange hidden
behind notation. -/
theorem integratedHolonomicMetricScalarAction_hasDerivAt
    (mu : Measure Coordinate4)
    (sector : IntegratedHolonomicMetricScalarSector4)
    (parameterDomain : Set Real)
    (hDomain : parameterDomain ∈ nhds (0 : Real))
    (hDensityMeasurable : Filter.Eventually (fun epsilon ↦
      AEStronglyMeasurable (fun point ↦
        holonomicMetricScalarDensityCurve
          (sector.metric point) (sector.metricVariation point)
          sector.massSquared sector.source sector.field sector.fieldVariation
          point epsilon) mu) (nhds (0 : Real)))
    (hDensityIntegrable : Integrable (fun point ↦
      holonomicMetricScalarDensityCurve
        (sector.metric point) (sector.metricVariation point)
        sector.massSquared sector.source sector.field sector.fieldVariation
        point 0) mu)
    (hVariationMeasurable : AEStronglyMeasurable (fun point ↦
      holonomicMetricScalarDensityFirstVariation
        (sector.metric point) (sector.metricVariation point)
        sector.massSquared sector.source sector.field sector.fieldVariation point) mu)
    (bound : Coordinate4 → Real)
    (hLipschitz : ∀ᵐ point ∂mu,
      LipschitzOnWith (Real.nnabs (bound point))
        (holonomicMetricScalarDensityCurve
          (sector.metric point) (sector.metricVariation point)
          sector.massSquared sector.source sector.field sector.fieldVariation point)
        parameterDomain)
    (hBoundIntegrable : Integrable bound mu) :
    HasDerivAt (integratedHolonomicMetricScalarAction mu sector)
      (integratedHolonomicMetricScalarFirstVariation mu sector) 0 := by
  have hPointwise : ∀ᵐ point ∂mu,
      HasDerivAt
        (holonomicMetricScalarDensityCurve
          (sector.metric point) (sector.metricVariation point)
          sector.massSquared sector.source sector.field sector.fieldVariation point)
        (holonomicMetricScalarDensityFirstVariation
          (sector.metric point) (sector.metricVariation point)
          sector.massSquared sector.source sector.field sector.fieldVariation point) 0 :=
    Filter.Eventually.of_forall
      (pointwiseHolonomicMetricScalarDensity_hasDerivAt sector)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    hDomain hDensityMeasurable hDensityIntegrable hVariationMeasurable
    hLipschitz hBoundIntegrable hPointwise).2

end

end P0EFTJanusIntegratedHolonomicMetricScalarVariation4D
end JanusFormal
