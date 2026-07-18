import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedScalarStressVariation4D

/-!
# Holonomic scalar-field variation on a four-dimensional chart

This gate removes the independent-gradient shortcut on the continuous chart
`R^4`.  A differentiable scalar field supplies both its value and the
coordinate covector extracted from its actual Frechet derivative.  The affine
field variation therefore varies `phi` and `d phi` together, and the resulting
pointwise and integrated first variations are proved.

The chart is still flat and global.  No identification with the decorated
Janus mapping torus, covariant derivative, integration by parts, curved wave
equation, boundary condition or stress-conservation theorem is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusHolonomicScalarFieldVariation4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusIntegratedScalarStressVariation4D

abbrev Coordinate4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private theorem scalarMatterJet_ext
    {first second : ScalarMatterJet}
    (hField : first.field = second.field)
    (hGradient : first.gradient = second.gradient) : first = second := by
  cases first
  cases second
  simp_all

/-- Coordinate covector of an actual Frechet derivative. -/
def coordinateGradient
    (field : Coordinate4 -> Real) (point : Coordinate4) :
    P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4 :=
  fun index => fderiv Real field point (Pi.single index 1)

/-- Holonomic first jet: value and gradient come from one scalar field. -/
def holonomicScalarJet
    (field : Coordinate4 -> Real) (point : Coordinate4) : ScalarMatterJet where
  field := field point
  gradient := coordinateGradient field point

@[simp]
theorem holonomicScalarJet_field
    (field : Coordinate4 -> Real) (point : Coordinate4) :
    (holonomicScalarJet field point).field = field point := rfl

@[simp]
theorem holonomicScalarJet_gradient
    (field : Coordinate4 -> Real) (point : Coordinate4) :
    (holonomicScalarJet field point).gradient = coordinateGradient field point := rfl

/-- Affine line in the genuine scalar function space. -/
def scalarFieldLine
    (field variation : Coordinate4 -> Real) (epsilon : Real) :
    Coordinate4 -> Real :=
  fun point => field point + epsilon * variation point

theorem fderiv_scalarFieldLine
    (field variation : Coordinate4 -> Real) (point : Coordinate4)
    (epsilon : Real)
    (hField : DifferentiableAt Real field point)
    (hVariation : DifferentiableAt Real variation point) :
    fderiv Real (scalarFieldLine field variation epsilon) point =
      fderiv Real field point + epsilon • fderiv Real variation point := by
  rw [show scalarFieldLine field variation epsilon =
      fun x => field x + epsilon * variation x from rfl]
  rw [fderiv_fun_add hField (hVariation.const_mul epsilon),
    fderiv_const_mul hVariation epsilon]

/-- The actual jet of the function-space line is exactly the simultaneous
value/gradient jet line. -/
theorem holonomicScalarJet_scalarFieldLine
    (field variation : Coordinate4 -> Real) (point : Coordinate4)
    (epsilon : Real)
    (hField : DifferentiableAt Real field point)
    (hVariation : DifferentiableAt Real variation point) :
    holonomicScalarJet (scalarFieldLine field variation epsilon) point =
      scalarJetLine (holonomicScalarJet field point)
        (holonomicScalarJet variation point) epsilon := by
  apply scalarMatterJet_ext
  · rfl
  · funext index
    simp only [holonomicScalarJet, coordinateGradient, scalarJetLine]
    rw [fderiv_scalarFieldLine field variation point epsilon hField hVariation]
    simp

/-- Scalar density with determinant measure and inverse from one fixed metric,
while the matter jet follows the actual field-space line. -/
def holonomicScalarDensityCurve
    (data : FixedSignMetric4) (massSquared source : Real)
    (field variation : Coordinate4 -> Real)
    (point : Coordinate4) (epsilon : Real) : Real :=
  Real.sqrt |Matrix.det data.metric| *
    scalarMatterLagrangian massSquared source data.metric⁻¹
      (holonomicScalarJet (scalarFieldLine field variation epsilon) point)

/-- Exact holonomic matter variation coefficient. -/
def holonomicScalarDensityFirstVariation
    (data : FixedSignMetric4) (massSquared source : Real)
    (field variation : Coordinate4 -> Real)
    (point : Coordinate4) : Real :=
  Real.sqrt |Matrix.det data.metric| *
    scalarMatterFirstVariation massSquared source data.metric⁻¹ 0
      (holonomicScalarJet field point) (holonomicScalarJet variation point)

theorem holonomicScalarDensityCurve_hasDerivAt
    (data : FixedSignMetric4) (massSquared source : Real)
    (field variation : Coordinate4 -> Real) (point : Coordinate4)
    (hField : DifferentiableAt Real field point)
    (hVariation : DifferentiableAt Real variation point) :
    HasDerivAt
      (holonomicScalarDensityCurve data massSquared source
        field variation point)
      (holonomicScalarDensityFirstVariation data massSquared source
        field variation point) 0 := by
  have hMatter := scalarMatterLagrangian_line_hasDerivAt
    massSquared source data.metric⁻¹ 0
    (holonomicScalarJet field point) (holonomicScalarJet variation point)
  have hDensity := hMatter.const_mul (Real.sqrt |Matrix.det data.metric|)
  refine (hDensity.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun epsilon => ?_)).congr_deriv ?_
  · simp only [holonomicScalarDensityCurve]
    rw [holonomicScalarJet_scalarFieldLine field variation point epsilon
      hField hVariation]
    simp [inverseMetricLine]
  · simp [holonomicScalarDensityFirstVariation]

/-- A continuous-chart scalar sector: the field and its variation are genuine
functions; the metric is allowed to vary with the spacetime point. -/
structure HolonomicScalarSector4 where
  metric : Coordinate4 -> FixedSignMetric4
  field : Coordinate4 -> Real
  variation : Coordinate4 -> Real
  field_differentiable : Differentiable Real field
  variation_differentiable : Differentiable Real variation
  massSquared : Real
  source : Real

def integratedHolonomicScalarAction
    (mu : Measure Coordinate4) (sector : HolonomicScalarSector4)
    (epsilon : Real) : Real :=
  integral mu (fun point => holonomicScalarDensityCurve
    (sector.metric point) sector.massSquared sector.source
    sector.field sector.variation point epsilon)

def integratedHolonomicScalarFirstVariation
    (mu : Measure Coordinate4) (sector : HolonomicScalarSector4) : Real :=
  integral mu (fun point => holonomicScalarDensityFirstVariation
    (sector.metric point) sector.massSquared sector.source
    sector.field sector.variation point)

/-- Genuine function-space derivative after a justified exchange with the
spacetime integral. -/
theorem integratedHolonomicScalarAction_hasDerivAt
    (mu : Measure Coordinate4) (sector : HolonomicScalarSector4)
    (parameterDomain : Set Real)
    (hDomain : parameterDomain ∈ nhds (0 : Real))
    (hDensityMeasurable : Filter.Eventually (fun epsilon =>
      AEStronglyMeasurable (fun point => holonomicScalarDensityCurve
        (sector.metric point) sector.massSquared sector.source
        sector.field sector.variation point epsilon) mu) (nhds (0 : Real)))
    (hDensityIntegrable : Integrable (fun point => holonomicScalarDensityCurve
      (sector.metric point) sector.massSquared sector.source
      sector.field sector.variation point 0) mu)
    (hVariationMeasurable : AEStronglyMeasurable
      (fun point => holonomicScalarDensityFirstVariation
        (sector.metric point) sector.massSquared sector.source
        sector.field sector.variation point) mu)
    (bound : Coordinate4 -> Real)
    (hLipschitz : ∀ᵐ point ∂mu,
      LipschitzOnWith (Real.nnabs (bound point))
        (holonomicScalarDensityCurve
          (sector.metric point) sector.massSquared sector.source
          sector.field sector.variation point) parameterDomain)
    (hBoundIntegrable : Integrable bound mu) :
    HasDerivAt (integratedHolonomicScalarAction mu sector)
      (integratedHolonomicScalarFirstVariation mu sector) 0 := by
  have hPointwise : ∀ᵐ point ∂mu,
      HasDerivAt
        (holonomicScalarDensityCurve
          (sector.metric point) sector.massSquared sector.source
          sector.field sector.variation point)
        (holonomicScalarDensityFirstVariation
          (sector.metric point) sector.massSquared sector.source
          sector.field sector.variation point) 0 :=
    Filter.Eventually.of_forall fun point =>
      holonomicScalarDensityCurve_hasDerivAt
        (sector.metric point) sector.massSquared sector.source
        sector.field sector.variation point
        (sector.field_differentiable point)
        (sector.variation_differentiable point)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    hDomain hDensityMeasurable hDensityIntegrable hVariationMeasurable
    hLipschitz hBoundIntegrable hPointwise).2

end

end P0EFTJanusHolonomicScalarFieldVariation4D
end JanusFormal
