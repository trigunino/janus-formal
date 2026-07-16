import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFlatHolonomicScalarEuler4D

/-!
# Integrated weak scalar Euler equation on the flat four-chart

The pointwise Euler-plus-flux decomposition is integrated on an arbitrary
measure.  Under explicit integrability and vanishing-flux hypotheses, the
actual action derivative equals the weak pairing with the flat scalar Euler
operator.
-/

namespace JanusFormal
namespace P0EFTJanusIntegratedFlatScalarEuler4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusHolonomicScalarFieldVariation4D
open P0EFTJanusFlatHolonomicScalarEuler4D

abbrev Coordinate4 := P0EFTJanusHolonomicScalarFieldVariation4D.Coordinate4
abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

/-- Fixed-metric scalar sector with enough regularity for the divergence
identity at every chart point. -/
structure FlatScalarEulerSector4 where
  metric : FixedSignMetric4
  field : Coordinate4 → Real
  variation : Coordinate4 → Real
  field_differentiable : Differentiable Real field
  variation_differentiable : Differentiable Real variation
  raisedGradient_differentiable : ∀ index : Index4,
    Differentiable Real
      (fun x ↦ raisedCoordinateGradient metric.metric⁻¹ field x index)
  massSquared : Real
  source : Real

def FlatScalarEulerSector4.toHolonomicScalarSector
    (sector : FlatScalarEulerSector4) : HolonomicScalarSector4 where
  metric := fun _ ↦ sector.metric
  field := sector.field
  variation := sector.variation
  field_differentiable := sector.field_differentiable
  variation_differentiable := sector.variation_differentiable
  massSquared := sector.massSquared
  source := sector.source

def integratedFlatScalarFirstVariation
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4) : Real :=
  integral mu fun point ↦
    holonomicScalarDensityFirstVariation sector.metric
      sector.massSquared sector.source sector.field sector.variation point

def integratedFlatScalarFlux
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4) : Real :=
  integral mu fun point ↦
    Real.sqrt |Matrix.det sector.metric.metric| *
      coordinateDivergence
        (scalarBoundaryFlux sector.metric.metric⁻¹
          sector.field sector.variation) point

def integratedFlatScalarEulerPairing
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4) : Real :=
  integral mu fun point ↦
    Real.sqrt |Matrix.det sector.metric.metric| * sector.variation point *
      flatScalarEulerOperator sector.metric.metric⁻¹
        sector.massSquared sector.source sector.field point

/-- Exact integrated boundary condition required by the weak equation. -/
def IntegratedScalarFluxVanishes
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4) : Prop :=
  integratedFlatScalarFlux mu sector = 0

theorem pointwise_flatScalarEuler_decomposition
    (sector : FlatScalarEulerSector4) (point : Coordinate4) :
    holonomicScalarDensityFirstVariation sector.metric
        sector.massSquared sector.source sector.field sector.variation point =
      Real.sqrt |Matrix.det sector.metric.metric| *
          coordinateDivergence
            (scalarBoundaryFlux sector.metric.metric⁻¹
              sector.field sector.variation) point +
        Real.sqrt |Matrix.det sector.metric.metric| * sector.variation point *
          flatScalarEulerOperator sector.metric.metric⁻¹
            sector.massSquared sector.source sector.field point := by
  have h := holonomicScalarDensityFirstVariation_euler_decomposition
    sector.metric sector.massSquared sector.source sector.field sector.variation point
    (sector.variation_differentiable point)
    (fun index ↦ sector.raisedGradient_differentiable index point)
  rw [h]
  ring

/-- Once the boundary flux vanishes, the integrated first variation is exactly
the weak Euler pairing. -/
theorem integratedFlatScalarFirstVariation_eq_eulerPairing
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4)
    (hFluxIntegrable : Integrable (fun point ↦
      Real.sqrt |Matrix.det sector.metric.metric| *
        coordinateDivergence
          (scalarBoundaryFlux sector.metric.metric⁻¹
            sector.field sector.variation) point) mu)
    (hEulerIntegrable : Integrable (fun point ↦
      Real.sqrt |Matrix.det sector.metric.metric| * sector.variation point *
        flatScalarEulerOperator sector.metric.metric⁻¹
          sector.massSquared sector.source sector.field point) mu)
    (hFlux : IntegratedScalarFluxVanishes mu sector) :
    integratedFlatScalarFirstVariation mu sector =
      integratedFlatScalarEulerPairing mu sector := by
  calc
    integratedFlatScalarFirstVariation mu sector =
        integral mu (fun point ↦
          Real.sqrt |Matrix.det sector.metric.metric| *
              coordinateDivergence
                (scalarBoundaryFlux sector.metric.metric⁻¹
                  sector.field sector.variation) point +
            Real.sqrt |Matrix.det sector.metric.metric| * sector.variation point *
              flatScalarEulerOperator sector.metric.metric⁻¹
                sector.massSquared sector.source sector.field point) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (pointwise_flatScalarEuler_decomposition sector)
    _ = integratedFlatScalarFlux mu sector +
        integratedFlatScalarEulerPairing mu sector := by
      exact integral_add hFluxIntegrable hEulerIntegrable
    _ = integratedFlatScalarEulerPairing mu sector := by
      rw [hFlux]
      simp

/-- Any already-justified derivative of the holonomic action acquires the
explicit weak Euler coefficient after the boundary condition is discharged. -/
theorem integratedHolonomicScalarAction_euler_hasDerivAt
    (mu : Measure Coordinate4) (sector : FlatScalarEulerSector4)
    (hAction : HasDerivAt
      (integratedHolonomicScalarAction mu sector.toHolonomicScalarSector)
      (integratedFlatScalarFirstVariation mu sector) 0)
    (hFluxIntegrable : Integrable (fun point ↦
      Real.sqrt |Matrix.det sector.metric.metric| *
        coordinateDivergence
          (scalarBoundaryFlux sector.metric.metric⁻¹
            sector.field sector.variation) point) mu)
    (hEulerIntegrable : Integrable (fun point ↦
      Real.sqrt |Matrix.det sector.metric.metric| * sector.variation point *
        flatScalarEulerOperator sector.metric.metric⁻¹
          sector.massSquared sector.source sector.field point) mu)
    (hFlux : IntegratedScalarFluxVanishes mu sector) :
    HasDerivAt
      (integratedHolonomicScalarAction mu sector.toHolonomicScalarSector)
      (integratedFlatScalarEulerPairing mu sector) 0 :=
  hAction.congr_deriv
    (integratedFlatScalarFirstVariation_eq_eulerPairing
      mu sector hFluxIntegrable hEulerIntegrable hFlux)

end

end P0EFTJanusIntegratedFlatScalarEuler4D
end JanusFormal
