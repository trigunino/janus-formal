import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

/-! # Canonical scalar Euler--boundary residual for the Maxwell variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The Euler-minus-boundary Maxwell density evaluated in the canonically
selected holonomic chart through a quotient point. -/
noncomputable def canonicalRegularMaxwellEulerBoundaryResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  ∑ component : Fin 2,
    (maxwellEulerPairing
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential witness.patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component witness.patch)
        witness.coordinate -
      maxwellBoundaryDivergence
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential witness.patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component witness.patch)
        witness.coordinate)

/-- The selected Euler--boundary residual is pointwise the authentic smooth
Maxwell first-variation density. -/
theorem canonicalRegularMaxwellEulerBoundaryResidual_eq_regularMaxwellFirstVariationField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalRegularMaxwellEulerBoundaryResidual period hPeriod metric
        potential variation point =
      regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point := by
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  calc
    canonicalRegularMaxwellEulerBoundaryResidual period hPeriod metric
        potential variation point =
        ∑ component : Fin 2,
          (maxwellEulerPairing
              (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
                potential witness.patch component)
              (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
                variation component witness.patch)
              witness.coordinate -
            maxwellBoundaryDivergence
              (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
                potential witness.patch component)
              (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
                variation component witness.patch)
              witness.coordinate) := rfl
    _ = regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (witness.patch.coordinateMap witness.coordinate) :=
      (regular_maxwell_first_variation_field_eq_euler_sub_boundary_gate
        period hPeriod metric potential variation witness.patch
          witness.coordinate).symm
    _ = regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) point := by
      rw [witness.coordinate_eq]

/-- Integral of the canonically selected scalar Maxwell residual. -/
noncomputable def canonicalRegularMaxwellEulerBoundaryResidualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    canonicalRegularMaxwellEulerBoundaryResidual period hPeriod metric
      potential variation point ∂measure

/-- The integrated canonical residual is exactly the intrinsic Maxwell first
variation; no pointwise stationarity hypothesis is used. -/
theorem canonicalRegularMaxwellEulerBoundaryResidualIntegral_eq_intrinsicMaxwellFirstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    canonicalRegularMaxwellEulerBoundaryResidualIntegral period hPeriod metric
        potential variation measure =
      intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) measure := by
  unfold canonicalRegularMaxwellEulerBoundaryResidualIntegral
    intrinsicMaxwellFirstVariation
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun point =>
      canonicalRegularMaxwellEulerBoundaryResidual_eq_regularMaxwellFirstVariationField
        period hPeriod metric potential variation point)

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
end JanusFormal
