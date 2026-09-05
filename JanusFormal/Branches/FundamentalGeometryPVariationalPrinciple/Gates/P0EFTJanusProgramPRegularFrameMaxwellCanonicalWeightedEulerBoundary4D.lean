import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D

/-! # Canonical weighted Maxwell Euler-boundary residual -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D

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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Canonical-chart representative of the weighted strong Maxwell pairing
minus its boundary divergence. -/
noncomputable def canonicalRegularMaxwellWeightedStrongBoundaryResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  ∑ component : Fin 2,
    (regularFrameMaxwellStrongPairing period hPeriod metric potential variation
        component witness.patch witness.coordinate -
      maxwellBoundaryDivergence
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential witness.patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component witness.patch)
        witness.coordinate)

/-- The canonical weighted residual is the authentic Maxwell first-variation
density. -/
theorem canonicalRegularMaxwellWeightedStrongBoundaryResidual_eq_firstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalRegularMaxwellWeightedStrongBoundaryResidual period hPeriod metric
        potential variation point =
      regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point := by
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  calc
    canonicalRegularMaxwellWeightedStrongBoundaryResidual period hPeriod metric
        potential variation point =
        ∑ component : Fin 2,
          (regularFrameMaxwellStrongPairing period hPeriod metric potential
              variation component witness.patch witness.coordinate -
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
      (regularMaxwellFirstVariationField_eq_weightedStrongPairing_sub_boundary
        period hPeriod metric potential variation witness.patch
          witness.coordinate).symm
    _ = regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) point := by
      rw [witness.coordinate_eq]

/-- The weighted and earlier Euler-coefficient canonical representatives
coincide pointwise. -/
theorem canonicalRegularMaxwellWeightedStrongBoundaryResidual_eq_eulerBoundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalRegularMaxwellWeightedStrongBoundaryResidual period hPeriod metric
        potential variation point =
      canonicalRegularMaxwellEulerBoundaryResidual period hPeriod metric
        potential variation point := by
  rw [canonicalRegularMaxwellWeightedStrongBoundaryResidual_eq_firstVariation,
    canonicalRegularMaxwellEulerBoundaryResidual_eq_regularMaxwellFirstVariationField]

/-- Integral of the canonical weighted strong residual with its boundary
divergence retained. -/
noncomputable def canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    canonicalRegularMaxwellWeightedStrongBoundaryResidual period hPeriod metric
      potential variation point ∂measure

/-- The integrated weighted residual is exactly the intrinsic Maxwell first
variation for every reference measure. -/
theorem canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period hPeriod
        metric potential variation measure =
      intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) measure := by
  unfold canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral
    intrinsicMaxwellFirstVariation
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun point =>
      canonicalRegularMaxwellWeightedStrongBoundaryResidual_eq_firstVariation
        period hPeriod metric potential variation point)

/-- Gate marker for the canonical integrated weighted Maxwell residual. -/
theorem regular_frame_maxwell_canonical_weighted_euler_boundary_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period hPeriod
        metric potential variation measure =
      intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) measure :=
  canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation
    period hPeriod metric potential variation measure

end
end P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D
end JanusFormal
