import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellWeightedStrongPDE4D

/-! # Stored-frame Maxwell weighted Euler-boundary decomposition -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellWeightedStrongPDE4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise pairing of the stored-action strong Maxwell residual with a
gauge-potential variation. -/
def regularFrameMaxwellStrongPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ second : Index4,
    regularFrameMaxwellStrongResidual period hPeriod metric potential component
        patch coordinate second *
      regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
        component patch coordinate second

/-- The Euler pairing is exactly the pointwise pairing with the weighted
stored-frame strong residual. -/
theorem regularIntrinsicMaxwellEulerPairing_eq_weightedStrongPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    maxwellEulerPairing
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component patch)
        coordinate =
      regularFrameMaxwellStrongPairing period hPeriod metric potential variation
        component patch coordinate := by
  unfold maxwellEulerPairing regularFrameMaxwellStrongPairing
  apply Finset.sum_congr rfl
  intro second _
  rw [regularIntrinsicMaxwellEulerCoefficient_eq_weightedStrongResidual]

/-- Exact local integration-by-parts formula expressed through the weighted
strong Maxwell residual selected by the stored action. -/
theorem regularMaxwellFirstVariationField_eq_weightedStrongPairing_sub_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        (regularFrameMaxwellStrongPairing period hPeriod metric potential
            variation component patch coordinate -
          maxwellBoundaryDivergence
            (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
              potential patch component)
            (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
              variation component patch)
            coordinate) := by
  rw [regular_maxwell_first_variation_field_eq_euler_sub_boundary_gate]
  apply Finset.sum_congr rfl
  intro component _
  rw [regularIntrinsicMaxwellEulerPairing_eq_weightedStrongPairing]

/-- Gate marker for the exact weighted Maxwell Euler-boundary split. -/
theorem regular_frame_maxwell_weighted_euler_boundary_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap coordinate) =
        ∑ component : Fin 2,
          (regularFrameMaxwellStrongPairing period hPeriod metric potential
              variation component patch coordinate -
            maxwellBoundaryDivergence
              (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
                potential patch component)
              (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
                variation component patch)
              coordinate) :=
  regularMaxwellFirstVariationField_eq_weightedStrongPairing_sub_boundary
    period hPeriod metric potential variation

end
end P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D
end JanusFormal
