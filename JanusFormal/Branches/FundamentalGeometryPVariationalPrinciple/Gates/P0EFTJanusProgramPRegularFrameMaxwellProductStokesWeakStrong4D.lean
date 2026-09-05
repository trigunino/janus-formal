import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellProductCoareaEulerBoundary4D

/-! # Maxwell product Stokes contract and weak/strong reduction -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellProductStokesWeakStrong4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellProductCoareaEulerBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

/-- Product-coordinate density containing only the weighted strong Maxwell
pairing. -/
noncomputable def canonicalRegularMaxwellProductWeightedStrongDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  let patch := canonicalPhysicalScalarEulerProductPatch period hPeriod parameter
  ∑ component : Fin 2,
    regularFrameMaxwellStrongPairing period hPeriod metric potential variation
      component patch 0

/-- Product-coordinate divergence of the Maxwell boundary current. -/
noncomputable def canonicalRegularMaxwellProductBoundaryDivergenceDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  let patch := canonicalPhysicalScalarEulerProductPatch period hPeriod parameter
  ∑ component : Fin 2,
    maxwellBoundaryDivergence
      (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
        potential patch component)
      (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
        component patch)
      0

/-- Exact pointwise split of Gate436's combined product density. -/
theorem canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_strong_sub_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod metric
        potential variation parameter =
      canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod metric
          potential variation parameter -
        canonicalRegularMaxwellProductBoundaryDivergenceDensity period hPeriod
          metric potential variation parameter := by
  unfold canonicalRegularMaxwellProductWeightedBoundaryResidual
    canonicalRegularMaxwellProductWeightedStrongDensity
    canonicalRegularMaxwellProductBoundaryDivergenceDensity
  dsimp only
  rw [Finset.sum_sub_distrib]

/-- Precise remaining analytic/geometric input for product-coordinate Maxwell
integration by parts. -/
structure RegularFrameMaxwellProductStokesData
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) where
  strong_integrable : ∀ variation : SmoothAbelianGaugePotential period hPeriod,
    Integrable
      (canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod metric
        potential variation)
      (canonicalLatitudeCauchyJetProductMeasure period)
  boundary_integrable :
    ∀ variation : SmoothAbelianGaugePotential period hPeriod,
      Integrable
        (canonicalRegularMaxwellProductBoundaryDivergenceDensity period hPeriod
          metric potential variation)
        (canonicalLatitudeCauchyJetProductMeasure period)
  boundary_integral_eq_zero :
    ∀ variation : SmoothAbelianGaugePotential period hPeriod,
      (∫ parameter,
        canonicalRegularMaxwellProductBoundaryDivergenceDensity period hPeriod
          metric potential variation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) = 0

/-- Under the exact product Stokes data, the intrinsic first variation is the
integral of the weighted strong residual pairing alone. -/
theorem intrinsicMaxwellFirstVariation_eq_integral_productWeightedStrong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (stokes : RegularFrameMaxwellProductStokesData period hPeriod metric
      potential) :
    intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ parameter,
        canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod
          metric potential variation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
  calc
    intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
        hPeriod metric potential variation
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
      (canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation
        period hPeriod metric potential variation
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).symm
    _ = ∫ parameter,
        canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod
          metric potential variation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period :=
      (integral_canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_global
        period hPeriod metric potential variation).symm
    _ =
        (∫ parameter,
          canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod
            metric potential variation parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) -
        ∫ parameter,
          canonicalRegularMaxwellProductBoundaryDivergenceDensity period hPeriod
            metric potential variation parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun parameter =>
        canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_strong_sub_boundary
          period hPeriod metric potential variation parameter)]
      exact integral_sub (stokes.strong_integrable variation)
        (stokes.boundary_integrable variation)
    _ = ∫ parameter,
        canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod
          metric potential variation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
      rw [stokes.boundary_integral_eq_zero variation, sub_zero]

/-- Weak stationarity of the intrinsic Maxwell action for the canonical
physical measure. -/
def RegularFrameMaxwellCanonicalWeakStationary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Prop :=
  ∀ variation : SmoothAbelianGaugePotential period hPeriod,
    intrinsicMaxwellFirstVariation period hPeriod metric
      (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric potential
        variation)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0

/-- Integrated weighted-strong Maxwell equation on the explicit product
domain. -/
def RegularFrameMaxwellProductWeightedWeakEquation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Prop :=
  ∀ variation : SmoothAbelianGaugePotential period hPeriod,
    (∫ parameter,
      canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod metric
        potential variation parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) = 0

/-- Product Stokes reduces authentic Maxwell stationarity exactly to the
integrated weighted strong equation. -/
theorem regularFrameMaxwellCanonicalWeakStationary_iff_productWeightedWeakEquation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (stokes : RegularFrameMaxwellProductStokesData period hPeriod metric
      potential) :
    RegularFrameMaxwellCanonicalWeakStationary period hPeriod metric potential ↔
      RegularFrameMaxwellProductWeightedWeakEquation period hPeriod metric
        potential := by
  constructor
  · intro hWeak variation
    rw [← intrinsicMaxwellFirstVariation_eq_integral_productWeightedStrong
      period hPeriod metric potential variation stokes]
    exact hWeak variation
  · intro hStrong variation
    rw [intrinsicMaxwellFirstVariation_eq_integral_productWeightedStrong
      period hPeriod metric potential variation stokes]
    exact hStrong variation

/-- Gate marker for the exact Maxwell product Stokes reduction. -/
theorem regular_frame_maxwell_product_stokes_weak_strong_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (stokes : RegularFrameMaxwellProductStokesData period hPeriod metric
      potential) :
    RegularFrameMaxwellCanonicalWeakStationary period hPeriod metric potential ↔
      RegularFrameMaxwellProductWeightedWeakEquation period hPeriod metric
        potential :=
  regularFrameMaxwellCanonicalWeakStationary_iff_productWeightedWeakEquation
    period hPeriod metric potential stokes

end
end P0EFTJanusProgramPRegularFrameMaxwellProductStokesWeakStrong4D
end JanusFormal
