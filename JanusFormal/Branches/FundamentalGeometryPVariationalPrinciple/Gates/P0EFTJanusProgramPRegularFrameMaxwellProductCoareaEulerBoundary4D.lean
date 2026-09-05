import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D

/-! # Maxwell weighted Euler-boundary residual in product coarea coordinates -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellProductCoareaEulerBoundary4D

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
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

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- The combined weighted strong pairing minus boundary divergence evaluated
in the canonical product patch at coordinate zero. -/
noncomputable def canonicalRegularMaxwellProductWeightedBoundaryResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  let patch := canonicalPhysicalScalarEulerProductPatch period hPeriod parameter
  ∑ component : Fin 2,
    (regularFrameMaxwellStrongPairing period hPeriod metric potential variation
        component patch 0 -
      maxwellBoundaryDivergence
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component patch)
        0)

/-- Pointwise, the product residual is the pullback of the authentic global
Maxwell first-variation density. -/
theorem canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_firstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod metric
        potential variation parameter =
      regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod
          parameter) := by
  let patch := canonicalPhysicalScalarEulerProductPatch period hPeriod parameter
  calc
    canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod metric
        potential variation parameter =
        ∑ component : Fin 2,
          (regularFrameMaxwellStrongPairing period hPeriod metric potential
              variation component patch 0 -
            maxwellBoundaryDivergence
              (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
                potential patch component)
              (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
                variation component patch)
              0) := rfl
    _ = regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap 0) :=
      (regularMaxwellFirstVariationField_eq_weightedStrongPairing_sub_boundary
        period hPeriod metric potential variation patch 0).symm
    _ = regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod
            parameter) := by
      rw [canonicalPhysicalScalarEulerProductPatch_zero]

/-- The product residual is also the pullback of Gate434's canonical weighted
representative. -/
theorem canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_canonical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod metric
        potential variation parameter =
      canonicalRegularMaxwellWeightedStrongBoundaryResidual period hPeriod
        metric potential variation
          (canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod
            parameter) := by
  rw [canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_firstVariation,
    canonicalRegularMaxwellWeightedStrongBoundaryResidual_eq_firstVariation]

/-- Integrability of the combined product residual follows from smoothness on
the compact quotient and exact measure preservation. -/
theorem canonicalRegularMaxwellProductWeightedBoundaryResidual_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
      (canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod
        metric potential variation)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  let field := regularMaxwellFirstVariationField period hPeriod metric
    (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
      potential variation)
  have hGlobal : Integrable field
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    field.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPullback :=
    (canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving period
      hPeriod).integrable_comp_of_integrable hGlobal
  exact hPullback.congr
    (Filter.Eventually.of_forall fun parameter =>
      (canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_firstVariation
        period hPeriod metric potential variation parameter).symm)

/-- Exact coarea transport of the combined Maxwell Euler-boundary residual. -/
theorem integral_canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    (∫ parameter,
      canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod
        metric potential variation parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
        hPeriod metric potential variation
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  let physicalMap := canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod
  let sourceMeasure := canonicalLatitudeCauchyJetProductMeasure period
  let targetMeasure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let field := regularMaxwellFirstVariationField period hPeriod metric
    (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
      potential variation)
  have hPreserving : MeasurePreserving physicalMap sourceMeasure targetMeasure :=
    canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving period hPeriod
  have hGlobal : Integrable field targetMeasure :=
    field.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hStrong : AEStronglyMeasurable field
      (Measure.map physicalMap sourceMeasure) := by
    rw [hPreserving.map_eq]
    exact hGlobal.aestronglyMeasurable
  calc
    (∫ parameter,
      canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod
        metric potential variation parameter ∂sourceMeasure) =
        ∫ parameter, field (physicalMap parameter) ∂sourceMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun parameter =>
        canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_firstVariation
          period hPeriod metric potential variation parameter)
    _ = ∫ point, field point ∂Measure.map physicalMap sourceMeasure :=
      (MeasureTheory.integral_map
        hPreserving.measurable.aemeasurable hStrong).symm
    _ = ∫ point, field point ∂targetMeasure := by
      rw [hPreserving.map_eq]
    _ = intrinsicMaxwellFirstVariation period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) targetMeasure := rfl
    _ = canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
          hPeriod metric potential variation targetMeasure :=
      (canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation
        period hPeriod metric potential variation targetMeasure).symm

/-- Gate marker for exact product-coarea realization of the combined Maxwell
weighted Euler-boundary residual. -/
theorem regular_frame_maxwell_product_coarea_euler_boundary_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    (∫ parameter,
      canonicalRegularMaxwellProductWeightedBoundaryResidual period hPeriod
        metric potential variation parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
        hPeriod metric potential variation
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  integral_canonicalRegularMaxwellProductWeightedBoundaryResidual_eq_global
    period hPeriod metric potential variation

end
end P0EFTJanusProgramPRegularFrameMaxwellProductCoareaEulerBoundary4D
end JanusFormal
