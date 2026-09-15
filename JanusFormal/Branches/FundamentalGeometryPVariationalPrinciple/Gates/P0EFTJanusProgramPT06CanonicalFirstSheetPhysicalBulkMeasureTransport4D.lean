import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBoundaryMeasureTransport4D

/-!
# Physical-image measure for the canonical first-sheet bulk collar

The regional coordinate source measure is multiplied by Lebesgue measure on
the half-open unit normal interval and pushed through the genuine finite-collar
map into the effective bulk.  The transported bulk integrand pulls back to
Gate 1069's corrected physical densitized divergence, so Fubini and
`Measure.map` turn the regional coordinate Stokes law into an equality of
integrals over physical image measures.

These are parametrized image measures.  No Hausdorff or metric-volume
identification, isometry, or physical nullity statement is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBulkMeasureTransport4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Topology
open scoped Interval Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetRegionalPhysicalMetricStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBoundaryMeasureTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveBulkMeasurableSpace :
    MeasurableSpace (ProgramPT06EffectiveBulk period hPeriod) := borel _

local instance effectiveBulkBorelSpace :
    BorelSpace (ProgramPT06EffectiveBulk period hPeriod) where
  measurable_eq := rfl

/-- Lebesgue measure on the half-open unit normal interval. -/
def programPT06CanonicalFirstSheetUnitNormalMeasure : Measure Real :=
  volume.restrict (Set.Ioc (0 : Real) 1)

instance programPT06CanonicalFirstSheetUnitNormalMeasure_isFinite :
    IsFiniteMeasure programPT06CanonicalFirstSheetUnitNormalMeasure := by
  unfold programPT06CanonicalFirstSheetUnitNormalMeasure
  infer_instance

local instance programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure_sFinite :
    SFinite (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) := by
  unfold programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure
    programPT06WarpedNullCoordinateSourceMeasure
  infer_instance

/-- Regional source measure times the half-open unit-normal measure. -/
def programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure :
    Measure (ProgramPT06NullFaceSource3 × Real) :=
  (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period).prod
    programPT06CanonicalFirstSheetUnitNormalMeasure

/-- Genuine effective-bulk parametrization of the canonical collar.  The
projection makes it total; on `[0,1]` it is the finite-collar map itself. -/
def programPT06CanonicalFirstSheetPhysicalBulkMap
    (pole : StandardEquatorialTwoSphere)
    (parameter : ProgramPT06NullFaceSource3 × Real) :
    ProgramPT06EffectiveBulk period hPeriod :=
  cutBulkFiniteCollarToAmbient period hPeriod
    (programPT06CanonicalFirstSheetBoundaryMap
        period hPeriod pole parameter.1,
      Set.projIcc 0 1 zero_le_one parameter.2)

theorem programPT06CanonicalFirstSheetPhysicalBulkMap_continuous
    (pole : StandardEquatorialTwoSphere) :
    Continuous
      (programPT06CanonicalFirstSheetPhysicalBulkMap
        period hPeriod pole) := by
  have hBoundary : Continuous
      (fun parameter : ProgramPT06NullFaceSource3 × Real =>
        programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole parameter.1) :=
    (programPT06CanonicalFirstSheetBoundaryMap_contMDiff
      period hPeriod pole).continuous.comp continuous_fst
  have hNormal : Continuous
      (fun parameter : ProgramPT06NullFaceSource3 × Real =>
        Set.projIcc 0 1 zero_le_one parameter.2) :=
    continuous_projIcc.comp continuous_snd
  exact (cutBulkFiniteCollarToAmbient_contMDiff
    period hPeriod).continuous.comp (hBoundary.prodMk hNormal)

theorem programPT06CanonicalFirstSheetPhysicalBulkMap_mem_chart
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (radius : Real)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period)
    (hRadius : radius ∈ Set.Icc (0 : Real) 1) :
    programPT06CanonicalFirstSheetPhysicalBulkMap
        period hPeriod pole (source, radius) ∈
      (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole).source := by
  simpa [programPT06CanonicalFirstSheetPhysicalBulkMap,
    Set.projIcc_of_mem zero_le_one hRadius] using
    (programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
      period hPeriod pole source (⟨radius, hRadius⟩ : CutCollarInterval)
      hSource)

theorem programPT06CanonicalFirstSheetPhysicalBulkMap_coordinate
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (radius : Real)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period)
    (hRadius : radius ∈ Set.Icc (0 : Real) 1) :
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole
        (programPT06CanonicalFirstSheetPhysicalBulkMap
          period hPeriod pole (source, radius)) =
      programPT06WarpedNullCollarEquiv (source, radius) := by
  simpa [programPT06CanonicalFirstSheetPhysicalBulkMap,
    programPT06WarpedNullClosedHalfCollarEmbedding,
    programPT06WarpedNullClosedHalfCollarCoordinate,
    Set.projIcc_of_mem zero_le_one hRadius] using
    (programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
      period hPeriod pole source (⟨radius, hRadius⟩ : CutCollarInterval)
      hSource)

/-- Pushforward of the regional coordinate bulk measure through the genuine
finite-collar parametrization. -/
def programPT06CanonicalFirstSheetPhysicalBulkMeasure
    (pole : StandardEquatorialTwoSphere) :
    Measure (ProgramPT06EffectiveBulk period hPeriod) :=
  Measure.map
    (programPT06CanonicalFirstSheetPhysicalBulkMap period hPeriod pole)
    (programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period)

/-- The collar integrand expressed through the inverse adapted coordinate,
extended by zero off the coordinate source.  On the canonical collar it is
Gate 1069's physical densitized divergence. -/
def programPT06CanonicalFirstSheetPhysicalBulkIntegrand
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06EffectiveBulk period hPeriod → Real := by
  classical
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  exact chart.source.piecewise
    (fun point =>
      programPT06WarpedNullScreenWeightedDensity density
        (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
    (fun _ => (0 : Real))

theorem programPT06CanonicalFirstSheetPhysicalBulkIntegrand_measurable
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : Continuous density) :
    Measurable
      (programPT06CanonicalFirstSheetPhysicalBulkIntegrand
        period hPeriod pole density) := by
  classical
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  have hSourceCoordinate : ContinuousOn
      (fun point : ProgramPT06EffectiveBulk period hPeriod =>
        (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
      chart.source :=
    continuous_fst.comp_continuousOn
      (programPT06WarpedNullCollarEquiv.symm.continuous.comp_continuousOn
        chart.contMDiffOn_toFun.continuousOn)
  have hWeighted : Continuous
      (programPT06WarpedNullScreenWeightedDensity density) := by
    unfold programPT06WarpedNullScreenWeightedDensity
    exact (Real.continuous_exp.comp continuous_fst).mul hDensity
  have hOn : ContinuousOn
      (fun point : ProgramPT06EffectiveBulk period hPeriod =>
        programPT06WarpedNullScreenWeightedDensity density
          (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
      chart.source := by
    exact hWeighted.comp_continuousOn hSourceCoordinate
  have hZero : ContinuousOn
      (fun _ : ProgramPT06EffectiveBulk period hPeriod => (0 : Real))
      chart.sourceᶜ :=
    continuous_const.continuousOn
  simpa [programPT06CanonicalFirstSheetPhysicalBulkIntegrand, chart] using
    hOn.measurable_piecewise hZero chart.open_source.measurableSet

theorem programPT06CanonicalFirstSheetPhysicalBulkIntegrand_apply
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3)
    (radius : Real)
    (hDensity : DifferentiableAt Real density source)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period)
    (hRadius : radius ∈ Set.Icc (0 : Real) 1) :
    programPT06CanonicalFirstSheetPhysicalBulkIntegrand
        period hPeriod pole density
        (programPT06CanonicalFirstSheetPhysicalBulkMap
          period hPeriod pole (source, radius)) =
      programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
        period hPeriod pole metric density source radius := by
  classical
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  have hMem := programPT06CanonicalFirstSheetPhysicalBulkMap_mem_chart
    period hPeriod pole source radius hSource hRadius
  rw [programPT06CanonicalFirstSheetPhysicalBulkIntegrand]
  simp only [Set.piecewise, hMem, if_true]
  rw [programPT06CanonicalFirstSheetPhysicalBulkMap_coordinate
    period hPeriod pole source radius hSource hRadius,
    programPT06WarpedNullCollarEquiv.symm_apply_apply]
  symm
  rw [programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence_eq_warped
    period hPeriod pole metric density source radius hSource hRadius,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar,
    programPT06WarpedNullCollarAffineFluxExtension_metricDivergence
      radius hDensity]
  rfl

theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.physicalMetric_joint_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Integrable
      (fun parameter : ProgramPT06NullFaceSource3 × Real =>
        programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
          period hPeriod pole metric density parameter.1 parameter.2)
      (programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period) := by
  have hWeighted : Integrable
      (programPT06WarpedNullScreenWeightedDensity density)
      (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) :=
    contract.screenWeighted_integrable.mono_measure Measure.restrict_le_self
  have hProduct : Integrable
      (fun parameter : ProgramPT06NullFaceSource3 × Real =>
        programPT06WarpedNullScreenWeightedDensity density parameter.1)
      (programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period) := by
    exact hWeighted.comp_fst programPT06CanonicalFirstSheetUnitNormalMeasure
  apply hProduct.congr
  rw [programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure,
    programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure,
    programPT06WarpedNullCoordinateSourceMeasure,
    programPT06CanonicalFirstSheetUnitNormalMeasure,
    Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    ((programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen period).measurableSet.prod
      measurableSet_Ioc)] with parameter hParameter
  symm
  rw [programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence_eq_warped
    period hPeriod pole metric density parameter.1 parameter.2 hParameter.1
      ⟨hParameter.2.1.le, hParameter.2.2⟩,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar,
    programPT06WarpedNullCollarAffineFluxExtension_metricDivergence
      parameter.2 (contract.differentiable parameter.1)]
  rfl

/-- Fubini identifies the four-dimensional coordinate integral with Gate
1069's regional iterated bulk integral. -/
theorem programPT06CanonicalFirstSheetCoordinateBulkIntegral_eq_iterated
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ parameter,
        programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
          period hPeriod pole metric density parameter.1 parameter.2
      ∂programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period) =
      ∫ source,
        programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density source
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period := by
  have hIntegrable :=
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.physicalMetric_joint_integrable
      period hPeriod contract pole metric
  rw [programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure] at hIntegrable ⊢
  calc
    (∫ parameter,
        programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
          period hPeriod pole metric density parameter.1 parameter.2
      ∂(programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period).prod
        programPT06CanonicalFirstSheetUnitNormalMeasure) =
      ∫ source, (∫ radius,
        programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
          period hPeriod pole metric density source radius
        ∂programPT06CanonicalFirstSheetUnitNormalMeasure)
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period := by
          simpa [Function.uncurry] using (integral_integral hIntegrable).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with source
      change (∫ radius,
          programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
            period hPeriod pole metric density source radius
          ∂programPT06CanonicalFirstSheetUnitNormalMeasure) =
        ∫ radius in (0 : Real)..1,
          programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
            period hPeriod pole metric density source radius
      rw [programPT06CanonicalFirstSheetUnitNormalMeasure,
        intervalIntegral.integral_of_le zero_le_one]

/-- Integration of the transported physical integrand over the physical bulk
image measure is exactly the regional coordinate bulk integral. -/
theorem programPT06CanonicalFirstSheetPhysicalBulkIntegral_eq_coordinate
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ point,
        programPT06CanonicalFirstSheetPhysicalBulkIntegrand
          period hPeriod pole density point
      ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
        period hPeriod pole) =
      ∫ source,
        programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density source
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period := by
  have hDensity : Continuous density :=
    (show Differentiable Real density from
      fun source => contract.differentiable source).continuous
  rw [programPT06CanonicalFirstSheetPhysicalBulkMeasure,
    integral_map_of_stronglyMeasurable
      (programPT06CanonicalFirstSheetPhysicalBulkMap_continuous
        period hPeriod pole).measurable
      (programPT06CanonicalFirstSheetPhysicalBulkIntegrand_measurable
        period hPeriod pole density hDensity).stronglyMeasurable]
  calc
    (∫ parameter,
        programPT06CanonicalFirstSheetPhysicalBulkIntegrand
          period hPeriod pole density
          (programPT06CanonicalFirstSheetPhysicalBulkMap
            period hPeriod pole parameter)
      ∂programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period) =
      ∫ parameter,
        programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
          period hPeriod pole metric density parameter.1 parameter.2
        ∂programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure period := by
      apply integral_congr_ae
      rw [programPT06CanonicalFirstSheetRegionalCoordinateBulkMeasure,
        programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure,
        programPT06WarpedNullCoordinateSourceMeasure,
        programPT06CanonicalFirstSheetUnitNormalMeasure,
        Measure.prod_restrict]
      filter_upwards [ae_restrict_mem
        ((programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen period).measurableSet.prod
          measurableSet_Ioc)] with parameter hParameter
      exact programPT06CanonicalFirstSheetPhysicalBulkIntegrand_apply
        period hPeriod pole metric density parameter.1 parameter.2
          (contract.differentiable parameter.1) hParameter.1
          ⟨hParameter.2.1.le, hParameter.2.2⟩
    _ = _ := programPT06CanonicalFirstSheetCoordinateBulkIntegral_eq_iterated
      period hPeriod contract pole metric

/-- Fully transported regional Stokes identity between the physical bulk and
boundary image measures. -/
theorem programPT06CanonicalFirstSheetPhysicalImageMeasure_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ point,
        programPT06CanonicalFirstSheetPhysicalBulkIntegrand
          period hPeriod pole density point
      ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
        period hPeriod pole) =
      ∫ point,
        programPT06CanonicalFirstSheetPhysicalBoundaryFlux
          period hPeriod pole density point
        ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
          period hPeriod pole := by
  rw [programPT06CanonicalFirstSheetPhysicalBulkIntegral_eq_coordinate
    period hPeriod contract pole metric]
  exact programPT06CanonicalFirstSheetRegionalPhysicalMetric_image_stokes
    period hPeriod contract pole metric

end
end P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBulkMeasureTransport4D
end JanusFormal
