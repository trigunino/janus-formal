import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

/-!
# Canonical spacetime PT measure and BV covariance

The round-sphere reflection and fundamental-domain time reversal preserve the
canonical quotient measure.  This closes PT covariance of the smooth
ultralocal spacetime BV master model without adding a measure contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

noncomputable section

open MeasureTheory Set
open scoped Pointwise Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev ambientReflection :=
  P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection

def spherePT (point : StandardSphere) : StandardSphere :=
  ⟨ambientReflection point.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [LinearIsometryEquiv.norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using point.2⟩

@[simp] theorem spherePT_coe (point : StandardSphere) :
    (spherePT point : EuclideanR4) = ambientReflection point.1 := rfl

@[simp] theorem spherePT_involutive (point : StandardSphere) :
    spherePT (spherePT point) = point := by
  apply Subtype.ext
  exact P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_involutive point.1

theorem spherePT_continuous : Continuous spherePT := by
  exact (ambientReflection.continuous.comp continuous_subtype_val).subtype_mk _

theorem spherePT_eq_standardSphereReflection (point : StandardSphere) :
    spherePT point = standardSphereReflection point := by
  apply Subtype.ext
  ext index
  simp [spherePT, standardSphereReflection,
    P0EFTJanusMappingTorusSmoothQuotient.euclideanReflection,
    ambientReflection,
    P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_apply,
    P0EFTJanusReflectionFixedThroat.reflectPoint]

theorem spherePT_cone_preimage (s : Set StandardSphere) :
    ambientReflection ⁻¹' (Ioo (0 : Real) 1 •
      ((fun point : StandardSphere => (point : EuclideanR4)) '' s)) =
      Ioo (0 : Real) 1 •
        ((fun point : StandardSphere => (point : EuclideanR4)) ''
          (spherePT ⁻¹' s)) := by
  ext point
  constructor
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, hPoint⟩
    refine ⟨scalar, hScalar, ambientReflection direction.1, ?_, ?_⟩
    · refine ⟨spherePT direction, ?_, rfl⟩
      simpa using hDirection
    · have hReflected := congrArg ambientReflection hPoint
      simpa using hReflected
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
    refine ⟨scalar, hScalar, (spherePT direction : EuclideanR4), ?_, ?_⟩
    · exact ⟨spherePT direction, hDirection, rfl⟩
    · simp

theorem measurableSet_sphere_cone {s : Set StandardSphere}
    (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : Real) 1 •
      ((fun point : StandardSphere => (point : EuclideanR4)) '' s)) := by
  let radialUpper : Set (Ioi (0 : Real)) :=
    Iio ⟨1, mem_Ioi.2 one_pos⟩
  have hCone :
      Ioo (0 : Real) 1 •
          ((fun point : StandardSphere => (point : EuclideanR4)) '' s) =
        (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR4).symm) ''
          (s ×ˢ radialUpper) := by
    ext point
    constructor
    · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
      refine ⟨(direction, ⟨scalar, hScalar.1⟩), ?_, ?_⟩
      · exact ⟨hDirection, hScalar.2⟩
      · simp [Function.comp_apply]
    · rintro ⟨⟨direction, scalar⟩, ⟨hDirection, hScalar⟩, rfl⟩
      refine ⟨scalar.1, ⟨scalar.2, hScalar⟩, direction.1, ?_, ?_⟩
      · exact ⟨direction, hDirection, rfl⟩
      · simp [Function.comp_apply]
  rw [hCone]
  have hEmbedding : MeasurableEmbedding
      (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR4).symm) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : EuclideanR4)).compl).comp
        (homeomorphUnitSphereProd EuclideanR4).symm.measurableEmbedding
  exact hEmbedding.measurableSet_image.mpr (hs.prod measurableSet_Iio)

theorem spherePT_measurePreserving :
    MeasurePreserving spherePT
      (volume : Measure EuclideanR4).toSphere
      (volume : Measure EuclideanR4).toSphere := by
  refine ⟨spherePT_continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply spherePT_continuous.measurable hs]
  rw [(volume : Measure EuclideanR4).toSphere_apply' hs,
    (volume : Measure EuclideanR4).toSphere_apply'
      (spherePT_continuous.measurable hs)]
  rw [← spherePT_cone_preimage]
  have hAmbient := LinearIsometryEquiv.measurePreserving ambientReflection
  rw [← Measure.map_apply hAmbient.measurable
    (measurableSet_sphere_cone hs)]
  rw [hAmbient.map_eq]

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

abbrev SpacetimeBase := StandardSphere × Real

def spacetimeBaseMeasure : Measure SpacetimeBase :=
  ((volume : Measure EuclideanR4).toSphere).prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

def spacetimeBasePT (base : SpacetimeBase) : SpacetimeBase :=
  (spherePT base.1, period - base.2)

theorem spacetimeBasePT_measurePreserving (hPeriod : period ≠ 0) :
    MeasurePreserving (spacetimeBasePT period)
      (spacetimeBaseMeasure period) (spacetimeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map spherePT (fun time : Real => period - time))
    (((volume : Measure EuclideanR4).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    (((volume : Measure EuclideanR4).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact spherePT_measurePreserving.prod
    (canonicalLatitudeTimeReflection_measurePreserving period hPeriod)

def spacetimeFundamentalDomainMap (base : SpacetimeBase) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm base.1, base.2))

theorem spacetimeFundamentalDomainMap_continuous :
    Continuous (spacetimeFundamentalDomainMap period hPeriod) := by
  have hProduct : Continuous
      (fun base : SpacetimeBase =>
        (unitThreeSphereHomeomorph.symm base.1, base.2)) :=
    (unitThreeSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (sphereData period hPeriod)).symm.continuous.comp hProduct)

theorem intrinsicCanonicalLorentzVolumeMeasure_eq_spacetimeBase :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      (spacetimeBaseMeasure period).map
        (spacetimeFundamentalDomainMap period hPeriod) := by
  rfl

theorem unitSphere_conjugacy (point : StandardSphere) :
    unitThreeSphereHomeomorph.symm (spherePT point) =
      sphereReflection (unitThreeSphereHomeomorph.symm point) := by
  rw [spherePT_eq_standardSphereReflection]
  simpa using standardSphereReflection_conjugates_actual
    (unitThreeSphereHomeomorph.symm point)

theorem reflectedSpherePT_fundamentalDomainMap (base : SpacetimeBase) :
    reflectedSpherePT period hPeriod
        (spacetimeFundamentalDomainMap period hPeriod base) =
      spacetimeFundamentalDomainMap period hPeriod
        (spacetimeBasePT period base) := by
  unfold reflectedSpherePT spacetimeFundamentalDomainMap spacetimeBasePT
  rw [mappingTorusTimeReversal_mk,
    mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨-1, ?_⟩
  apply MappingTorusCover.ext
  · rw [vadd_fiber]
    rw [unitSphere_conjugacy]
    simp [reflectedSphereData]
  · rw [vadd_time]
    change (period - base.2) + ((-1 : Int) : Real) * period = -base.2
    norm_num
    ring

def reflectedSpherePTMeasurableEquiv :
    EffectiveQuotient period hPeriod ≃ᵐ EffectiveQuotient period hPeriod where
  toEquiv :=
    { toFun := reflectedSpherePT period hPeriod
      invFun := reflectedSpherePT period hPeriod
      left_inv := reflectedSpherePT_involutive period hPeriod
      right_inv := reflectedSpherePT_involutive period hPeriod }
  measurable_toFun := (continuous_reflectedSpherePT period hPeriod).measurable
  measurable_invFun := (continuous_reflectedSpherePT period hPeriod).measurable

theorem intrinsicCanonicalLorentzVolumeMeasure_pt_measurePreserving :
    MeasurePreserving (reflectedSpherePTMeasurableEquiv period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_spacetimeBase]
  apply MeasurePreserving.of_semiconj
    ((spacetimeFundamentalDomainMap_continuous period hPeriod).measurable.measurePreserving
      (spacetimeBaseMeasure period))
    (spacetimeBasePT_measurePreserving period hPeriod)
  · intro base
    exact (reflectedSpherePT_fundamentalDomainMap period hPeriod base).symm
  · exact (reflectedSpherePTMeasurableEquiv period hPeriod).measurable

theorem intrinsicCanonicalLorentzVolumeMeasure_integral_pt
    (integrand : EffectiveQuotient period hPeriod → Real) :
    (∫ point, integrand (reflectedSpherePT period hPeriod point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, integrand point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (intrinsicCanonicalLorentzVolumeMeasure_pt_measurePreserving
    period hPeriod).integral_comp' integrand

private def finiteMetricBVPTExchangeContinuous :
    FiniteMetricBVPhase →L[Real] FiniteMetricBVPhase :=
  LinearMap.toContinuousLinearMap finiteMetricBVPTExchange

def smoothSpacetimeBVPT
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    SmoothFiniteMetricBVSpacetimeField period hPeriod where
  toFun point := finiteMetricBVPTExchange
    (field (reflectedSpherePT period hPeriod point))
  contMDiff_toFun :=
    finiteMetricBVPTExchangeContinuous.contDiff.contMDiff.comp
      (field.contMDiff_toFun.comp
        (reflectedSpherePT_contMDiff period hPeriod))

@[simp] theorem smoothSpacetimeBVPT_apply
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVPT period hPeriod field point =
      finiteMetricBVPTExchange
        (field (reflectedSpherePT period hPeriod point)) := rfl

theorem smoothSpacetimeBVPT_involutive
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    smoothSpacetimeBVPT period hPeriod
      (smoothSpacetimeBVPT period hPeriod field) = field := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  simp [smoothSpacetimeBVPT,
    finiteMetricBVPTExchange_involutive]

theorem smoothSpacetimeBVPT_commutes_BRST
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    smoothSpacetimeBVPT period hPeriod
        (smoothSpacetimeBVBRST period hPeriod field) =
      smoothSpacetimeBVBRST period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  exact finiteMetricBVPTExchange_commutes_BRST
    (field (reflectedSpherePT period hPeriod point))

theorem smoothSpacetimeBVMasterDensity_pt
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterDensity period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) point =
      smoothSpacetimeBVMasterDensity period hPeriod field
        (reflectedSpherePT period hPeriod point) := by
  rw [smoothSpacetimeBVMasterDensity_apply,
    smoothSpacetimeBVPT_apply,
    smoothSpacetimeBVMasterDensity_apply]
  exact finiteMetricBVMasterAction_ptExchange
    (field (reflectedSpherePT period hPeriod point))

theorem canonicalSmoothSpacetimeBVMasterAction_pt
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterAction period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) =
      canonicalSmoothSpacetimeBVMasterAction period hPeriod field := by
  unfold canonicalSmoothSpacetimeBVMasterAction
  calc
    (∫ point, smoothSpacetimeBVMasterDensity period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, smoothSpacetimeBVMasterDensity period hPeriod field
          (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothSpacetimeBVMasterDensity_pt period hPeriod field)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (smoothSpacetimeBVMasterDensity period hPeriod field)

theorem canonicalSmoothSpacetimeBVMasterSelfBracket_pt
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterSelfBracket period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) =
      canonicalSmoothSpacetimeBVMasterSelfBracket period hPeriod field := by
  rw [canonicalSmoothSpacetimeBV_integrated_classical_master_equation,
    canonicalSmoothSpacetimeBV_integrated_classical_master_equation]

theorem canonicalSmoothSpacetimeBV_integrated_CME_pt
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterSelfBracket period hPeriod
        (smoothSpacetimeBVPT period hPeriod field) = 0 :=
  canonicalSmoothSpacetimeBV_integrated_classical_master_equation
    period hPeriod (smoothSpacetimeBVPT period hPeriod field)

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D
end JanusFormal
