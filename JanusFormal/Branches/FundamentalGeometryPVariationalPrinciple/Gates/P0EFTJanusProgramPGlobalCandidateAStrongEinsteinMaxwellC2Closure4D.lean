import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Strong-field C² closure for Einstein--Maxwell densities

A strong `C⁰ ∩ H¹` scalar family has a continuous representative.  For every
finite measure, continuous inclusion into `L¹` followed by the Bochner
integral is therefore one continuous linear functional.  Consequently a
strong `C²` density family integrates to a `C²` action automatically.

The Einstein--Hilbert and Maxwell density constructors below use the existing
strong product.  Their continuous representatives are exactly the physical
pointwise densities.  No separate parameter--spacetime regularity or
domination axiom is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongEinsteinMaxwellC2Closure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 5000000

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

/-! ## Integration of strong scalar families -/

/-- Integration against any finite common measure, factored through the
continuous representative and the canonical `L¹` inclusion. -/
def canonicalPhysicalStrongScalarIntegralCLM
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    StrongScalar period hPeriod →L[Real] Real :=
  (L1.integralCLM
      (α := EffectiveQuotient period hPeriod)
      (E := Real)
      (μ := measure)).comp
    ((ContinuousMap.toLp (1 : ENNReal) measure Real).comp
      (canonicalPhysicalScalarStrongH1C0CoreToContinuous
        period hPeriod))

theorem canonicalPhysicalStrongScalarIntegralCLM_apply
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (field : StrongScalar period hPeriod) :
    canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure field =
      ∫ point,
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod field point ∂measure := by
  let continuousField :=
    canonicalPhysicalScalarStrongH1C0CoreToContinuous
      period hPeriod field
  let l1Field : Lp Real (1 : ENNReal) measure :=
    ContinuousMap.toLp (1 : ENNReal) measure Real continuousField
  change L1.integralCLM l1Field =
    ∫ point, continuousField point ∂measure
  calc
    L1.integralCLM l1Field = L1.integral l1Field :=
      (L1.integral_eq l1Field).symm
    _ = ∫ point, (l1Field : EffectiveQuotient period hPeriod → Real) point
          ∂measure :=
      L1.integral_eq_integral l1Field
    _ = ∫ point, continuousField point ∂measure := by
      exact integral_congr_ae
        (ContinuousMap.coeFn_toLp
          (p := (1 : ENNReal)) (μ := measure) (𝕜 := Real)
          continuousField)

/-- A strong `C²` density family integrates to a `C²` scalar action. -/
theorem canonicalPhysicalStrongScalarIntegral_comp_contDiff_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (density : Model → StrongScalar period hPeriod)
    (hDensity : ContDiff Real 2 density) :
    ContDiff Real 2
      (canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure ∘
        density) :=
  (canonicalPhysicalStrongScalarIntegralCLM
    period hPeriod measure).contDiff.comp hDensity

/-- Open-domain version used by the local variational chart. -/
theorem canonicalPhysicalStrongScalarIntegral_comp_contDiffOn_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (domain : Set Model)
    (density : Model → StrongScalar period hPeriod)
    (hDensity : ContDiffOn Real 2 density domain) :
    ContDiffOn Real 2
      (canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure ∘
        density) domain := by
  exact
    (canonicalPhysicalStrongScalarIntegralCLM
      period hPeriod measure).contDiff.contDiffOn.comp hDensity
        (fun _ _ => mem_univ _)

/-! ## Strong Einstein--Maxwell density constructors -/

def canonicalPhysicalStrongScalarConstant
    (value : Real) : StrongScalar period hPeriod :=
  smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
    (constantSmoothField period hPeriod Real value)

@[simp]
theorem canonicalPhysicalStrongScalarConstant_toContinuous_apply
    (value : Real) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (canonicalPhysicalStrongScalarConstant period hPeriod value) point =
      value :=
  rfl

/-- Strong form of `volume · (2κ)⁻¹ (R - 2Λ)`. -/
def strongEinsteinHilbertDensity
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : StrongScalar period hPeriod) :
    StrongScalar period hPeriod :=
  scalarStrongProduct period hPeriod volume
    ((1 / (2 * couplings.gravitationalCoupling)) •
      (scalarCurvature -
        canonicalPhysicalStrongScalarConstant period hPeriod
          (2 * couplings.cosmologicalConstant)))

theorem strongEinsteinHilbertDensity_toContinuous_apply
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : StrongScalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (strongEinsteinHilbertDensity period hPeriod couplings
          volume scalarCurvature) point =
      canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (canonicalPhysicalScalarStrongH1C0CoreToContinuous
              period hPeriod scalarCurvature point -
            2 * couplings.cosmologicalConstant)) := by
  rw [strongEinsteinHilbertDensity,
    scalarStrongProduct_toContinuous]
  rw [map_smul, map_sub]
  change
    canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (canonicalPhysicalScalarStrongH1C0CoreToContinuous
              period hPeriod scalarCurvature point -
            canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
              (canonicalPhysicalStrongScalarConstant period hPeriod
                (2 * couplings.cosmologicalConstant)) point)) = _
  rw [canonicalPhysicalStrongScalarConstant_toContinuous_apply]

/-- Strong form of `volume · (-1/4) F²`. -/
def strongMaxwellDensity
    (volume pairing : StrongScalar period hPeriod) :
    StrongScalar period hPeriod :=
  scalarStrongProduct period hPeriod volume
    ((-(1 / 4 : Real)) • pairing)

theorem strongMaxwellDensity_toContinuous_apply
    (volume pairing : StrongScalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (strongMaxwellDensity period hPeriod volume pairing) point =
      canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod volume point *
        (-(1 / 4 : Real) *
          canonicalPhysicalScalarStrongH1C0CoreToContinuous
            period hPeriod pairing point) := by
  rw [strongMaxwellDensity, scalarStrongProduct_toContinuous]
  rw [map_smul]
  rfl

theorem strongEinsteinHilbertDensity_contDiff_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : Model → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hScalarCurvature : ContDiff Real 2 scalarCurvature) :
    ContDiff Real 2
      (fun parameter =>
        strongEinsteinHilbertDensity period hPeriod couplings
          (volume parameter) (scalarCurvature parameter)) := by
  have hSecond : ContDiff Real 2
      (fun parameter =>
        (1 / (2 * couplings.gravitationalCoupling)) •
          (scalarCurvature parameter -
            canonicalPhysicalStrongScalarConstant period hPeriod
              (2 * couplings.cosmologicalConstant))) :=
    (hScalarCurvature.sub contDiff_const).const_smul _
  exact
    ((scalarStrongProduct period hPeriod).contDiff.comp hVolume).clm_apply
      hSecond

theorem strongMaxwellDensity_contDiff_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (volume pairing : Model → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hPairing : ContDiff Real 2 pairing) :
    ContDiff Real 2
      (fun parameter =>
        strongMaxwellDensity period hPeriod
          (volume parameter) (pairing parameter)) := by
  exact
    ((scalarStrongProduct period hPeriod).contDiff.comp hVolume).clm_apply
      (hPairing.const_smul (-(1 / 4 : Real)))

theorem strongEinsteinHilbertDensity_contDiffOn_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (domain : Set Model)
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : Model → StrongScalar period hPeriod)
    (hVolume : ContDiffOn Real 2 volume domain)
    (hScalarCurvature : ContDiffOn Real 2 scalarCurvature domain) :
    ContDiffOn Real 2
      (fun parameter =>
        strongEinsteinHilbertDensity period hPeriod couplings
          (volume parameter) (scalarCurvature parameter)) domain := by
  have hFirst : ContDiffOn Real 2
      (fun parameter =>
        scalarStrongProduct period hPeriod (volume parameter)) domain :=
    (scalarStrongProduct period hPeriod).contDiff.contDiffOn.comp hVolume
      (fun _ _ => mem_univ _)
  have hSecond : ContDiffOn Real 2
      (fun parameter =>
        (1 / (2 * couplings.gravitationalCoupling)) •
          (scalarCurvature parameter -
            canonicalPhysicalStrongScalarConstant period hPeriod
              (2 * couplings.cosmologicalConstant))) domain :=
    (hScalarCurvature.sub contDiffOn_const).const_smul _
  exact hFirst.clm_apply hSecond

theorem strongMaxwellDensity_contDiffOn_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (domain : Set Model)
    (volume pairing : Model → StrongScalar period hPeriod)
    (hVolume : ContDiffOn Real 2 volume domain)
    (hPairing : ContDiffOn Real 2 pairing domain) :
    ContDiffOn Real 2
      (fun parameter =>
        strongMaxwellDensity period hPeriod
          (volume parameter) (pairing parameter)) domain := by
  have hFirst : ContDiffOn Real 2
      (fun parameter =>
        scalarStrongProduct period hPeriod (volume parameter)) domain :=
    (scalarStrongProduct period hPeriod).contDiff.contDiffOn.comp hVolume
      (fun _ _ => mem_univ _)
  exact hFirst.clm_apply
    (hPairing.const_smul (-(1 / 4 : Real)))

/-- General finite-measure EH action closure from strong volume and scalar
curvature targets. -/
theorem strongEinsteinHilbertAction_contDiff_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : Model → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hScalarCurvature : ContDiff Real 2 scalarCurvature) :
    ContDiff Real 2
      (fun parameter =>
        canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
          (strongEinsteinHilbertDensity period hPeriod couplings
            (volume parameter) (scalarCurvature parameter))) := by
  exact
    canonicalPhysicalStrongScalarIntegral_comp_contDiff_two
      period hPeriod measure _
      (strongEinsteinHilbertDensity_contDiff_two period hPeriod couplings
        volume scalarCurvature hVolume hScalarCurvature)

/-- General finite-measure Maxwell action closure from strong volume and
curvature-pairing targets. -/
theorem strongMaxwellAction_contDiff_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (volume pairing : Model → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hPairing : ContDiff Real 2 pairing) :
    ContDiff Real 2
      (fun parameter =>
        canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
          (strongMaxwellDensity period hPeriod
            (volume parameter) (pairing parameter))) := by
  exact
    canonicalPhysicalStrongScalarIntegral_comp_contDiff_two
      period hPeriod measure _
      (strongMaxwellDensity_contDiff_two period hPeriod
        volume pairing hVolume hPairing)

/-- Local-chart EH action closure on the admissible open domain. -/
theorem strongEinsteinHilbertAction_contDiffOn_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (domain : Set Model)
    (couplings : EinsteinHilbertCouplings)
    (volume scalarCurvature : Model → StrongScalar period hPeriod)
    (hVolume : ContDiffOn Real 2 volume domain)
    (hScalarCurvature : ContDiffOn Real 2 scalarCurvature domain) :
    ContDiffOn Real 2
      (fun parameter =>
        canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
          (strongEinsteinHilbertDensity period hPeriod couplings
            (volume parameter) (scalarCurvature parameter))) domain := by
  exact
    canonicalPhysicalStrongScalarIntegral_comp_contDiffOn_two
      period hPeriod measure domain _
      (strongEinsteinHilbertDensity_contDiffOn_two period hPeriod domain
        couplings volume scalarCurvature hVolume hScalarCurvature)

/-- Local-chart Maxwell action closure on the admissible open domain. -/
theorem strongMaxwellAction_contDiffOn_two
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (domain : Set Model)
    (volume pairing : Model → StrongScalar period hPeriod)
    (hVolume : ContDiffOn Real 2 volume domain)
    (hPairing : ContDiffOn Real 2 pairing domain) :
    ContDiffOn Real 2
      (fun parameter =>
        canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
          (strongMaxwellDensity period hPeriod
            (volume parameter) (pairing parameter))) domain := by
  exact
    canonicalPhysicalStrongScalarIntegral_comp_contDiffOn_two
      period hPeriod measure domain _
      (strongMaxwellDensity_contDiffOn_two period hPeriod domain
        volume pairing hVolume hPairing)

/-! ## Exact bridges to the pre-existing general-metric action lines -/

/-- The genuine arbitrary-metric EH action line is `C²` as soon as its actual
volume and scalar curvature admit `C²` lifts to the canonical strong core. -/
theorem intrinsicEinsteinHilbertMetricActionCurve_contDiff_two_of_strong
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (volume scalarCurvature : Real → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hScalarCurvature : ContDiff Real 2 scalarCurvature)
    (hVolume_eq : ∀ parameter,
      volume parameter =
        smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (line.data parameter).metric.volume)
    (hScalarCurvature_eq : ∀ parameter,
      scalarCurvature parameter =
        smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (line.data parameter).scalarCurvature) :
    ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings line
        measure) := by
  have hAction :
      intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings line
          measure =
        fun parameter =>
          canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
            (strongEinsteinHilbertDensity period hPeriod couplings
              (volume parameter) (scalarCurvature parameter)) := by
    funext parameter
    rw [canonicalPhysicalStrongScalarIntegralCLM_apply]
    unfold intrinsicEinsteinHilbertMetricActionCurve
      intrinsicEinsteinHilbertAction
    apply integral_congr_ae
    filter_upwards with point
    rw [strongEinsteinHilbertDensity_toContinuous_apply,
      hVolume_eq, hScalarCurvature_eq]
    rfl
  rw [hAction]
  exact strongEinsteinHilbertAction_contDiff_two period hPeriod measure
    couplings volume scalarCurvature hVolume hScalarCurvature

/-- The genuine varying-metric Maxwell action line is `C²` as soon as its
actual volume and curvature pairing admit `C²` strong lifts. -/
theorem intrinsicMaxwellMetricGaugeActionCurve_contDiff_two_of_strong
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (volume pairing : Real → StrongScalar period hPeriod)
    (hVolume : ContDiff Real 2 volume)
    (hPairing : ContDiff Real 2 pairing)
    (hVolume_eq : ∀ parameter,
      volume parameter =
        smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (gravity.data parameter).metric.volume)
    (hPairing_eq : ∀ parameter,
      pairing parameter =
        smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (line.pairing parameter)) :
    ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod gravity line
        measure) := by
  have hAction :
      intrinsicMaxwellMetricGaugeActionCurve period hPeriod gravity line
          measure =
        fun parameter =>
          canonicalPhysicalStrongScalarIntegralCLM period hPeriod measure
            (strongMaxwellDensity period hPeriod
              (volume parameter) (pairing parameter)) := by
    funext parameter
    rw [canonicalPhysicalStrongScalarIntegralCLM_apply]
    unfold intrinsicMaxwellMetricGaugeActionCurve intrinsicMaxwellAction
    apply integral_congr_ae
    filter_upwards with point
    rw [strongMaxwellDensity_toContinuous_apply,
      hVolume_eq, hPairing_eq]
    rfl
  rw [hAction]
  exact strongMaxwellAction_contDiff_two period hPeriod measure
    volume pairing hVolume hPairing

end
end P0EFTJanusProgramPGlobalCandidateAStrongEinsteinMaxwellC2Closure4D
end JanusFormal
