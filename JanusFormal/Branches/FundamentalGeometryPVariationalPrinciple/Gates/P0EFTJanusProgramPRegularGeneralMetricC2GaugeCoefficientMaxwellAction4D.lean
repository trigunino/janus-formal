import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D

/-! # Maxwell action from completed gauge coefficients -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev GaugeC2Core :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev C0Matrix :=
  Fin 4 → Fin 4 → C0Scalar period hPeriod

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

/-- Pointwise continuous Maxwell contraction. -/
def c0MaxwellMatrixContraction
    (inverseMetric first second : C0Matrix period hPeriod) :
    C0Scalar period hPeriod :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    inverseMetric μ ρ * inverseMetric ν σ * first μ ν * second ρ σ

/-- Maxwell pairing from a metric core and a fixed-frame gauge packet. -/
def regularGeneralMetricC0GaugeCoefficientMaxwellPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    C0Scalar period hPeriod :=
  ∑ component : Fin 2,
    c0MaxwellMatrixContraction period hPeriod
      (fun row column =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          variation row column)
      (regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod
        metric coefficients component)
      (regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod
        metric coefficients component)

/-- The natural joint domain only constrains the metric variable. -/
def regularGeneralMetricC2GaugeCoefficientMaxwellDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2Core period hPeriod metric ×
      GaugeC2Core period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod metric ×ˢ Set.univ

/-- The completed Maxwell pairing is jointly C² in metric and gauge data. -/
theorem regularGeneralMetricC0GaugeCoefficientMaxwellPairing_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (fun input =>
        regularGeneralMetricC0GaugeCoefficientMaxwellPairing period hPeriod
          metric input.1 input.2)
      (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
        metric) := by
  unfold regularGeneralMetricC0GaugeCoefficientMaxwellPairing
    c0MaxwellMatrixContraction
  apply ContDiffOn.sum
  intro component _
  apply ContDiffOn.sum
  intro μ _
  apply ContDiffOn.sum
  intro ν _
  apply ContDiffOn.sum
  intro ρ _
  apply ContDiffOn.sum
  intro σ _
  have hInverse (row column : Fin 4) : ContDiffOn Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          input.1 row column)
      (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
        metric) := by
    exact (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn
        period hPeriod metric row column).of_le
          (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
            exact WithTop.coe_le_coe.mpr le_top)
      |>.comp
        ((ContinuousLinearMap.fst Real
          (RegularGeneralMetricC2Core period hPeriod metric)
          (GaugeC2Core period hPeriod)).contDiff.contDiffOn.of_le
            (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
              exact WithTop.coe_le_coe.mpr le_top))
        (fun _ hInput => hInput.1)
  have hCurvature (first second : Fin 4) : ContDiffOn Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod =>
        regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
          input.2 component first second)
      (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
        metric) := by
    exact ((regularFrameGaugeCurvatureC0FromC2Coefficients_contDiff
        period hPeriod metric component first second).comp
          (ContinuousLinearMap.snd Real
            (RegularGeneralMetricC2Core period hPeriod metric)
            (GaugeC2Core period hPeriod)).contDiff).of_le
              (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
                exact WithTop.coe_le_coe.mpr le_top)
      |>.contDiffOn
  exact (((hInverse μ ρ).mul (hInverse ν σ)).mul
    (hCurvature μ ν)).mul (hCurvature ρ σ)

/-- Smooth frame coefficients recover the pre-existing Maxwell pairing. -/
theorem regularGeneralMetricC0GaugeCoefficientMaxwellPairing_frameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0GaugeCoefficientMaxwellPairing period hPeriod metric
        variation
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) =
      regularGeneralMetricC0MaxwellPairing period hPeriod metric potential
        potential variation := by
  apply ContinuousMap.ext
  intro point
  unfold regularGeneralMetricC0GaugeCoefficientMaxwellPairing
    c0MaxwellMatrixContraction regularGeneralMetricC0MaxwellPairing
    regularGeneralMetricC2MaxwellPairing c2MaxwellMatrixContraction
  simp only [map_sum, ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro σ _
  unfold regularFrameGaugeCurvatureC0MatrixFromC2Coefficients
  rw [regularFrameGaugeCurvatureC0FromC2Coefficients_smooth,
    regularFrameGaugeCurvatureC0FromC2Coefficients_smooth]
  simp only [regularFrameGaugePotentialFromCoefficients_frameCoefficients,
    regularFrameGaugeCurvatureC2Matrix_apply]
  rfl

/-- Fixed-volume density from completed gauge coefficients. -/
def regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume *
    ((-(1 / 4 : Real)) •
      regularGeneralMetricC0GaugeCoefficientMaxwellPairing period hPeriod
        metric variation coefficients)

/-- Integrated fixed-volume action from completed gauge coefficients. -/
def regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) : Real :=
  regularGeneralMetricC0IntegralCLM period hPeriod measure
    (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
      period hPeriod metric variation coefficients)

/-- The coefficient action is jointly C². -/
theorem regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
      (fun input =>
        regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure input.1 input.2)
      (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
        metric) := by
  have hIntegral : ContDiff Real 2
      (regularGeneralMetricC0IntegralCLM period hPeriod measure) :=
    (regularGeneralMetricC0IntegralCLM period hPeriod measure).contDiff.of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
        exact WithTop.coe_le_coe.mpr le_top)
  exact hIntegral.contDiffOn.comp
    (contDiffOn_const.mul
      ((regularGeneralMetricC0GaugeCoefficientMaxwellPairing_contDiffOn_two
        period hPeriod metric).const_smul _))
    (fun _ _ => Set.mem_univ _)

/-- On smooth coefficients, the new action is exactly the established one. -/
theorem regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_frameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure variation
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) =
      regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric
        measure potential potential variation := by
  unfold regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
    regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
    regularGeneralMetricC0FixedVolumeMaxwellAction
    regularGeneralMetricC0FixedVolumeMaxwellDensity
  rw [regularGeneralMetricC0GaugeCoefficientMaxwellPairing_frameCoefficients]

/-- Metric/gauge inputs on which the moving-frame root transport is C². -/
def regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2Core period hPeriod metric ×
      GaugeC2Core period hPeriod) :=
  regularGeneralMetricC2LorentzChartDomain period hPeriod metric ×ˢ Set.univ

/-- Fixed-volume action for coefficients supplied in the moving metric frame. -/
def regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2Matrix period hPeriod :=
  generalMetricRelativeC2CoreToMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric

/-- Root transport of a gauge packet supplied in the moving metric frame. -/
def regularGeneralMetricC2MobileGaugeCoefficientTransport
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    GaugeC2Core period hPeriod :=
  gaugeCoefficientC2CoreFrameTransport period hPeriod
    (c2IdentityRootBranch period hPeriod
      (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod
        metric variation)) coefficients

/-- The moving-frame gauge transport is jointly C² on the Lorentz chart. -/
theorem regularGeneralMetricC2MobileGaugeCoefficientTransport_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (fun input => regularGeneralMetricC2MobileGaugeCoefficientTransport
        period hPeriod metric input.1 input.2)
      (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
        period hPeriod metric) := by
  let domain := regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
    period hPeriod metric
  have hMatrix : ContDiffOn Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod =>
        regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod
          metric input.1) domain :=
    (((regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod
      metric).comp (ContinuousLinearMap.fst Real
        (RegularGeneralMetricC2Core period hPeriod metric)
        (GaugeC2Core period hPeriod))).contDiff.of_le
          (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
            exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hRoot : ContDiffOn Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod =>
        c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod
            metric input.1)) domain :=
    (c2IdentityRootBranch_contDiffOn period hPeriod).comp hMatrix
      (fun input hInput => by
        change input.1.1 ∈ c2IdentityRootPerturbationDomain period hPeriod
        exact (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
          period hPeriod metric hInput.1).1)
  have hGauge : ContDiffOn Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod => input.2) domain :=
    contDiff_snd.contDiffOn
  have hTransport : ContDiff Real 2
      (fun input : C2Matrix period hPeriod × GaugeC2Core period hPeriod =>
        gaugeCoefficientC2CoreFrameTransport period hPeriod input.1
          input.2) :=
    (gaugeCoefficientC2CoreFrameTransport_contDiff period hPeriod).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
        exact WithTop.coe_le_coe.mpr le_top)
  exact hTransport.contDiffOn.comp (hRoot.prodMk hGauge)
    (fun _ _ => Set.mem_univ _)

/-- Package the metric core with its transported fixed-frame gauge packet. -/
def regularGeneralMetricC2MobileGaugeCoefficientInputMap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (input : RegularGeneralMetricC2Core period hPeriod metric ×
      GaugeC2Core period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric ×
      GaugeC2Core period hPeriod :=
  (input.1, regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod
    metric input.1 input.2)

theorem regularGeneralMetricC2MobileGaugeCoefficientInputMap_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2MobileGaugeCoefficientInputMap period hPeriod
        metric)
      (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
        period hPeriod metric) :=
  contDiff_fst.contDiffOn.prodMk
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_contDiffOn_two
      period hPeriod metric)

theorem regularGeneralMetricC2MobileGaugeCoefficientInputMap_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {input : RegularGeneralMetricC2Core period hPeriod metric ×
      GaugeC2Core period hPeriod}
    (hInput : input ∈ regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
      period hPeriod metric) :
    regularGeneralMetricC2MobileGaugeCoefficientInputMap period hPeriod metric
        input ∈
      regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
        metric :=
  ⟨hInput.1.1, Set.mem_univ _⟩

/-- Fixed-volume action for coefficients supplied in the moving metric frame. -/
def regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) : Real :=
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod metric measure variation
      (regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod
        metric variation coefficients)

/-- The moving-frame coefficient action is jointly C² on the Lorentz chart. -/
theorem regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
      (fun input =>
        regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure input.1 input.2)
      (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
        period hPeriod metric) := by
  have h :=
    (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod metric measure).comp
        (regularGeneralMetricC2MobileGaugeCoefficientInputMap_contDiffOn_two
          period hPeriod metric)
        (fun _ hInput =>
          regularGeneralMetricC2MobileGaugeCoefficientInputMap_mem
            period hPeriod metric hInput)
  exact h.congr (fun _ _ => rfl)

/-- Exact intrinsic Maxwell action for genuine moving-frame coefficients. -/
theorem regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure
        (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              metric tensor hLorentz) potential)) =
      intrinsicMaxwellAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          tensor hLorentz)
        (globalSmoothMaxwellPairing period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            tensor hLorentz).metric potential potential) measure := by
  unfold regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
  change regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure
        (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor)
        (gaugeCoefficientC2CoreFrameTransport period hPeriod
          (c2IdentityRootBranch period hPeriod
            (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor))
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
                metric tensor hLorentz) potential))) = _
  rw [gaugeCoefficientC2CoreFrameTransport_lorentzChart period hPeriod metric
    tensor hLorentz potential]
  rw [regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_frameCoefficients]
  exact regularGeneralMetricC0FixedVolumeMaxwellAction_smooth period hPeriod
    metric tensor hLorentz measure potential potential

/-- Gate marker for the exact jointly C² coefficient Maxwell action. -/
theorem regular_general_metric_c2_gauge_coefficient_maxwell_action_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
        (fun input =>
          regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure input.1 input.2)
        (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod
          metric) ∧
      regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod metric potential)) =
        regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric
          measure potential potential variation := by
  exact ⟨regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod metric measure,
    regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_frameCoefficients
      period hPeriod metric measure variation potential⟩

/-- Gate marker including the true moving-frame chart input. -/
theorem regular_general_metric_c2_mobile_gauge_coefficient_maxwell_action_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
        (fun input =>
          regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure input.1 input.2)
        (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain
          period hPeriod metric) ∧
      regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor)
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
                metric tensor hLorentz) potential)) =
        intrinsicMaxwellAction period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            tensor hLorentz)
          (globalSmoothMaxwellPairing period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
              tensor hLorentz).metric potential potential) measure := by
  exact ⟨regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod metric measure,
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_smooth
      period hPeriod metric tensor hLorentz measure potential⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
end JanusFormal
