import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D

/-!
# General-metric C² Maxwell family

The true base inverse metric, the genuine `dA` curvature coefficients, the
relative inverse on the open metric chart, the selected volume root, and the
finite-measure integral are assembled into one local `C²` Maxwell family.
At the base point it is exactly the pre-existing chart-free Maxwell pairing.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The inverse of the varied metric in the genuine regular frame. -/
def regularGeneralMetricC2InverseMetricMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C2FiniteMatrix period hPeriod 4 :=
  c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    (generalMetricRelativeC2InverseMatrix period hPeriod
      (RegularFrame period hPeriod metric) metric.metric variation)
    (regularFrameMetricInverseC2Matrix period hPeriod metric)

theorem regularGeneralMetricC2InverseMetricMatrix_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  have hProduct : ContDiff Real ∞
      (fun matrix : C2FiniteMatrix period hPeriod 4 =>
        c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 matrix
          (regularFrameMetricInverseC2Matrix period hPeriod metric)) :=
    (c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).contDiff.clm_apply contDiff_const
  have hInverse : ContDiffOn Real ∞
      (generalMetricRelativeC2InverseMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
    apply (generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod
      (RegularFrame period hPeriod metric) metric.metric).mono
    intro variation hVariation
    exact hVariation.1
  exact hProduct.contDiffOn.comp hInverse (fun _ _ => mem_univ _)

theorem generalMetricRelativeC2InverseMatrix_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    generalMetricRelativeC2InverseMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric 0 =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  have hInverse := c2FiniteMatrixProduct_inverse_right period hPeriod 4
    (c2FiniteMatrixIdentity period hPeriod 4)
    (c2FiniteMatrixIdentity_mem_unitSet period hPeriod 4)
  change c2FiniteMatrixInverse period hPeriod 4
      (c2FiniteMatrixIdentity period hPeriod 4 + 0) = _
  rw [c2FiniteMatrixProduct_identity_left] at hInverse
  simpa using hInverse

theorem regularGeneralMetricC2InverseMetricMatrix_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2InverseMetricMatrix period hPeriod metric 0 =
      regularFrameMetricInverseC2Matrix period hPeriod metric := by
  rw [regularGeneralMetricC2InverseMetricMatrix,
    generalMetricRelativeC2InverseMatrix_zero,
    c2FiniteMatrixProduct_identity_left]

/-- C² algebraic contraction of two covariant two-tensor matrices. -/
def c2MaxwellMatrixContraction
    (inverseMetric first second : C2FiniteMatrix period hPeriod 4) :
    C2Scalar period hPeriod :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (inverseMetric μ ρ) (inverseMetric ν σ))
        (first μ ν))
      (second ρ σ)

private theorem c2FiniteMatrixEntry_contDiff (row column : Fin 4) :
    ContDiff Real ∞
      (fun matrix : C2FiniteMatrix period hPeriod 4 => matrix row column) :=
  (contDiff_apply Real (C2Scalar period hPeriod) column).comp
    (contDiff_apply Real (Fin 4 → C2Scalar period hPeriod) row)

theorem c2MaxwellMatrixContraction_contDiff
    (first second : C2FiniteMatrix period hPeriod 4) :
    ContDiff Real ∞
      (fun inverseMetric =>
        c2MaxwellMatrixContraction period hPeriod inverseMetric first second) := by
  apply ContDiff.sum
  intro μ _
  apply ContDiff.sum
  intro ν _
  apply ContDiff.sum
  intro ρ _
  apply ContDiff.sum
  intro σ _
  have hInverseProduct : ContDiff Real ∞
      (fun inverseMetric : C2FiniteMatrix period hPeriod 4 =>
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (inverseMetric μ ρ) (inverseMetric ν σ)) := by
    have hOperator : ContDiff Real ∞
        (fun inverseMetric : C2FiniteMatrix period hPeriod 4 =>
          canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (inverseMetric μ ρ)) :=
      (canonicalPhysicalScalarC2JetCoreProduct
        period hPeriod).contDiff.comp
          (c2FiniteMatrixEntry_contDiff period hPeriod μ ρ)
    exact hOperator.clm_apply
      (c2FiniteMatrixEntry_contDiff period hPeriod ν σ)
  have hFirstConstant : ContDiff Real ∞
      (fun _ : C2FiniteMatrix period hPeriod 4 => first μ ν) :=
    contDiff_const
  have hFirstProduct : ContDiff Real ∞
      (fun inverseMetric : C2FiniteMatrix period hPeriod 4 =>
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (inverseMetric μ ρ) (inverseMetric ν σ))
          (first μ ν)) := by
    have hOperator : ContDiff Real ∞
        (fun inverseMetric : C2FiniteMatrix period hPeriod 4 =>
          canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
              (inverseMetric μ ρ) (inverseMetric ν σ))) :=
      (canonicalPhysicalScalarC2JetCoreProduct
        period hPeriod).contDiff.comp hInverseProduct
    exact hOperator.clm_apply hFirstConstant
  have hSecondConstant : ContDiff Real ∞
      (fun _ : C2FiniteMatrix period hPeriod 4 => second ρ σ) :=
    contDiff_const
  have hOperator : ContDiff Real ∞
      (fun inverseMetric : C2FiniteMatrix period hPeriod 4 =>
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
              (inverseMetric μ ρ) (inverseMetric ν σ))
            (first μ ν))) :=
    (canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.comp hFirstProduct
  exact hOperator.clm_apply hSecondConstant

/-- Maxwell pairing throughout the genuine open general-metric chart. -/
def regularGeneralMetricC2MaxwellPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C2Scalar period hPeriod :=
  ∑ component : Fin 2,
    c2MaxwellMatrixContraction period hPeriod
      (regularGeneralMetricC2InverseMetricMatrix
        period hPeriod metric variation)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric first component)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric second component)

theorem regularGeneralMetricC2MaxwellPairing_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2MaxwellPairing
        period hPeriod metric first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  apply ContDiffOn.sum
  intro component _
  exact
    (c2MaxwellMatrixContraction_contDiff period hPeriod
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric first component)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric second component)).of_le
          (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
            exact WithTop.coe_le_coe.mpr le_top)
      |>.contDiffOn.comp
        ((regularGeneralMetricC2InverseMetricMatrix_contDiffOn
          period hPeriod metric).of_le
            (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
              exact WithTop.coe_le_coe.mpr le_top))
        (fun _ _ => mem_univ _)

/-- Smooth version of the same finite contraction. -/
def smoothMaxwellMatrixContraction
    (inverseMetric first second : SmoothFiniteMatrix period hPeriod 4) :
    SmoothScalarField period hPeriod :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    smoothScalarFieldMul period hPeriod
      (smoothScalarFieldMul period hPeriod
        (smoothScalarFieldMul period hPeriod
          (inverseMetric μ ρ) (inverseMetric ν σ))
        (first μ ν))
      (second ρ σ)

@[simp]
private theorem smoothFiniteMatrixToC2_entry
    (matrix : SmoothFiniteMatrix period hPeriod 4) (row column : Fin 4) :
    smoothFiniteMatrixToC2 period hPeriod 4 matrix row column =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (matrix row column) :=
  rfl

theorem c2MaxwellMatrixContraction_smooth
    (inverseMetric first second : SmoothFiniteMatrix period hPeriod 4) :
    c2MaxwellMatrixContraction period hPeriod
        (smoothFiniteMatrixToC2 period hPeriod 4 inverseMetric)
        (smoothFiniteMatrixToC2 period hPeriod 4 first)
        (smoothFiniteMatrixToC2 period hPeriod 4 second) =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothMaxwellMatrixContraction period hPeriod
          inverseMetric first second) := by
  unfold c2MaxwellMatrixContraction smoothMaxwellMatrixContraction
  simp_rw [map_sum]
  simp_rw [smoothFiniteMatrixToC2_entry,
    canonicalPhysicalScalarC2JetCoreProduct_smooth]

/-- Genuine regular-frame smooth pairing before its exact chart-free
identification. -/
def regularFrameSmoothMaxwellPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ component : Fin 2,
    smoothMaxwellMatrixContraction period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric)
      (regularFrameGaugeCurvatureMatrix period hPeriod metric first component)
      (regularFrameGaugeCurvatureMatrix period hPeriod metric second component)

theorem regularFrameSmoothMaxwellPairing_eq_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameSmoothMaxwellPairing period hPeriod metric first second =
      globalSmoothMaxwellPairing period hPeriod metric.metric first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  change regularFrameSmoothMaxwellPairing period hPeriod metric first second
      (patch.coordinateMap coordinate) =
    globalMaxwellPairing period hPeriod metric.metric first second
      (patch.coordinateMap coordinate)
  rw [globalMaxwellPairing_eq_regularFrameContraction]
  simp [regularFrameSmoothMaxwellPairing, smoothMaxwellMatrixContraction,
    matrixMaxwellContraction, regularFrameMetricInverseMatrix,
    regularFrameMetricInverseMatrixMap, smoothScalarFieldMul_apply,
    regularFrameGaugeCurvatureMatrix,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]

theorem regularGeneralMetricC2MaxwellPairing_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC2MaxwellPairing period hPeriod metric first second 0 =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (globalSmoothMaxwellPairing period hPeriod metric.metric first second) := by
  rw [regularGeneralMetricC2MaxwellPairing,
    regularGeneralMetricC2InverseMetricMatrix_zero]
  unfold regularFrameMetricInverseC2Matrix
    regularFrameGaugeCurvatureC2Matrix
  simp_rw [c2MaxwellMatrixContraction_smooth]
  rw [← map_sum]
  exact congrArg
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    (regularFrameSmoothMaxwellPairing_eq_global
      period hPeriod metric first second)

/-- Maxwell density including the varied positive volume factor. -/
def regularGeneralMetricC2MaxwellDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C2Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (regularGeneralMetricC2Volume period hPeriod metric variation)
    (regularGeneralMetricC2MaxwellPairing
      period hPeriod metric first second variation)

theorem regularGeneralMetricC2MaxwellDensity_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2MaxwellDensity
        period hPeriod metric first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  have hOperator : ContDiffOn Real 2
      (fun variation =>
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (regularGeneralMetricC2Volume
            period hPeriod metric variation))
      (regularGeneralMetricC2Domain period hPeriod metric) :=
    (canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.contDiffOn.comp
        (regularGeneralMetricC2Volume_contDiffOn_two
          period hPeriod metric)
        (fun _ _ => mem_univ _)
  exact hOperator.clm_apply
    (regularGeneralMetricC2MaxwellPairing_contDiffOn_two
      period hPeriod metric first second)

theorem regularGeneralMetricC2MaxwellDensity_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC2MaxwellDensity period hPeriod metric first second 0 =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothScalarFieldMul period hPeriod metric.volume
          (globalSmoothMaxwellPairing
            period hPeriod metric.metric first second)) := by
  rw [regularGeneralMetricC2MaxwellDensity,
    regularGeneralMetricC2Volume_zero,
    regularGeneralMetricC2MaxwellPairing_zero,
    canonicalPhysicalScalarC2JetCoreProduct_smooth]

/-- Integrated general-metric Maxwell pairing against any finite common
measure. -/
def regularGeneralMetricC2IntegratedMaxwellPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
    (regularGeneralMetricC2MaxwellDensity
      period hPeriod metric first second variation)

theorem regularGeneralMetricC2IntegratedMaxwellPairing_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2IntegratedMaxwellPairing
        period hPeriod metric measure first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  exact (canonicalPhysicalC2ScalarIntegralCLM
      period hPeriod measure).contDiff.contDiffOn.comp
    (regularGeneralMetricC2MaxwellDensity_contDiffOn_two
      period hPeriod metric first second)
    (fun _ _ => mem_univ _)

theorem regularGeneralMetricC2IntegratedMaxwellPairing_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC2IntegratedMaxwellPairing
        period hPeriod metric measure first second 0 =
      ∫ point, metric.volume point *
        globalMaxwellPairing period hPeriod metric.metric first second point
        ∂measure := by
  rw [regularGeneralMetricC2IntegratedMaxwellPairing,
    regularGeneralMetricC2MaxwellDensity_zero,
    canonicalPhysicalC2ScalarIntegralCLM_apply,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

/-- Summary gate for the unrestricted local general-metric Maxwell family. -/
theorem regular_general_metric_c2_maxwell_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
        (regularGeneralMetricC2MaxwellPairing
          period hPeriod metric first second)
        (regularGeneralMetricC2Domain period hPeriod metric) ∧
      regularGeneralMetricC2MaxwellPairing
          period hPeriod metric first second 0 =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (globalSmoothMaxwellPairing period hPeriod metric.metric first second) ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2IntegratedMaxwellPairing
          period hPeriod metric measure first second)
        (regularGeneralMetricC2Domain period hPeriod metric) ∧
      regularGeneralMetricC2IntegratedMaxwellPairing
          period hPeriod metric measure first second 0 =
        ∫ point, metric.volume point *
          globalMaxwellPairing period hPeriod metric.metric first second point
          ∂measure :=
  ⟨regularGeneralMetricC2MaxwellPairing_contDiffOn_two
      period hPeriod metric first second,
    regularGeneralMetricC2MaxwellPairing_zero
      period hPeriod metric first second,
    regularGeneralMetricC2IntegratedMaxwellPairing_contDiffOn_two
      period hPeriod metric measure first second,
    regularGeneralMetricC2IntegratedMaxwellPairing_zero
      period hPeriod metric measure first second⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
end JanusFormal
