import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# General-metric C2 Einstein--Hilbert family

This is the unique P1 implementation named by the authoritative
`HESSIAN-GLOBAL-01` closure map.  It reuses the canonical physical C2 jet
core and the existing smooth redundant-frame coefficients.  Spatial scalar
curvature targets `C0`; only parameter dependence is C2.  No C4 metric
regularity or additional metric ansatz is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff BigOperators ENNReal Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev PhysicalFrame :=
  finiteSmoothTangentFrame period hPeriod

private abbrev PhysicalIndex :=
  Fin (PhysicalFrame period hPeriod).count

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev CoordinateMatrix :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

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
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel (EffectiveQuotient period hPeriod)

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

/-! ## The actual varied metric matrix -/

/-- The varied metric in the fixed regular frame.  The relative chart stores
`g₀⁻¹ h`, hence the actual metric is `g₀ (1 + g₀⁻¹ h)`. -/
def regularGeneralMetricC2MetricMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :=
  c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    (regularFrameMetricC2Matrix period hPeriod metric)
    (generalMetricRelativeC2ExtendedMatrix period hPeriod
      (RegularFrame period hPeriod metric) metric.metric variation)

theorem regularGeneralMetricC2MetricMatrix_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞
      (regularGeneralMetricC2MetricMatrix period hPeriod metric) := by
  exact
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (regularFrameMetricC2Matrix period hPeriod metric)).contDiff.comp
        (generalMetricRelativeC2ExtendedMatrix_contDiff period hPeriod
          (RegularFrame period hPeriod metric) metric.metric)

theorem regularGeneralMetricC2MetricMatrix_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2MetricMatrix period hPeriod metric 0 =
      regularFrameMetricC2Matrix period hPeriod metric := by
  unfold regularGeneralMetricC2MetricMatrix
    generalMetricRelativeC2ExtendedMatrix
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (regularFrameMetricC2Matrix period hPeriod metric)
      (c2FiniteMatrixIdentity period hPeriod 4 + 0) =
    regularFrameMetricC2Matrix period hPeriod metric
  rw [add_zero, c2FiniteMatrixProduct_identity_right]

/-! ## Lossless projections from the canonical second jet -/

def scalarFrameJet2FirstComponent
    (index : PhysicalIndex period hPeriod) :
    ScalarFrameJet2 (PhysicalIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst Real
      (PhysicalIndex period hPeriod → Real)
      (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)).comp
    (ContinuousLinearMap.snd Real Real
      ((PhysicalIndex period hPeriod → Real) ×
        (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real))))

def scalarFrameJet2SecondComponent
    (outer inner : PhysicalIndex period hPeriod) :
    ScalarFrameJet2 (PhysicalIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp
    ((ContinuousLinearMap.proj outer).comp
      ((ContinuousLinearMap.snd Real
        (PhysicalIndex period hPeriod → Real)
        (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)).comp
      (ContinuousLinearMap.snd Real Real
        ((PhysicalIndex period hPeriod → Real) ×
          (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)))))

def canonicalPhysicalScalarC2FirstComponent
    (index : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ((scalarFrameJet2FirstComponent period hPeriod index).compLeftContinuous
      Real (EffectiveQuotient period hPeriod)).comp
    (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)

def canonicalPhysicalScalarC2SecondComponent
    (outer inner : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ((scalarFrameJet2SecondComponent period hPeriod outer inner).compLeftContinuous
      Real (EffectiveQuotient period hPeriod)).comp
    (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)

@[simp]
theorem canonicalPhysicalScalarC2FirstComponent_smooth
    (field : SmoothScalarField period hPeriod)
    (index : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2FirstComponent period hPeriod index
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
        field point index :=
  rfl

@[simp]
theorem canonicalPhysicalScalarC2SecondComponent_smooth
    (field : SmoothScalarField period hPeriod)
    (outer inner : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2SecondComponent period hPeriod outer inner
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameSecondDerivative period hPeriod (PhysicalFrame period hPeriod)
        field point outer inner :=
  rfl

/-! ## Existing redundant-frame coefficients, reused -/

/-- Smooth coefficients expressing one regular-frame vector in the canonical
finite physical spanning family. -/
def regularFrameFromPhysicalCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (index : PhysicalIndex period hPeriod) :
    SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (PhysicalFrame period hPeriod) metric.metric (metric.frame regular) index

theorem regularFrameFromPhysical_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (point : EffectiveQuotient period hPeriod) :
    metric.frame regular point =
      ∑ index : PhysicalIndex period hPeriod,
        regularFrameFromPhysicalCoefficient period hPeriod metric regular index
            point •
          (PhysicalFrame period hPeriod).vectorAt point index :=
  generalMetricFiniteFrame_reconstructs period hPeriod
    (PhysicalFrame period hPeriod) metric.metric (metric.frame regular) point

def regularFrameFromPhysicalCoefficientContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (index : PhysicalIndex period hPeriod) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (regularFrameFromPhysicalCoefficient period hPeriod metric regular index)

@[simp]
theorem regularFrameFromPhysicalCoefficientContinuous_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (index : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
        regular index point =
      regularFrameFromPhysicalCoefficient period hPeriod metric regular index
        point :=
  rfl

/-! ## First regular-frame derivative on the completed C2 core -/

def regularFrameC2FirstDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (jet : C2Scalar period hPeriod) :
    C0Scalar period hPeriod :=
  ∑ index : PhysicalIndex period hPeriod,
    regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
        regular index *
      canonicalPhysicalScalarC2FirstComponent period hPeriod index jet

theorem regularFrameC2FirstDerivative_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) :
    ContDiff Real ∞
      (regularFrameC2FirstDerivative period hPeriod metric regular) := by
  apply ContDiff.sum
  intro index _
  exact contDiff_const.mul
    (canonicalPhysicalScalarC2FirstComponent
      period hPeriod index).contDiff

@[simp]
theorem regularFrameC2FirstDerivative_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (first second : C2Scalar period hPeriod) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (first + second) =
      regularFrameC2FirstDerivative period hPeriod metric regular first +
        regularFrameC2FirstDerivative period hPeriod metric regular second := by
  unfold regularFrameC2FirstDerivative
  simp only [map_add, mul_add, Finset.sum_add_distrib]

theorem regularFrameC2FirstDerivative_sum
    {indexType : Type*} [Fintype indexType]
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (jet : indexType → C2Scalar period hPeriod) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (∑ index, jet index) =
      ∑ index, regularFrameC2FirstDerivative period hPeriod metric regular
        (jet index) := by
  apply ContinuousMap.ext
  intro point
  unfold regularFrameC2FirstDerivative
  simp only [map_sum, ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

@[simp]
theorem regularFrameC2FirstDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameDerivative period hPeriod Real
        (RegularFrame period hPeriod metric) field point regular := by
  unfold regularFrameC2FirstDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    regularFrameFromPhysicalCoefficientContinuous_apply,
    canonicalPhysicalScalarC2FirstComponent_smooth]
  rw [frameDerivative_eq_mfderiv]
  rw [regularGeneralLorentzMetricSmoothD8Frame_vectorAt]
  change (∑ index : PhysicalIndex period hPeriod,
      regularFrameFromPhysicalCoefficient period hPeriod metric regular index
          point *
        frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
          field point index) = _
  rw [regularFrameFromPhysical_reconstructs period hPeriod metric regular point]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul]
  rw [frameDerivative_eq_mfderiv]
  rfl

@[simp]
theorem regularFrameC2FirstDerivative_constant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (value : Real) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField
            period hPeriod Real value)) = 0 := by
  apply ContinuousMap.ext
  intro point
  rw [regularFrameC2FirstDerivative_smooth,
    frameDerivative_eq_mfderiv]
  simp [mvfderiv,
    P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField,
    mfderiv_const]
  exact map_zero (NormedSpace.fromTangentSpace value)

@[simp]
theorem regularFrameC2FirstDerivative_identity_entry
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (dimension : Nat) (row column : Fin dimension) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (c2FiniteMatrixIdentity period hPeriod dimension row column) = 0 := by
  change regularFrameC2FirstDerivative period hPeriod metric regular
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField
          period hPeriod Real (if row = column then 1 else 0))) = 0
  exact regularFrameC2FirstDerivative_constant period hPeriod metric regular _

/-- The completed regular-frame derivative obeys the exact Leibniz rule of
the canonical physical C2 jet product. -/
theorem regularFrameC2FirstDerivative_product
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (first second : C2Scalar period hPeriod) :
    regularFrameC2FirstDerivative period hPeriod metric regular
        (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first second) =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first *
          regularFrameC2FirstDerivative
            period hPeriod metric regular second +
        regularFrameC2FirstDerivative period hPeriod metric regular first *
          canonicalPhysicalScalarC2JetCoreToContinuous
            period hPeriod second := by
  apply ContinuousMap.ext
  intro point
  unfold regularFrameC2FirstDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply]
  change
    (∑ index : PhysicalIndex period hPeriod,
      regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
          regular index point *
        ((first.1 point).1 * (second.1 point).2.1 index +
          (second.1 point).1 * (first.1 point).2.1 index)) =
      (first.1 point).1 *
          ∑ index : PhysicalIndex period hPeriod,
            regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
                regular index point * (second.1 point).2.1 index +
        (∑ index : PhysicalIndex period hPeriod,
            regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
                regular index point * (first.1 point).2.1 index) *
          (second.1 point).1
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro index _ <;> ring

/-! ## Second regular-frame derivative on the same completed core -/

/-- The physical derivative of one already existing frame coefficient. -/
def regularFrameFromPhysicalCoefficientDerivativeContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (inner outer : PhysicalIndex period hPeriod) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (frameDerivativeComponentField period hPeriod
      (PhysicalFrame period hPeriod)
      (regularFrameFromPhysicalCoefficient period hPeriod metric regular inner)
      outer)

@[simp]
theorem regularFrameFromPhysicalCoefficientDerivativeContinuous_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (inner outer : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameFromPhysicalCoefficientDerivativeContinuous period hPeriod
        metric regular inner outer point =
      frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
        (regularFrameFromPhysicalCoefficient period hPeriod metric regular inner)
        point outer :=
  rfl

/-- Ordered derivative `e_outer (e_inner f)`.  The formula is the exact
frame-change chain rule; it loses no information from the canonical C² jet. -/
def regularFrameC2SecondDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : Fin 4) (jet : C2Scalar period hPeriod) :
    C0Scalar period hPeriod :=
  ∑ physicalOuter : PhysicalIndex period hPeriod,
    regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
        outer physicalOuter *
      ∑ physicalInner : PhysicalIndex period hPeriod, (
        regularFrameFromPhysicalCoefficientDerivativeContinuous period hPeriod
            metric inner physicalInner physicalOuter *
          canonicalPhysicalScalarC2FirstComponent period hPeriod
            physicalInner jet +
        regularFrameFromPhysicalCoefficientContinuous period hPeriod metric
            inner physicalInner *
          canonicalPhysicalScalarC2SecondComponent period hPeriod
            physicalOuter physicalInner jet)

theorem regularFrameC2SecondDerivative_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : Fin 4) :
    ContDiff Real ∞
      (regularFrameC2SecondDerivative period hPeriod metric outer inner) := by
  unfold regularFrameC2SecondDerivative
  apply ContDiff.sum
  intro physicalOuter _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro physicalInner _
  exact
    (contDiff_const.mul
      (canonicalPhysicalScalarC2FirstComponent period hPeriod
        physicalInner).contDiff).add
    (contDiff_const.mul
      (canonicalPhysicalScalarC2SecondComponent period hPeriod
        physicalOuter physicalInner).contDiff)

/-- Smooth first derivatives obey the same finite frame-change formula as
the completed first-jet operator. -/
theorem regularFrameDerivativeComponentField_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (field : SmoothScalarField period hPeriod) :
    frameDerivativeComponentField period hPeriod
        (RegularFrame period hPeriod metric) field regular =
      ∑ physical : PhysicalIndex period hPeriod,
        smoothScalarFieldMul period hPeriod
          (regularFrameFromPhysicalCoefficient period hPeriod metric
            regular physical)
          (frameDerivativeComponentField period hPeriod
            (PhysicalFrame period hPeriod) field physical) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hAgreement := regularFrameC2FirstDerivative_smooth period hPeriod
    metric regular field point
  simp only [frameDerivativeComponentField,
    smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  change frameDerivative period hPeriod Real
      (RegularFrame period hPeriod metric) field point regular =
    ∑ physical : PhysicalIndex period hPeriod,
      regularFrameFromPhysicalCoefficient period hPeriod metric regular
          physical point *
        frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
          field point physical
  unfold regularFrameC2FirstDerivative at hAgreement
  simp only [ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, regularFrameFromPhysicalCoefficientContinuous,
    canonicalPhysicalScalarC2FirstComponent_smooth] at hAgreement
  change (∑ physical : PhysicalIndex period hPeriod,
      regularFrameFromPhysicalCoefficient period hPeriod metric regular
          physical point *
        frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
          field point physical) = _ at hAgreement
  exact hAgreement.symm

private theorem frameDerivative_finset_sum
    {Index : Type*} [DecidableEq Index]
    (frame : SmoothD8Frame period hPeriod)
    (fields : Index → SmoothScalarField period hPeriod)
    (indices : Finset Index)
    (point : EffectiveQuotient period hPeriod)
    (direction : Fin frame.count) :
    frameDerivative period hPeriod Real frame
        (∑ index ∈ indices, fields index) point direction =
      ∑ index ∈ indices,
        frameDerivative period hPeriod Real frame (fields index)
          point direction := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [frameDerivative_eq_mfderiv]
      change mvfderiv coverModelWithCorners
        (0 : EffectiveQuotient period hPeriod → Real) point
          (frame.vectorAt point direction) = 0
      rw [mvfderiv_zero]
      rfl
  | @insert current indices hCurrent induction =>
      simp only [Finset.sum_insert hCurrent]
      rw [show
        frameDerivative period hPeriod Real frame
            (fields current + ∑ index ∈ indices, fields index)
              point direction =
          frameDerivative period hPeriod Real frame (fields current)
              point direction +
            frameDerivative period hPeriod Real frame
              (∑ index ∈ indices, fields index) point direction from
        congrFun (congrFun
          (frameDerivative_add period hPeriod Real frame
            (fields current) (∑ index ∈ indices, fields index)) point)
          direction]
      rw [induction]

@[simp]
theorem regularFrameC2SecondDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : Fin 4) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameC2SecondDerivative period hPeriod metric outer inner
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameSecondDerivative period hPeriod
        (RegularFrame period hPeriod metric) field point outer inner := by
  unfold regularFrameC2SecondDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply,
    regularFrameFromPhysicalCoefficientContinuous_apply,
    regularFrameFromPhysicalCoefficientDerivativeContinuous_apply,
    canonicalPhysicalScalarC2FirstComponent_smooth,
    canonicalPhysicalScalarC2SecondComponent_smooth]
  unfold frameSecondDerivative
  rw [regularFrameDerivativeComponentField_eq_sum period hPeriod metric
    inner field]
  rw [frameDerivative_eq_mfderiv]
  rw [regularGeneralLorentzMetricSmoothD8Frame_vectorAt]
  rw [regularFrameFromPhysical_reconstructs period hPeriod metric outer point]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  simp_rw [← frameDerivative_eq_mfderiv]
  simp_rw [frameDerivative_finset_sum period hPeriod]
  simp_rw [frameDerivative_mul period hPeriod
    (PhysicalFrame period hPeriod)]
  simp only [frameDerivativeComponentField]
  apply Finset.sum_congr rfl
  intro physicalOuter _
  congr 1
  apply Finset.sum_congr rfl
  intro physicalInner _
  ring

/-! ## Metric jets and the fixed anholonomy of the regular frame -/

private theorem c2FiniteMatrixEntry_contDiff
    (row column : Fin 4) :
    ContDiff Real ∞
      (fun matrix : C2FiniteMatrix period hPeriod 4 => matrix row column) :=
  (contDiff_apply Real (C2Scalar period hPeriod) column).comp
    (contDiff_apply Real (Fin 4 → C2Scalar period hPeriod) row)

/-- Continuous value of the varied metric in the fixed regular frame. -/
def regularGeneralMetricC0MetricCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (row column : Fin 4) : C0Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (regularGeneralMetricC2MetricMatrix period hPeriod metric variation
      row column)

theorem regularGeneralMetricC0MetricCoefficient_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    ContDiff Real ∞
      (fun variation => regularGeneralMetricC0MetricCoefficient period hPeriod
        metric variation row column) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous
    period hPeriod).contDiff.comp
      ((c2FiniteMatrixEntry_contDiff period hPeriod row column).comp
        (regularGeneralMetricC2MetricMatrix_contDiff period hPeriod metric))

/-- Entrywise value expansion of the installed regular metric chart. -/
theorem regularGeneralMetricC0MetricCoefficient_apply_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric variation
        row column point =
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
              (variation.1 middle column) point) := by
  unfold regularGeneralMetricC0MetricCoefficient
    regularGeneralMetricC2MetricMatrix
  rw [c2FiniteMatrixProduct_apply, map_sum]
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro middle _
  change
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (regularFrameMetricC2Matrix period hPeriod metric row middle) point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (generalMetricRelativeC2ExtendedMatrix period hPeriod
            (RegularFrame period hPeriod metric) metric.metric variation
              middle column) point = _
  have hBaseJet :
      regularFrameMetricC2Matrix period hPeriod metric row middle =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (regularFrameMetricMatrix period hPeriod metric row middle) :=
    rfl
  have hBaseValue :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (regularFrameMetricMatrix period hPeriod metric row middle) point =
        regularFrameMetricMatrix period hPeriod metric row middle point :=
    rfl
  rw [hBaseJet, canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    hBaseValue]
  unfold generalMetricRelativeC2ExtendedMatrix
  rw [Pi.add_apply, Pi.add_apply, map_add]
  simp only [ContinuousMap.add_apply]
  have hIdentityValue :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2FiniteMatrixIdentity period hPeriod
            (RegularFrame period hPeriod metric).count middle column) point =
        (1 : Matrix (Fin 4) (Fin 4) Real) middle column := by
    rw [show c2FiniteMatrixIdentity period hPeriod
          (RegularFrame period hPeriod metric).count middle column =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothFiniteMatrixIdentity period hPeriod
            (RegularFrame period hPeriod metric).count middle column) from rfl,
      canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    simp [smoothFiniteMatrixIdentity, Matrix.one_apply,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D.smoothToCanonicalPhysicalContinuousScalar,
      P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField]
  rw [hIdentityValue]

theorem regularGeneralMetricC0MetricCoefficient_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameMetricMatrix period hPeriod metric row column) := by
  unfold regularGeneralMetricC0MetricCoefficient
  rw [regularGeneralMetricC2MetricMatrix_zero]
  unfold regularFrameMetricC2Matrix smoothFiniteMatrixToC2
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod
    (regularFrameMetricMatrix period hPeriod metric row column)

/-- First spacetime derivative of the varied metric coefficient. -/
def regularGeneralMetricC0MetricFirstDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative row column : Fin 4) : C0Scalar period hPeriod :=
  regularFrameC2FirstDerivative period hPeriod metric derivative
    (regularGeneralMetricC2MetricMatrix period hPeriod metric variation
      row column)

theorem regularGeneralMetricC0MetricFirstDerivative_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative row column : Fin 4) :
    ContDiff Real ∞
      (fun variation =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          variation derivative row column) :=
  (regularFrameC2FirstDerivative_contDiff period hPeriod metric derivative).comp
    ((c2FiniteMatrixEntry_contDiff period hPeriod row column).comp
      (regularGeneralMetricC2MetricMatrix_contDiff period hPeriod metric))

/-- Entrywise Leibniz expansion of the first derivative of the installed
regular metric chart. -/
theorem regularGeneralMetricC0MetricFirstDerivative_apply_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        variation derivative row column point =
      ∑ middle : Fin 4,
        (frameDerivative period hPeriod Real
              (RegularFrame period hPeriod metric)
              (regularFrameMetricMatrix period hPeriod metric row middle)
              point derivative *
            ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
              canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
                (variation.1 middle column) point) +
          regularFrameMetricMatrix period hPeriod metric row middle point *
            regularFrameC2FirstDerivative period hPeriod metric derivative
              (variation.1 middle column) point) := by
  unfold regularGeneralMetricC0MetricFirstDerivative
    regularGeneralMetricC2MetricMatrix
  rw [c2FiniteMatrixProduct_apply,
    regularFrameC2FirstDerivative_sum]
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro middle _
  rw [regularFrameC2FirstDerivative_product]
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply]
  have hBaseJet :
      regularFrameMetricC2Matrix period hPeriod metric row middle =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (regularFrameMetricMatrix period hPeriod metric row middle) :=
    rfl
  have hBaseValue :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (regularFrameMetricMatrix period hPeriod metric row middle) point =
        regularFrameMetricMatrix period hPeriod metric row middle point :=
    rfl
  rw [hBaseJet, regularFrameC2FirstDerivative_smooth,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  unfold generalMetricRelativeC2ExtendedMatrix
  rw [Pi.add_apply, Pi.add_apply,
    regularFrameC2FirstDerivative_add,
    regularFrameC2FirstDerivative_identity_entry, map_add]
  simp only [ContinuousMap.zero_apply, zero_add, ContinuousMap.add_apply]
  have hIdentityValue :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2FiniteMatrixIdentity period hPeriod
            (RegularFrame period hPeriod metric).count middle column) point =
        (1 : Matrix (Fin 4) (Fin 4) Real) middle column := by
    rw [show c2FiniteMatrixIdentity period hPeriod
          (RegularFrame period hPeriod metric).count middle column =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothFiniteMatrixIdentity period hPeriod
            (RegularFrame period hPeriod metric).count middle column) from rfl,
      canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    simp [smoothFiniteMatrixIdentity, Matrix.one_apply,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D.smoothToCanonicalPhysicalContinuousScalar,
      P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField]
  rw [hIdentityValue, hBaseValue]
  ring

theorem regularGeneralMetricC0MetricFirstDerivative_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative row column : Fin 4) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        derivative row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (frameDerivativeComponentField period hPeriod
          (RegularFrame period hPeriod metric)
          (regularFrameMetricMatrix period hPeriod metric row column)
          derivative) := by
  apply ContinuousMap.ext
  intro point
  unfold regularGeneralMetricC0MetricFirstDerivative
  rw [regularGeneralMetricC2MetricMatrix_zero]
  change regularFrameC2FirstDerivative period hPeriod metric derivative
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameMetricMatrix period hPeriod metric row column)) point =
    frameDerivative period hPeriod Real
      (RegularFrame period hPeriod metric)
      (regularFrameMetricMatrix period hPeriod metric row column)
      point derivative
  exact regularFrameC2FirstDerivative_smooth period hPeriod metric derivative
    (regularFrameMetricMatrix period hPeriod metric row column) point

/-- Ordered second spacetime derivative of the varied metric coefficient. -/
def regularGeneralMetricC0MetricSecondDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (outer inner row column : Fin 4) : C0Scalar period hPeriod :=
  regularFrameC2SecondDerivative period hPeriod metric outer inner
    (regularGeneralMetricC2MetricMatrix period hPeriod metric variation
      row column)

theorem regularGeneralMetricC0MetricSecondDerivative_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner row column : Fin 4) :
    ContDiff Real ∞
      (fun variation =>
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation outer inner row column) :=
  (regularFrameC2SecondDerivative_contDiff period hPeriod metric
      outer inner).comp
    ((c2FiniteMatrixEntry_contDiff period hPeriod row column).comp
      (regularGeneralMetricC2MetricMatrix_contDiff period hPeriod metric))

theorem regularGeneralMetricC0MetricSecondDerivative_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner row column : Fin 4) :
    regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
        outer inner row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        { toFun := fun point =>
            frameSecondDerivative period hPeriod
              (RegularFrame period hPeriod metric)
              (regularFrameMetricMatrix period hPeriod metric row column)
              point outer inner
          contMDiff_toFun :=
            (contMDiff_pi_space.mp (contMDiff_pi_space.mp
              (frameSecondDerivative_contMDiff period hPeriod
                (RegularFrame period hPeriod metric)
                (regularFrameMetricMatrix period hPeriod metric row column))
              outer) inner) } := by
  apply ContinuousMap.ext
  intro point
  unfold regularGeneralMetricC0MetricSecondDerivative
  rw [regularGeneralMetricC2MetricMatrix_zero]
  change regularFrameC2SecondDerivative period hPeriod metric outer inner
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameMetricMatrix period hPeriod metric row column)) point =
    frameSecondDerivative period hPeriod
      (RegularFrame period hPeriod metric)
      (regularFrameMetricMatrix period hPeriod metric row column)
      point outer inner
  exact regularFrameC2SecondDerivative_smooth period hPeriod metric outer inner
    (regularFrameMetricMatrix period hPeriod metric row column) point

/-- Intrinsic Lie bracket of two members of the fixed smooth regular frame. -/
def regularFrameLieBracket
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) : SmoothTangentField period hPeriod where
  toFun := VectorField.mlieBracket coverModelWithCorners
    (metric.frame first) (metric.frame second)
  contMDiff_toFun := by
    intro point
    exact ((metric.frame first).contMDiff_toFun point).mlieBracket_vectorField
      ((metric.frame second).contMDiff_toFun point) (by simp)

/-- Smooth structure coefficients `[e_i,e_j] = C^k_ij e_k`, obtained from
the already available finite-frame reconstruction. -/
def regularFrameStructureCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (RegularFrame period hPeriod metric) metric.metric
    (regularFrameLieBracket period hPeriod metric first second) upper

theorem regularFrameStructureCoefficient_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameLieBracket period hPeriod metric first second point =
      ∑ upper : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
            upper point •
          metric.frame upper point := by
  change regularFrameLieBracket period hPeriod metric first second point =
    ∑ upper : Fin (RegularFrame period hPeriod metric).count,
      generalMetricFiniteFrameCoefficient period hPeriod
          (RegularFrame period hPeriod metric) metric.metric
          (regularFrameLieBracket period hPeriod metric first second) upper
          point •
        (RegularFrame period hPeriod metric).vectorAt point upper
  exact generalMetricFiniteFrame_reconstructs period hPeriod
    (RegularFrame period hPeriod metric) metric.metric
    (regularFrameLieBracket period hPeriod metric first second) point

def regularFrameStructureCoefficientContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (regularFrameStructureCoefficient period hPeriod metric first second upper)

@[simp]
theorem regularFrameStructureCoefficientContinuous_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameStructureCoefficientContinuous period hPeriod metric
        first second upper point =
      regularFrameStructureCoefficient period hPeriod metric first second upper
        point :=
  rfl

def regularFrameStructureCoefficientDerivativeContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second upper : Fin 4) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (frameDerivativeComponentField period hPeriod
      (RegularFrame period hPeriod metric)
      (regularFrameStructureCoefficient period hPeriod metric first second upper)
      derivative)

@[simp]
theorem regularFrameStructureCoefficientDerivativeContinuous_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second upper : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameStructureCoefficientDerivativeContinuous period hPeriod metric
        derivative first second upper point =
      frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
        (regularFrameStructureCoefficient period hPeriod metric first second
          upper) point derivative :=
  rfl

/-! ## Levi--Civita coefficients on the admissible open chart -/

def regularGeneralMetricC0InverseMetricCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (row column : Fin 4) : C0Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric variation
      row column)

theorem regularGeneralMetricC0InverseMetricCoefficient_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    ContDiffOn Real ∞
      (fun variation =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          variation row column)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  exact (canonicalPhysicalScalarC2JetCoreToContinuous
    period hPeriod).contDiff.contDiffOn.comp
      ((c2FiniteMatrixEntry_contDiff period hPeriod row column).contDiffOn.comp
        (regularGeneralMetricC2InverseMetricMatrix_contDiffOn
          period hPeriod metric)
        (fun _ _ => Set.mem_univ _))
      (fun _ _ => Set.mem_univ _)

theorem regularGeneralMetricC0InverseMetricCoefficient_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
        row column =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric row column) := by
  unfold regularGeneralMetricC0InverseMetricCoefficient
  rw [regularGeneralMetricC2InverseMetricMatrix_zero]
  unfold regularFrameMetricInverseC2Matrix smoothFiniteMatrixToC2
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod
    (regularFrameMetricInverseMatrix period hPeriod metric row column)

/-- Lowered Koszul coefficient
`Γ_{i j k} = g(∇_{e_i} e_j, e_k)` in the fixed nonholonomic frame. -/
def regularGeneralMetricC0KoszulLower
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (first second lower : Fin 4) : C0Scalar period hPeriod :=
  (1 / 2 : Real) •
    (regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          variation first second lower +
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          variation second lower first -
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          variation lower first second -
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficientContinuous period hPeriod metric
            second lower contracted *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            variation first contracted +
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficientContinuous period hPeriod metric
            lower first contracted *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            variation second contracted +
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficientContinuous period hPeriod metric
            first second contracted *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            variation lower contracted)

theorem regularGeneralMetricC0KoszulLower_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Fin 4) :
    ContDiff Real ∞
      (fun variation => regularGeneralMetricC0KoszulLower period hPeriod metric
        variation first second lower) := by
  unfold regularGeneralMetricC0KoszulLower
  apply ContDiff.const_smul
  apply ContDiff.add
  · apply ContDiff.add
    · apply ContDiff.sub
      · apply ContDiff.sub
        · exact (regularGeneralMetricC0MetricFirstDerivative_contDiff
            period hPeriod metric first second lower).add
            (regularGeneralMetricC0MetricFirstDerivative_contDiff
              period hPeriod metric second lower first)
        · exact regularGeneralMetricC0MetricFirstDerivative_contDiff
            period hPeriod metric lower first second
      · apply ContDiff.sum
        intro contracted _
        exact contDiff_const.mul
          (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod
            metric first contracted)
    · apply ContDiff.sum
      intro contracted _
      exact contDiff_const.mul
        (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod
          metric second contracted)
  · apply ContDiff.sum
    intro contracted _
    exact contDiff_const.mul
      (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod
        metric lower contracted)

/-- Raised Levi--Civita coefficient `Γ^upper_first,second`. -/
def regularGeneralMetricC0Christoffel
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (upper first second : Fin 4) : C0Scalar period hPeriod :=
  ∑ lower : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation upper lower *
      regularGeneralMetricC0KoszulLower period hPeriod metric variation
        first second lower

theorem regularGeneralMetricC0Christoffel_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Fin 4) :
    ContDiffOn Real ∞
      (fun variation => regularGeneralMetricC0Christoffel period hPeriod
        metric variation upper first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0Christoffel
  apply ContDiffOn.sum
  intro lower _
  exact
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod
      metric upper lower).mul
    (regularGeneralMetricC0KoszulLower_contDiff period hPeriod metric
      first second lower).contDiffOn

/-- Exact first derivative of the inverse matrix, obtained by differentiating
`g⁻¹ g = 1`; no extra inverse regularity is assumed. -/
def regularGeneralMetricC0InverseMetricDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative upper lower : Fin 4) : C0Scalar period hPeriod :=
  -∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation upper first *
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        variation derivative first second *
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation second lower

theorem regularGeneralMetricC0InverseMetricDerivative_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper lower : Fin 4) :
    ContDiffOn Real ∞
      (fun variation =>
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
          variation derivative upper lower)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0InverseMetricDerivative
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  exact
    ((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod
      metric upper first).mul
      (regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod
        metric derivative first second).contDiffOn).mul
    (regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod
      metric second lower)

def regularFrameStructureMetricDerivativeTerm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn :
      Fin 4) : C0Scalar period hPeriod :=
  regularFrameStructureCoefficientDerivativeContinuous period hPeriod metric
      derivative bracketFirst bracketSecond contracted *
    regularGeneralMetricC0MetricCoefficient period hPeriod metric variation
      metricRow metricColumn +
  regularFrameStructureCoefficientContinuous period hPeriod metric
      bracketFirst bracketSecond contracted *
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric variation
      derivative metricRow metricColumn

theorem regularFrameStructureMetricDerivativeTerm_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn :
      Fin 4) :
    ContDiff Real ∞
      (fun variation => regularFrameStructureMetricDerivativeTerm
        period hPeriod metric variation derivative bracketFirst bracketSecond
          contracted metricRow metricColumn) := by
  unfold regularFrameStructureMetricDerivativeTerm
  exact
    (contDiff_const.mul
      (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod metric
        metricRow metricColumn)).add
    (contDiff_const.mul
      (regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod
        metric derivative metricRow metricColumn))

/-- Derivative of the lowered Koszul coefficient. -/
def regularGeneralMetricC0KoszulLowerDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative first second lower : Fin 4) : C0Scalar period hPeriod :=
  (1 / 2 : Real) •
    (regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative first second lower +
      regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative second lower first -
      regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative lower first second -
      ∑ contracted : Fin 4,
        regularFrameStructureMetricDerivativeTerm period hPeriod metric
          variation derivative second lower contracted first contracted +
      ∑ contracted : Fin 4,
        regularFrameStructureMetricDerivativeTerm period hPeriod metric
          variation derivative lower first contracted second contracted +
      ∑ contracted : Fin 4,
        regularFrameStructureMetricDerivativeTerm period hPeriod metric
          variation derivative first second contracted lower contracted)

theorem regularGeneralMetricC0KoszulLowerDerivative_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Fin 4) :
    ContDiff Real ∞
      (fun variation => regularGeneralMetricC0KoszulLowerDerivative
        period hPeriod metric variation derivative first second lower) := by
  unfold regularGeneralMetricC0KoszulLowerDerivative
  apply ContDiff.const_smul
  apply ContDiff.add
  · apply ContDiff.add
    · apply ContDiff.sub
      · apply ContDiff.sub
        · exact (regularGeneralMetricC0MetricSecondDerivative_contDiff
            period hPeriod metric derivative first second lower).add
            (regularGeneralMetricC0MetricSecondDerivative_contDiff
              period hPeriod metric derivative second lower first)
        · exact regularGeneralMetricC0MetricSecondDerivative_contDiff
            period hPeriod metric derivative lower first second
      · apply ContDiff.sum
        intro contracted _
        exact regularFrameStructureMetricDerivativeTerm_contDiff
          period hPeriod metric derivative second lower contracted first
            contracted
    · apply ContDiff.sum
      intro contracted _
      exact regularFrameStructureMetricDerivativeTerm_contDiff
        period hPeriod metric derivative lower first contracted second
          contracted
  · apply ContDiff.sum
    intro contracted _
    exact regularFrameStructureMetricDerivativeTerm_contDiff
      period hPeriod metric derivative first second contracted lower contracted

/-- Exact regular-frame derivative `e_derivative Γ^upper_first,second`. -/
def regularGeneralMetricC0ChristoffelDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (derivative upper first second : Fin 4) : C0Scalar period hPeriod :=
  ∑ lower : Fin 4, (
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
        variation derivative upper lower *
      regularGeneralMetricC0KoszulLower period hPeriod metric variation
        first second lower +
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation upper lower *
      regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric
        variation derivative first second lower)

theorem regularGeneralMetricC0ChristoffelDerivative_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Fin 4) :
    ContDiffOn Real ∞
      (fun variation => regularGeneralMetricC0ChristoffelDerivative
        period hPeriod metric variation derivative upper first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0ChristoffelDerivative
  apply ContDiffOn.sum
  intro lower _
  exact
    ((regularGeneralMetricC0InverseMetricDerivative_contDiffOn period hPeriod
      metric derivative upper lower).mul
      (regularGeneralMetricC0KoszulLower_contDiff period hPeriod metric
        first second lower).contDiffOn).add
    ((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod
      metric upper lower).mul
      (regularGeneralMetricC0KoszulLowerDerivative_contDiff period hPeriod
        metric derivative first second lower).contDiffOn)

/-! ## Riemann, Ricci and scalar curvature -/

def regularGeneralMetricC0Riemann
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (upper lower first second : Fin 4) : C0Scalar period hPeriod :=
  regularGeneralMetricC0ChristoffelDerivative period hPeriod metric variation
      first upper second lower -
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric variation
      second upper first lower +
    ∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric variation
          contracted second lower *
        regularGeneralMetricC0Christoffel period hPeriod metric variation
          upper first contracted -
    ∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric variation
          contracted first lower *
        regularGeneralMetricC0Christoffel period hPeriod metric variation
          upper second contracted -
    ∑ contracted : Fin 4,
      regularFrameStructureCoefficientContinuous period hPeriod metric
          first second contracted *
        regularGeneralMetricC0Christoffel period hPeriod metric variation
          upper contracted lower

theorem regularGeneralMetricC0Riemann_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper lower first second : Fin 4) :
    ContDiffOn Real ∞
      (fun variation => regularGeneralMetricC0Riemann period hPeriod metric
        variation upper lower first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0Riemann
  apply ContDiffOn.sub
  · apply ContDiffOn.sub
    · apply ContDiffOn.add
      · exact
          (regularGeneralMetricC0ChristoffelDerivative_contDiffOn period hPeriod
            metric first upper second lower).sub
          (regularGeneralMetricC0ChristoffelDerivative_contDiffOn period hPeriod
            metric second upper first lower)
      · apply ContDiffOn.sum
        intro contracted _
        exact
          (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
            contracted second lower).mul
          (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
            upper first contracted)
    · apply ContDiffOn.sum
      intro contracted _
      exact
        (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
          contracted first lower).mul
        (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
          upper second contracted)
  · apply ContDiffOn.sum
    intro contracted _
    exact contDiffOn_const.mul
      (regularGeneralMetricC0Christoffel_contDiffOn period hPeriod metric
        upper contracted lower)

def regularGeneralMetricC0Ricci
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (first second : Fin 4) : C0Scalar period hPeriod :=
  ∑ contracted : Fin 4,
    regularGeneralMetricC0Riemann period hPeriod metric variation
      contracted first contracted second

theorem regularGeneralMetricC0Ricci_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) :
    ContDiffOn Real ∞
      (fun variation => regularGeneralMetricC0Ricci period hPeriod metric
        variation first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0Ricci
  apply ContDiffOn.sum
  intro contracted _
  exact regularGeneralMetricC0Riemann_contDiffOn period hPeriod metric
    contracted first contracted second

/-- General-metric scalar curvature in `C0`, built from exactly two spatial
derivatives of the C² metric core. -/
def regularGeneralMetricC0ScalarCurvature
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation first second *
      regularGeneralMetricC0Ricci period hPeriod metric variation first second

theorem regularGeneralMetricC0ScalarCurvature_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  exact
    ((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod
      metric first second).of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
          exact WithTop.coe_le_coe.mpr le_top)).mul
    ((regularGeneralMetricC0Ricci_contDiffOn period hPeriod metric
      first second).of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
          exact WithTop.coe_le_coe.mpr le_top))

/-! ## Fidelity of the regular frame at the physical metric -/

@[simp]
theorem regularGeneralMetricC0MetricCoefficient_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row column
        point =
      regularFrameMetricMatrix period hPeriod metric row column point := by
  rw [regularGeneralMetricC0MetricCoefficient_zero]
  rfl

@[simp]
theorem regularGeneralMetricC0MetricFirstDerivative_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        derivative row column point =
      frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column)
        point derivative := by
  rw [regularGeneralMetricC0MetricFirstDerivative_zero]
  rfl

@[simp]
theorem regularGeneralMetricC0MetricSecondDerivative_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
        outer inner row column point =
      frameSecondDerivative period hPeriod (RegularFrame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column)
        point outer inner := by
  rw [regularGeneralMetricC0MetricSecondDerivative_zero]
  rfl

@[simp]
theorem regularGeneralMetricC0InverseMetricCoefficient_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
        row column point =
      regularFrameMetricInverseMatrix period hPeriod metric row column point := by
  rw [regularGeneralMetricC0InverseMetricCoefficient_zero]
  rfl

/-- Coordinate representative of `∇_{e_first} e_second` in an arbitrary
holonomic chart. -/
def regularFrameLocalCovariantDerivativeVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Fin 4) (coordinate : CoordinateVector) :
    CoordinateVector :=
  fderiv Real
      (pulledRegularFrameVector period hPeriod metric patch second)
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate) +
    localLeviCivitaChristoffelApply period hPeriod metric.metric patch
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate)

theorem localMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate) =
      regularFrameMetricMatrix period hPeriod metric first second
        (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    coordinateMap_mfderiv_pulledRegularFrameVector]
  rfl

private theorem localMetricCoordinateForm_add_left
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CoordinateVector) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (first + second) third =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first third +
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          second third := by
  exact congrArg (fun form => form third)
    (map_add
      (localMetricCoordinateForm period hPeriod metric.metric patch coordinate)
      first second)

private theorem localMetricCoordinateForm_add_right
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CoordinateVector) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        first (second + third) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first second +
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first third := by
  exact map_add
    (localMetricCoordinateForm period hPeriod metric.metric patch coordinate
      first) second third

private theorem localMetricCoordinateForm_sub_left
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CoordinateVector) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (first - second) third =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first third -
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          second third := by
  exact congrArg (fun form => form third)
    (map_sub
      (localMetricCoordinateForm period hPeriod metric.metric patch coordinate)
      first second)

private theorem localMetricCoordinateForm_sub_right
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CoordinateVector) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        first (second - third) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first second -
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          first third := by
  exact map_sub
    (localMetricCoordinateForm period hPeriod metric.metric patch coordinate
      first) second third

private theorem localMetricCoordinateForm_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CoordinateVector) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        first second =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        second first := by
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  exact metric.metric.tensor.symmetric _ _ _

private theorem fderiv_localMetricCoordinateForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (derivative first second : Fin 4) :
    fderiv Real
        (fun current =>
          localMetricCoordinateForm period hPeriod metric.metric patch current
            (pulledRegularFrameVector period hPeriod metric patch first current)
            (pulledRegularFrameVector period hPeriod metric patch second current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric first second)
        (patch.coordinateMap coordinate) derivative := by
  have hFunction :
      (fun current =>
        localMetricCoordinateForm period hPeriod metric.metric patch current
          (pulledRegularFrameVector period hPeriod metric patch first current)
          (pulledRegularFrameVector period hPeriod metric patch second current)) =
        (regularFrameMetricMatrix period hPeriod metric first second).toFun ∘
          patch.coordinateMap := by
    funext current
    exact localMetricCoordinateForm_pulledRegularFrameVector period hPeriod
      metric patch current first second
  rw [hFunction]
  exact fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
    metric (regularFrameMetricMatrix period hPeriod metric first second)
    patch coordinate derivative

private theorem fderiv_localMetricCoordinateForm_pulledRegularFrameVector_expand
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (derivative first second : Fin 4) :
    fderiv Real
        (fun current =>
          localMetricCoordinateForm period hPeriod metric.metric patch current
            (pulledRegularFrameVector period hPeriod metric patch first current)
            (pulledRegularFrameVector period hPeriod metric patch second current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch first)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate))
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricDerivativeTrilinearForm period hPeriod metric.metric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch second)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate)) := by
  have hMatrix : DifferentiableAt Real
      (localMetricMatrix period hPeriod metric.metric patch) coordinate :=
    (localMetricMatrix_contDiff period hPeriod metric.metric patch)
      |>.differentiable (by simp) coordinate
  simpa only [localMetricCoordinateForm,
    localMetricDerivativeTrilinearForm_apply] using
    (fderiv_matrix_toBilin_dynamic_apply
      (localMetricMatrix period hPeriod metric.metric patch)
      (pulledRegularFrameVector period hPeriod metric patch first)
      (pulledRegularFrameVector period hPeriod metric patch second)
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate)
      hMatrix
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate first)
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate second))

theorem regularFrameLocalCovariantDerivative_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (derivative first second : Fin 4) :
    frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric first second)
        (patch.coordinateMap coordinate) derivative =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch derivative first coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) +
        localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch derivative second coordinate) := by
  rw [← fderiv_localMetricCoordinateForm_pulledRegularFrameVector period
    hPeriod metric patch coordinate derivative first second]
  rw [fderiv_localMetricCoordinateForm_pulledRegularFrameVector_expand]
  have hCompatibility := congrArg
    (fun form => form
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate)
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate))
    (localMetricDerivativeTrilinearForm_eq_leviCivita period hPeriod
      metric.metric patch coordinate)
  rw [hCompatibility]
  simp only [localLeviCivitaMetricCompatibilityForm_apply,
    localLeviCivitaChristoffelBilinearMap_apply,
    regularFrameLocalCovariantDerivativeVector]
  rw [localMetricCoordinateForm_add_left,
    localMetricCoordinateForm_add_right]
  abel

theorem regularFrameLocalCovariantDerivative_torsion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
        first second coordinate -
      regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
        second first coordinate =
      VectorField.lieBracket Real
        (pulledRegularFrameVector period hPeriod metric patch first)
        (pulledRegularFrameVector period hPeriod metric patch second)
        coordinate := by
  unfold regularFrameLocalCovariantDerivativeVector VectorField.lieBracket
  rw [localLeviCivitaChristoffelApply_symmetric period hPeriod metric.metric
    patch coordinate
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)]
  abel

theorem regularFrameLocalLieBracket_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    VectorField.lieBracket Real
        (pulledRegularFrameVector period hPeriod metric patch first)
        (pulledRegularFrameVector period hPeriod metric patch second)
        coordinate =
      ∑ upper : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second upper
            (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper coordinate := by
  let derivative := patch.coordinateMap_isLocalDiffeomorph
    |>.mfderivToContinuousLinearEquiv (by simp) coordinate
  apply derivative.injective
  calc
    derivative
        (VectorField.lieBracket (E := CoordinateVector) Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second)
          coordinate) =
        smoothGhostLieBracket period hPeriod
          (metric.frame first) (metric.frame second)
          (patch.coordinateMap coordinate) := by
      exact coordinateMap_mfderiv_lieBracket_pulledRegularFrameVector
        period hPeriod metric patch coordinate first second
    _ = ∑ upper : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
              upper (patch.coordinateMap coordinate) •
            metric.frame upper (patch.coordinateMap coordinate) := by
      exact regularFrameStructureCoefficient_reconstructs period hPeriod metric
        first second (patch.coordinateMap coordinate)
    _ = derivative
        (∑ upper : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
              upper (patch.coordinateMap coordinate) •
            pulledRegularFrameVector period hPeriod metric patch upper
              coordinate) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro upper _
      have hVector :
          derivative
              (pulledRegularFrameVector period hPeriod metric patch upper
                coordinate) =
            metric.frame upper (patch.coordinateMap coordinate) :=
        coordinateMap_mfderiv_pulledRegularFrameVector period hPeriod metric
          patch coordinate upper
      rw [← hVector]
      exact (map_smul derivative
        (regularFrameStructureCoefficient period hPeriod metric first second
          upper (patch.coordinateMap coordinate))
        (pulledRegularFrameVector period hPeriod metric patch upper
          coordinate)).symm

theorem regularFrameStructureMetricContraction_eq_localLieBracket
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (row first second : Fin 4) :
    (∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second upper
          (patch.coordinateMap coordinate) *
        regularFrameMetricMatrix period hPeriod metric row upper
          (patch.coordinateMap coordinate)) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch row coordinate)
        (VectorField.lieBracket Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second)
          coordinate) := by
  rw [regularFrameLocalLieBracket_eq_sum period hPeriod metric patch coordinate]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro upper _
  rw [map_smul]
  rw [localMetricCoordinateForm_pulledRegularFrameVector]
  rfl

theorem regularGeneralMetricC0KoszulLower_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second lower
        (patch.coordinateMap coordinate) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  unfold regularGeneralMetricC0KoszulLower
  change (1 / 2 : Real) *
      (regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            first second lower (patch.coordinateMap coordinate) +
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            second lower first (patch.coordinateMap coordinate) -
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            lower first second (patch.coordinateMap coordinate) -
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              second lower contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric 0
              first contracted (patch.coordinateMap coordinate) +
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              lower first contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric 0
              second contracted (patch.coordinateMap coordinate) +
        ∑ contracted : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              first second contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric 0
              lower contracted (patch.coordinateMap coordinate)) = _
  simp only [
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularFrameStructureCoefficientContinuous_apply,
    regularGeneralMetricC0MetricCoefficient_zero_apply]
  rw [regularFrameStructureMetricContraction_eq_localLieBracket period hPeriod
    metric patch coordinate first second lower]
  rw [regularFrameStructureMetricContraction_eq_localLieBracket period hPeriod
    metric patch coordinate second lower first]
  rw [regularFrameStructureMetricContraction_eq_localLieBracket period hPeriod
    metric patch coordinate lower first second]
  rw [regularFrameLocalCovariantDerivative_metricCompatible period hPeriod
    metric patch coordinate first second lower]
  rw [regularFrameLocalCovariantDerivative_metricCompatible period hPeriod
    metric patch coordinate second lower first]
  rw [regularFrameLocalCovariantDerivative_metricCompatible period hPeriod
    metric patch coordinate lower first second]
  rw [← regularFrameLocalCovariantDerivative_torsion period hPeriod metric patch
    coordinate second lower]
  rw [← regularFrameLocalCovariantDerivative_torsion period hPeriod metric patch
    coordinate lower first]
  rw [← regularFrameLocalCovariantDerivative_torsion period hPeriod metric patch
    coordinate first second]
  rw [localMetricCoordinateForm_sub_right,
    localMetricCoordinateForm_sub_right,
    localMetricCoordinateForm_sub_right]
  simp only [localMetricCoordinateForm_symmetric]
  ring

private theorem regularFrameMetricMatrix_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin 4) :
    regularFrameMetricMatrix period hPeriod metric first second point =
      regularFrameMetricMatrix period hPeriod metric second first point := by
  exact metric.metric.tensor.symmetric _ _ _

private theorem regularFrameLocalCovariantDerivative_metricPairing_mulVec
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      Matrix.mulVec
        (regularFrameMetricMatrixMap period hPeriod metric
          (patch.coordinateMap coordinate))
        ((pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch first second coordinate)) lower := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := regularFrameLocalCovariantDerivativeVector period hPeriod
    metric patch first second coordinate
  calc
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        connection
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (∑ upper : Fin 4, basis.repr connection upper • basis upper)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by rw [basis.sum_repr]
    _ = ∑ upper : Fin 4,
        basis.repr connection upper *
          regularFrameMetricMatrix period hPeriod metric upper lower
            (patch.coordinateMap coordinate) := by
      rw [map_sum]
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro upper _
      rw [map_smul]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [show basis upper =
          pulledRegularFrameVector period hPeriod metric patch upper coordinate by
        exact pulledRegularFrameBasis_apply period hPeriod metric patch
          coordinate upper]
      rw [localMetricCoordinateForm_pulledRegularFrameVector]
    _ = Matrix.mulVec
        (regularFrameMetricMatrixMap period hPeriod metric
          (patch.coordinateMap coordinate))
        (basis.repr connection) lower := by
      simp only [Matrix.mulVec, dotProduct, regularFrameMetricMatrixMap]
      apply Finset.sum_congr rfl
      intro upper _
      rw [regularFrameMetricMatrix_symmetric]
      ring

theorem regularGeneralMetricC0Christoffel_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper first second : Fin 4) :
    regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first second
        (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second coordinate) upper := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := regularFrameLocalCovariantDerivativeVector period hPeriod
    metric patch first second coordinate
  unfold regularGeneralMetricC0Christoffel
  change (∑ lower : Fin 4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          upper lower (patch.coordinateMap coordinate) *
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap coordinate)) = basis.repr connection upper
  simp_rw [regularGeneralMetricC0InverseMetricCoefficient_zero_apply]
  simp_rw [regularGeneralMetricC0KoszulLower_zero_apply period hPeriod metric
    patch coordinate first second]
  simp_rw [regularFrameLocalCovariantDerivative_metricPairing_mulVec period
    hPeriod metric patch coordinate first second]
  change Matrix.mulVec
      (regularFrameMetricInverseMatrixMap period hPeriod metric
        (patch.coordinateMap coordinate))
      (Matrix.mulVec
        (regularFrameMetricMatrixMap period hPeriod metric
          (patch.coordinateMap coordinate))
        (basis.repr connection)) upper = basis.repr connection upper
  rw [Matrix.mulVec_mulVec]
  have hProduct :
      regularFrameMetricInverseMatrixMap period hPeriod metric
            (patch.coordinateMap coordinate) *
          regularFrameMetricMatrixMap period hPeriod metric
            (patch.coordinateMap coordinate) = 1 := by
    exact Matrix.nonsing_inv_mul
      (regularFrameMetricMatrixMap period hPeriod metric
        (patch.coordinateMap coordinate))
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric
          (patch.coordinateMap coordinate)))
  rw [hProduct, Matrix.one_mulVec]

theorem regularGeneralMetricC0Christoffel_zero_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    (∑ upper : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
          second (patch.coordinateMap coordinate) •
        pulledRegularFrameVector period hPeriod metric patch upper coordinate) =
      regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
        first second coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection := regularFrameLocalCovariantDerivativeVector period hPeriod
    metric patch first second coordinate
  simp_rw [regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
    patch coordinate]
  calc
    (∑ upper : Fin 4,
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
          connection upper •
        pulledRegularFrameVector period hPeriod metric patch upper coordinate) =
        ∑ upper : Fin 4, basis.repr connection upper • basis upper := by
      apply Finset.sum_congr rfl
      intro upper _
      congr 1
      exact (pulledRegularFrameBasis_apply period hPeriod metric patch
        coordinate upper).symm
    _ = connection := basis.sum_repr connection

private theorem fderiv_regularFrameMetricMatrix_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (derivative row column : Fin 4) :
    fderiv Real
        (fun current => regularFrameMetricMatrix period hPeriod metric row column
          (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        derivative row column (patch.coordinateMap coordinate) := by
  rw [regularGeneralMetricC0MetricFirstDerivative_zero_apply]
  convert
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (regularFrameMetricMatrix period hPeriod metric row column) patch
      coordinate derivative) using 1 <;> rfl

private theorem fderiv_regularGeneralMetricC0MetricFirstDerivative_zero_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (outer inner row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            inner row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch outer coordinate) =
      regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
        outer inner row column (patch.coordinateMap coordinate) := by
  have hFunction :
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
          inner row column (patch.coordinateMap current)) =
        (frameDerivativeComponentField period hPeriod
          (RegularFrame period hPeriod metric)
          (regularFrameMetricMatrix period hPeriod metric row column) inner).toFun
            ∘ patch.coordinateMap := by
    funext current
    exact regularGeneralMetricC0MetricFirstDerivative_zero_apply period hPeriod
      metric inner row column (patch.coordinateMap current)
  rw [hFunction]
  rw [regularGeneralMetricC0MetricSecondDerivative_zero_apply]
  simpa only [frameSecondDerivative] using
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (frameDerivativeComponentField period hPeriod
        (RegularFrame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column) inner)
      patch coordinate outer)

private theorem fderiv_regularFrameStructureCoefficient_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second upper : Fin 4) :
    fderiv Real
        (fun current =>
          regularFrameStructureCoefficientContinuous period hPeriod metric
            first second upper (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureCoefficientDerivativeContinuous period hPeriod
        metric derivative first second upper
        (patch.coordinateMap coordinate) := by
  change fderiv Real
      ((regularFrameStructureCoefficient period hPeriod metric first second
        upper).toFun ∘ patch.coordinateMap) coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) =
    frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
      (regularFrameStructureCoefficient period hPeriod metric first second upper)
      (patch.coordinateMap coordinate) derivative
  convert
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (regularFrameStructureCoefficient period hPeriod metric first second
        upper) patch coordinate derivative) using 1 <;> rfl

private theorem fderiv_regularFrameMetricInverseMatrix_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (derivative row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularFrameMetricInverseMatrix period hPeriod metric row column
            (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
        derivative row column (patch.coordinateMap coordinate) := by
  let matrix : CoordinateVector → CoordinateMatrix := fun current =>
    regularFrameMetricMatrixMap period hPeriod metric
      (patch.coordinateMap current)
  let inverse : CoordinateVector → CoordinateMatrix := fun current =>
    regularFrameMetricInverseMatrixMap period hPeriod metric
      (patch.coordinateMap current)
  have hMatrixContDiff : ContDiff Real ∞ matrix := by
    exact ((regularFrameMetricMatrixMap_contMDiff period hPeriod metric).comp
      patch.coordinateMap_contMDiff).contDiff
  have hInverseContDiff : ContDiff Real ∞ inverse := by
    exact
      ((regularFrameMetricInverseMatrixMap_contMDiff period hPeriod metric).comp
        patch.coordinateMap_contMDiff).contDiff
  have hMatrix : DifferentiableAt Real matrix coordinate :=
    hMatrixContDiff.differentiable (by simp) coordinate
  have hInverse : DifferentiableAt Real inverse coordinate :=
    hInverseContDiff.differentiable (by simp) coordinate
  have hMatrixDerivative :
      fderiv Real matrix coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        fun currentRow currentColumn =>
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            derivative currentRow currentColumn
            (patch.coordinateMap coordinate) := by
    ext currentRow currentColumn
    rw [← fderiv_matrix_entry_apply matrix coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) hMatrix currentRow currentColumn]
    simpa only [matrix, regularFrameMetricMatrixMap] using
      (fderiv_regularFrameMetricMatrix_local period hPeriod metric patch
        coordinate derivative currentRow currentColumn)
  have hFunction : inverse = Ring.inverse ∘ matrix := by
    funext current
    change (regularFrameMetricMatrixMap period hPeriod metric
      (patch.coordinateMap current))⁻¹ =
        Ring.inverse (regularFrameMetricMatrixMap period hPeriod metric
          (patch.coordinateMap current))
    exact Matrix.nonsing_inv_eq_ringInverse
      (A := regularFrameMetricMatrixMap period hPeriod metric
        (patch.coordinateMap current))
  let unitMetric : CoordinateMatrixˣ :=
    (regularFrameMetricMatrix_isUnit period hPeriod metric
      (patch.coordinateMap coordinate)).unit
  have hUnitSpec : (unitMetric : CoordinateMatrix) = matrix coordinate :=
    (regularFrameMetricMatrix_isUnit period hPeriod metric
      (patch.coordinateMap coordinate)).unit_spec
  have hInverseDerivative :
      fderiv Real inverse coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        -(inverse coordinate *
            fderiv Real matrix coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) *
            inverse coordinate) := by
    rw [hFunction]
    have hDerivative :=
      ((hasFDerivAt_ringInverse (𝕜 := Real) unitMetric).comp coordinate
        hMatrix.hasFDerivAt).fderiv
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] CoordinateMatrix =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hDerivative
    have hUnitInverse :
        (↑(unitMetric⁻¹) : CoordinateMatrix) =
          Ring.inverse (matrix coordinate) := by
      calc
        (↑(unitMetric⁻¹) : CoordinateMatrix) =
            Ring.inverse (unitMetric : CoordinateMatrix) :=
          (Ring.inverse_unit unitMetric).symm
        _ = Ring.inverse (matrix coordinate) := by rw [hUnitSpec]
    rw [hUnitInverse] at hApplied
    change fderiv Real (Ring.inverse ∘ matrix) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      -(Ring.inverse (matrix coordinate) *
        fderiv Real matrix coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) *
        Ring.inverse (matrix coordinate)) at hApplied
    exact hApplied
  calc
    fderiv Real
        (fun current =>
          regularFrameMetricInverseMatrix period hPeriod metric row column
            (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      fderiv Real inverse coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) row column := by
        simpa only [inverse, regularFrameMetricInverseMatrix] using
          (fderiv_matrix_entry_apply inverse coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate) hInverse row column)
    _ = (-(inverse coordinate *
          fderiv Real matrix coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate) *
          inverse coordinate)) row column := by rw [hInverseDerivative]
    _ = regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
        derivative row column (patch.coordinateMap coordinate) := by
      rw [hMatrixDerivative]
      unfold regularGeneralMetricC0InverseMetricDerivative
      change _ =
        -(∑ first : Fin 4, ∑ second : Fin 4,
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod
              metric 0 row first (patch.coordinateMap coordinate) *
            regularGeneralMetricC0MetricFirstDerivative period hPeriod
              metric 0 derivative first second
                (patch.coordinateMap coordinate) *
            regularGeneralMetricC0InverseMetricCoefficient period hPeriod
              metric 0 second column (patch.coordinateMap coordinate))
      simp only [regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
        regularGeneralMetricC0MetricFirstDerivative_zero_apply]
      dsimp only [inverse]
      change
        (-((regularFrameMetricInverseMatrixMap period hPeriod metric
              (patch.coordinateMap coordinate) *
            (show CoordinateMatrix from fun currentRow currentColumn =>
              frameDerivative period hPeriod Real
                (RegularFrame period hPeriod metric)
                (regularFrameMetricMatrix period hPeriod metric currentRow
                  currentColumn)
                (patch.coordinateMap coordinate) derivative) *
            regularFrameMetricInverseMatrixMap period hPeriod metric
              (patch.coordinateMap coordinate)) row column)) =
          -(∑ first : Fin 4, ∑ second : Fin 4,
            regularFrameMetricInverseMatrixMap period hPeriod metric
                (patch.coordinateMap coordinate) row first *
              frameDerivative period hPeriod Real
                (RegularFrame period hPeriod metric)
                (regularFrameMetricMatrix period hPeriod metric first second)
                (patch.coordinateMap coordinate) derivative *
              regularFrameMetricInverseMatrixMap period hPeriod metric
                (patch.coordinateMap coordinate) second column)
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]

private theorem fderiv_regularFrameStructureMetricProduct_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative bracketFirst bracketSecond contracted row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularFrameStructureCoefficientContinuous period hPeriod metric
              bracketFirst bracketSecond contracted
                (patch.coordinateMap current) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric 0
              row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
        derivative bracketFirst bracketSecond contracted row column
        (patch.coordinateMap coordinate) := by
  let structureField :=
    regularFrameStructureCoefficient period hPeriod metric bracketFirst
      bracketSecond contracted
  let metricField := regularFrameMetricMatrix period hPeriod metric row column
  have hStructure : DifferentiableAt Real
      (structureField.toFun ∘ patch.coordinateMap) coordinate :=
    ((((structureField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
      patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp)).differentiableAt)
  have hMetric : DifferentiableAt Real
      (metricField.toFun ∘ patch.coordinateMap) coordinate :=
    ((((metricField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
      patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp)).differentiableAt)
  have hFunction :
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row
            column (patch.coordinateMap current)) =
        (structureField.toFun ∘ patch.coordinateMap) *
          (metricField.toFun ∘ patch.coordinateMap) := by
    funext current
    simp only [structureField, metricField,
      regularFrameStructureCoefficientContinuous_apply,
      regularGeneralMetricC0MetricCoefficient_zero_apply,
      Function.comp_apply, Pi.mul_apply]
  rw [hFunction]
  change fderiv Real
      ((structureField.toFun ∘ patch.coordinateMap) *
        (metricField.toFun ∘ patch.coordinateMap)) coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) = _
  rw [fderiv_mul hStructure hMetric]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [show fderiv Real (structureField.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureCoefficientDerivativeContinuous period hPeriod
        metric derivative bracketFirst bracketSecond contracted
          (patch.coordinateMap coordinate) by
    exact fderiv_regularFrameStructureCoefficient_local period hPeriod metric
      patch coordinate derivative bracketFirst bracketSecond contracted]
  rw [show fderiv Real (metricField.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        derivative row column (patch.coordinateMap coordinate) by
    exact fderiv_regularFrameMetricMatrix_local period hPeriod metric patch
      coordinate derivative row column]
  unfold regularFrameStructureMetricDerivativeTerm
  change _ =
    regularFrameStructureCoefficientDerivativeContinuous period hPeriod metric
          derivative bracketFirst bracketSecond contracted
          (patch.coordinateMap coordinate) *
        regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row
          column (patch.coordinateMap coordinate) +
      regularFrameStructureCoefficientContinuous period hPeriod metric
          bracketFirst bracketSecond contracted (patch.coordinateMap coordinate) *
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
          derivative row column (patch.coordinateMap coordinate)
  simp only [regularGeneralMetricC0MetricCoefficient_zero_apply,
    regularFrameStructureCoefficientContinuous_apply]
  dsimp only [structureField, metricField, Function.comp_apply]
  ring

private theorem regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (inner row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
          inner row column (patch.coordinateMap current)) coordinate := by
  let field := frameDerivativeComponentField period hPeriod
    (RegularFrame period hPeriod metric)
    (regularFrameMetricMatrix period hPeriod metric row column) inner
  have hFunction :
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
          inner row column (patch.coordinateMap current)) =
        field.toFun ∘ patch.coordinateMap := by
    funext current
    exact regularGeneralMetricC0MetricFirstDerivative_zero_apply period hPeriod
      metric inner row column (patch.coordinateMap current)
  rw [hFunction]
  exact ((((field.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
    patch.coordinateMap_contMDiff).contDiff.differentiable
      (by simp)).differentiableAt)

private theorem regularFrameStructureMetricProduct_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (bracketFirst bracketSecond contracted row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row
            column (patch.coordinateMap current)) coordinate := by
  let structureField :=
    regularFrameStructureCoefficient period hPeriod metric bracketFirst
      bracketSecond contracted
  let metricField := regularFrameMetricMatrix period hPeriod metric row column
  have hFunction :
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row
            column (patch.coordinateMap current)) =
        (structureField.toFun ∘ patch.coordinateMap) *
          (metricField.toFun ∘ patch.coordinateMap) := by
    funext current
    simp only [structureField, metricField,
      regularFrameStructureCoefficientContinuous_apply,
      regularGeneralMetricC0MetricCoefficient_zero_apply,
      Function.comp_apply, Pi.mul_apply]
  rw [hFunction]
  exact
    (((((structureField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff.differentiable
          (by simp)).differentiableAt).mul
      ((((metricField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff.differentiable
          (by simp)).differentiableAt))

private theorem fderiv_regularGeneralMetricC0KoszulLower_zero_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second lower : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0KoszulLower period hPeriod metric 0 first
            second lower (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric 0
        derivative first second lower (patch.coordinateMap coordinate) := by
  let metricTerm (inner row column : Fin 4) : CoordinateVector → Real :=
    fun current =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        inner row column (patch.coordinateMap current)
  let structureTerm
      (bracketFirst bracketSecond contracted row column : Fin 4) :
      CoordinateVector → Real := fun current =>
    regularFrameStructureCoefficientContinuous period hPeriod metric
        bracketFirst bracketSecond contracted (patch.coordinateMap current) *
      regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row column
        (patch.coordinateMap current)
  let firstMetric := metricTerm first second lower
  let secondMetric := metricTerm second lower first
  let thirdMetric := metricTerm lower first second
  let firstStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm second lower contracted first contracted current
  let secondStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm lower first contracted second contracted current
  let thirdStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm first second contracted lower contracted current
  let firstPair := firstMetric + secondMetric
  let subtractMetric := firstPair - thirdMetric
  let subtractStructure := subtractMetric - firstStructure
  let addSecondStructure := subtractStructure + secondStructure
  let inside := addSecondStructure + thirdStructure
  have hFirstMetric : DifferentiableAt Real firstMetric coordinate := by
    exact regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate first second lower
  have hSecondMetric : DifferentiableAt Real secondMetric coordinate := by
    exact regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate second lower first
  have hThirdMetric : DifferentiableAt Real thirdMetric coordinate := by
    exact regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate lower first second
  have hFirstStructure : DifferentiableAt Real firstStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate second lower contracted first contracted
  have hSecondStructure : DifferentiableAt Real secondStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate lower first contracted second contracted
  have hThirdStructure : DifferentiableAt Real thirdStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate first second contracted lower contracted
  have hFirstPair : DifferentiableAt Real firstPair coordinate :=
    hFirstMetric.add hSecondMetric
  have hSubtractMetric : DifferentiableAt Real subtractMetric coordinate :=
    hFirstPair.sub hThirdMetric
  have hSubtractStructure : DifferentiableAt Real subtractStructure coordinate :=
    hSubtractMetric.sub hFirstStructure
  have hAddSecondStructure : DifferentiableAt Real addSecondStructure coordinate :=
    hSubtractStructure.add hSecondStructure
  have hInside : DifferentiableAt Real inside coordinate :=
    hAddSecondStructure.add hThirdStructure
  have hFirstStructureDerivative :
      fderiv Real firstStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
            derivative second lower contracted first contracted
            (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_local_differentiableAt period
          hPeriod metric patch coordinate second lower contracted first
            contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real firstStructure coordinate _ = _
    rw [hApplied]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_local period hPeriod metric
      patch coordinate derivative second lower contracted first contracted
  have hSecondStructureDerivative :
      fderiv Real secondStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
            derivative lower first contracted second contracted
            (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_local_differentiableAt period
          hPeriod metric patch coordinate lower first contracted second
            contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real secondStructure coordinate _ = _
    rw [hApplied]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_local period hPeriod metric
      patch coordinate derivative lower first contracted second contracted
  have hThirdStructureDerivative :
      fderiv Real thirdStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
            derivative first second contracted lower contracted
            (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_local_differentiableAt period
          hPeriod metric patch coordinate first second contracted lower
            contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real thirdStructure coordinate _ = _
    rw [hApplied]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_local period hPeriod metric
      patch coordinate derivative first second contracted lower contracted
  have hFirstPairDerivative :
      fderiv Real firstPair coordinate =
        fderiv Real firstMetric coordinate +
          fderiv Real secondMetric coordinate := by
    exact fderiv_add hFirstMetric hSecondMetric
  have hSubtractMetricDerivative :
      fderiv Real subtractMetric coordinate =
        fderiv Real firstPair coordinate -
          fderiv Real thirdMetric coordinate := by
    exact fderiv_sub hFirstPair hThirdMetric
  have hSubtractStructureDerivative :
      fderiv Real subtractStructure coordinate =
        fderiv Real subtractMetric coordinate -
          fderiv Real firstStructure coordinate := by
    exact fderiv_sub hSubtractMetric hFirstStructure
  have hAddSecondStructureDerivative :
      fderiv Real addSecondStructure coordinate =
        fderiv Real subtractStructure coordinate +
          fderiv Real secondStructure coordinate := by
    exact fderiv_add hSubtractStructure hSecondStructure
  have hInsideDerivative :
      fderiv Real inside coordinate =
        fderiv Real addSecondStructure coordinate +
          fderiv Real thirdStructure coordinate := by
    exact fderiv_add hAddSecondStructure hThirdStructure
  have hInsideApplied :
      fderiv Real inside coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
              derivative first second lower (patch.coordinateMap coordinate) +
          regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
              derivative second lower first (patch.coordinateMap coordinate) -
          regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
              derivative lower first second (patch.coordinateMap coordinate) -
          (∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
              derivative second lower contracted first contracted
              (patch.coordinateMap coordinate)) +
          (∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
              derivative lower first contracted second contracted
              (patch.coordinateMap coordinate)) +
          ∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric 0
              derivative first second contracted lower contracted
              (patch.coordinateMap coordinate) := by
    rw [hInsideDerivative, add_apply, hAddSecondStructureDerivative, add_apply,
      hSubtractStructureDerivative, sub_apply, hSubtractMetricDerivative,
      sub_apply, hFirstPairDerivative, add_apply]
    rw [show fderiv Real firstMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
          derivative first second lower (patch.coordinateMap coordinate) by
      exact fderiv_regularGeneralMetricC0MetricFirstDerivative_zero_local
        period hPeriod metric patch coordinate derivative first second lower]
    rw [show fderiv Real secondMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
          derivative second lower first (patch.coordinateMap coordinate) by
      exact fderiv_regularGeneralMetricC0MetricFirstDerivative_zero_local
        period hPeriod metric patch coordinate derivative second lower first]
    rw [show fderiv Real thirdMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric 0
          derivative lower first second (patch.coordinateMap coordinate) by
      exact fderiv_regularGeneralMetricC0MetricFirstDerivative_zero_local
        period hPeriod metric patch coordinate derivative lower first second]
    rw [hFirstStructureDerivative, hSecondStructureDerivative,
      hThirdStructureDerivative]
  have hFunction :
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) =
        fun current => (1 / 2 : Real) * inside current := by
    funext current
    unfold regularGeneralMetricC0KoszulLower
    change (1 / 2 : Real) *
        (metricTerm first second lower current +
          metricTerm second lower first current -
          metricTerm lower first second current -
          (∑ contracted : Fin 4,
            structureTerm second lower contracted first contracted current) +
          (∑ contracted : Fin 4,
            structureTerm lower first contracted second contracted current) +
          ∑ contracted : Fin 4,
            structureTerm first second contracted lower contracted current) = _
    rfl
  rw [hFunction]
  have hScaledDerivative :
      fderiv Real (fun current => (1 / 2 : Real) * inside current) coordinate =
        (1 / 2 : Real) • fderiv Real inside coordinate := by
    change fderiv Real ((1 / 2 : Real) • inside) coordinate = _
    exact congrFun
      (fderiv_const_smul_field (𝕜 := Real) (R := Real) (f := inside)
        (1 / 2 : Real)) coordinate
  rw [hScaledDerivative]
  simp only [smul_apply, smul_eq_mul]
  rw [hInsideApplied]
  unfold regularGeneralMetricC0KoszulLowerDerivative
  change (1 / 2 : Real) * _ = (1 / 2 : Real) * _
  rfl

private theorem regularFrameMetricInverseCoefficient_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularFrameMetricInverseMatrix period hPeriod metric row column
          (patch.coordinateMap current)) coordinate := by
  let inverse : CoordinateVector → CoordinateMatrix := fun current =>
    regularFrameMetricInverseMatrixMap period hPeriod metric
      (patch.coordinateMap current)
  have hInverse : DifferentiableAt Real inverse coordinate :=
    (((regularFrameMetricInverseMatrixMap_contMDiff period hPeriod metric).comp
      patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp)).differentiableAt
  simpa only [inverse, regularFrameMetricInverseMatrix] using
    (differentiableAt_pi.mp (differentiableAt_pi.mp hInverse row) column)

private theorem regularGeneralMetricC0KoszulLower_zero_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) coordinate := by
  let metricTerm (inner row column : Fin 4) : CoordinateVector → Real :=
    fun current =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        inner row column (patch.coordinateMap current)
  let structureTerm
      (bracketFirst bracketSecond contracted row column : Fin 4) :
      CoordinateVector → Real := fun current =>
    regularFrameStructureCoefficientContinuous period hPeriod metric
        bracketFirst bracketSecond contracted (patch.coordinateMap current) *
      regularGeneralMetricC0MetricCoefficient period hPeriod metric 0 row column
        (patch.coordinateMap current)
  let firstStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm second lower contracted first contracted current
  let secondStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm lower first contracted second contracted current
  let thirdStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm first second contracted lower contracted current
  let inside : CoordinateVector → Real := fun current =>
    metricTerm first second lower current +
      metricTerm second lower first current -
      metricTerm lower first second current -
      firstStructure current + secondStructure current + thirdStructure current
  have hFirstMetric : DifferentiableAt Real
      (metricTerm first second lower) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate first second lower
  have hSecondMetric : DifferentiableAt Real
      (metricTerm second lower first) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate second lower first
  have hThirdMetric : DifferentiableAt Real
      (metricTerm lower first second) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_zero_local_differentiableAt
      period hPeriod metric patch coordinate lower first second
  have hFirstStructure : DifferentiableAt Real firstStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate second lower contracted first contracted
  have hSecondStructure : DifferentiableAt Real secondStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate lower first contracted second contracted
  have hThirdStructure : DifferentiableAt Real thirdStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_local_differentiableAt period
      hPeriod metric patch coordinate first second contracted lower contracted
  have hInside : DifferentiableAt Real inside coordinate :=
    (((hFirstMetric.add hSecondMetric).sub hThirdMetric).sub hFirstStructure).add
      hSecondStructure |>.add hThirdStructure
  have hFunction :
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) =
        fun current => (1 / 2 : Real) * inside current := by
    funext current
    unfold regularGeneralMetricC0KoszulLower
    change (1 / 2 : Real) *
        (metricTerm first second lower current +
          metricTerm second lower first current -
          metricTerm lower first second current - firstStructure current +
          secondStructure current + thirdStructure current) = _
    rfl
  rw [hFunction]
  exact hInside.const_mul (1 / 2 : Real)

private theorem fderiv_regularGeneralMetricC0Christoffel_zero_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative upper first second : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
            second (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
        derivative upper first second (patch.coordinateMap coordinate) := by
  let inverseTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularFrameMetricInverseMatrix period hPeriod metric upper lower
      (patch.coordinateMap current)
  let koszulTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second lower
      (patch.coordinateMap current)
  let productTerm (lower : Fin 4) : CoordinateVector → Real :=
    inverseTerm lower * koszulTerm lower
  let christoffel : CoordinateVector → Real := fun current =>
    ∑ lower : Fin 4, productTerm lower current
  have hInverse (lower : Fin 4) :
      DifferentiableAt Real (inverseTerm lower) coordinate :=
    regularFrameMetricInverseCoefficient_local_differentiableAt period hPeriod
      metric patch coordinate upper lower
  have hKoszul (lower : Fin 4) :
      DifferentiableAt Real (koszulTerm lower) coordinate :=
    regularGeneralMetricC0KoszulLower_zero_local_differentiableAt period hPeriod
      metric patch coordinate first second lower
  have hProduct (lower : Fin 4) :
      DifferentiableAt Real (productTerm lower) coordinate :=
    (hInverse lower).mul (hKoszul lower)
  have hProductDerivative (lower : Fin 4) :
      fderiv Real (productTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
              derivative upper lower (patch.coordinateMap coordinate) *
            regularGeneralMetricC0KoszulLower period hPeriod metric 0 first
              second lower (patch.coordinateMap coordinate) +
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
              upper lower (patch.coordinateMap coordinate) *
            regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric 0
              derivative first second lower
                (patch.coordinateMap coordinate) := by
    have hDerivative := fderiv_mul (hInverse lower) (hKoszul lower)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hDerivative
    change fderiv Real (productTerm lower) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show fderiv Real (inverseTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
          derivative upper lower (patch.coordinateMap coordinate) by
      exact fderiv_regularFrameMetricInverseMatrix_local period hPeriod metric
        patch coordinate derivative upper lower]
    rw [show fderiv Real (koszulTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric 0
          derivative first second lower (patch.coordinateMap coordinate) by
      exact fderiv_regularGeneralMetricC0KoszulLower_zero_local period hPeriod
        metric patch coordinate derivative first second lower]
    simp only [inverseTerm, koszulTerm,
      regularGeneralMetricC0InverseMetricCoefficient_zero_apply]
    ring
  have hFunction :
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
          second (patch.coordinateMap current)) = christoffel := by
    funext current
    unfold regularGeneralMetricC0Christoffel
    change (∑ lower : Fin 4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          upper lower (patch.coordinateMap current) *
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) = _
    simp only [regularGeneralMetricC0InverseMetricCoefficient_zero_apply]
    rfl
  rw [hFunction]
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun lower _ => hProduct lower)
  have hApplied := congrArg
    (fun derivativeMap : CoordinateVector →L[Real] Real =>
      derivativeMap
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) hSum
  change fderiv Real christoffel coordinate _ = _
  rw [hApplied]
  simp only [sum_apply]
  unfold regularGeneralMetricC0ChristoffelDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  exact hProductDerivative lower

/-- Coordinate covariant derivative of one vector field along another. -/
private def localCovariantDerivativeVectorField
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : CoordinateVector → CoordinateVector)
    (coordinate : CoordinateVector) : CoordinateVector :=
  fderiv Real second coordinate (first coordinate) +
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
      (first coordinate) (second coordinate)

private theorem localLeviCivitaChristoffelApply_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : CoordinateVector) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        (first + second) vector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          first vector +
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          second vector := by
  change localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
      coordinate (first + second) vector = _
  rw [map_add]
  rw [LinearMap.add_apply]
  rfl

private theorem localLeviCivitaChristoffelApply_sub_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : CoordinateVector) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        (first - second) vector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          first vector -
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          second vector := by
  change localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
      coordinate (first - second) vector = _
  rw [map_sub]
  rw [LinearMap.sub_apply]
  rfl

private theorem localLeviCivitaChristoffelApply_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second third : CoordinateVector) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        first (second + third) =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          first second +
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          first third := by
  change localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
      coordinate first (second + third) = _
  rw [map_add]
  simp only [localLeviCivitaChristoffelBilinearMap_apply]

/-- Curvature computed with moving vector fields is the intrinsic coordinate
Riemann vector.  The only second-derivative input is Mathlib's commutator
identity for a `C²` vector field. -/
private theorem localCovariantDerivativeVectorField_curvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (first second vector : CoordinateVector → CoordinateVector)
    (hFirst : DifferentiableAt Real first coordinate)
    (hSecond : DifferentiableAt Real second coordinate)
    (hVector : ContDiff Real ∞ vector) :
    localCovariantDerivativeVectorField period hPeriod metric patch first
          (localCovariantDerivativeVectorField period hPeriod metric patch
            second vector) coordinate -
        localCovariantDerivativeVectorField period hPeriod metric patch second
          (localCovariantDerivativeVectorField period hPeriod metric patch
            first vector) coordinate -
        localCovariantDerivativeVectorField period hPeriod metric patch
          (VectorField.lieBracket Real first second) vector coordinate =
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (first coordinate) (second coordinate) (vector coordinate) := by
  have hVectorDifferentiable : DifferentiableAt Real vector coordinate :=
    hVector.differentiable (by simp) coordinate
  have hFDeriv : DifferentiableAt Real (fderiv Real vector) coordinate :=
    ((hVector.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp)).differentiableAt
  have hDerivativeSecond : DifferentiableAt Real
      (fun current => fderiv Real vector current (second current))
      coordinate :=
    hFDeriv.clm_apply hSecond
  have hDerivativeFirst : DifferentiableAt Real
      (fun current => fderiv Real vector current (first current))
      coordinate :=
    hFDeriv.clm_apply hFirst
  have hConnectionSecond : DifferentiableAt Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch current
          (second current) (vector current)) coordinate :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      patch id second vector coordinate differentiableAt_id hSecond
        hVectorDifferentiable
  have hConnectionFirst : DifferentiableAt Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch current
          (first current) (vector current)) coordinate :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      patch id first vector coordinate differentiableAt_id hFirst
        hVectorDifferentiable
  have hCovariantSecond :
      fderiv Real
          (fun current =>
            fderiv Real vector current (second current) +
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (second current) (vector current)) coordinate =
        fderiv Real
            (fun current => fderiv Real vector current (second current))
            coordinate +
          fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (second current) (vector current)) coordinate :=
    fderiv_add hDerivativeSecond hConnectionSecond
  have hCovariantFirst :
      fderiv Real
          (fun current =>
            fderiv Real vector current (first current) +
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (first current) (vector current)) coordinate =
        fderiv Real
            (fun current => fderiv Real vector current (first current))
            coordinate +
          fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (first current) (vector current)) coordinate :=
    fderiv_add hDerivativeFirst hConnectionFirst
  have hDynamicSecond :=
    fderiv_localLeviCivitaChristoffelApply_dynamic period hPeriod metric patch
      id second vector coordinate (first coordinate) differentiableAt_id
        hSecond hVectorDifferentiable
  have hDynamicFirst :=
    fderiv_localLeviCivitaChristoffelApply_dynamic period hPeriod metric patch
      id first vector coordinate (second coordinate) differentiableAt_id
        hFirst hVectorDifferentiable
  have hDynamicSecondClean :
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric patch current
              (second current) (vector current)) coordinate (first coordinate) =
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
              (fderiv Real second coordinate (first coordinate))
              (vector coordinate) +
          fderiv Real
              (fun current =>
                localLeviCivitaChristoffelApply period hPeriod metric patch
                  current (second coordinate) (vector coordinate))
              coordinate (first coordinate) +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (second coordinate)
            (fderiv Real vector coordinate (first coordinate)) := by
    simpa only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] using
      hDynamicSecond
  have hDynamicFirstClean :
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric patch current
              (first current) (vector current)) coordinate (second coordinate) =
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
              (fderiv Real first coordinate (second coordinate))
              (vector coordinate) +
          fderiv Real
              (fun current =>
                localLeviCivitaChristoffelApply period hPeriod metric patch
                  current (first coordinate) (vector coordinate))
              coordinate (second coordinate) +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (first coordinate)
            (fderiv Real vector coordinate (second coordinate)) := by
    simpa only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] using
      hDynamicFirst
  have hBracketDerivative :=
    VectorField.fderiv_apply_lieBracket
      (𝕜 := Real) (f := vector) (V := first) (W := second)
      hVector.contDiffAt
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
        hSecond hFirst
  unfold localCovariantDerivativeVectorField
  rw [hCovariantSecond, hCovariantFirst]
  simp only [add_apply]
  rw [hDynamicSecondClean, hDynamicFirstClean]
  rw [localLeviCivitaChristoffelApply_add_right,
    localLeviCivitaChristoffelApply_add_right]
  rw [hBracketDerivative]
  unfold VectorField.lieBracket
  rw [localLeviCivitaChristoffelApply_sub_left]
  unfold localLeviCivitaRiemannVector
  abel

private theorem regularGeneralMetricC0Christoffel_zero_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper first second : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
          second (patch.coordinateMap current)) coordinate := by
  let inverseTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularFrameMetricInverseMatrix period hPeriod metric upper lower
      (patch.coordinateMap current)
  let koszulTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second lower
      (patch.coordinateMap current)
  have hFunction :
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
          second (patch.coordinateMap current)) =
        fun current => ∑ lower : Fin 4,
          inverseTerm lower current * koszulTerm lower current := by
    funext current
    unfold regularGeneralMetricC0Christoffel
    change (∑ lower : Fin 4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          upper lower (patch.coordinateMap current) *
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) = _
    simp only [regularGeneralMetricC0InverseMetricCoefficient_zero_apply]
    rfl
  rw [hFunction]
  apply DifferentiableAt.fun_sum
  intro lower _
  exact
    (regularFrameMetricInverseCoefficient_local_differentiableAt period hPeriod
      metric patch coordinate upper lower).mul
    (regularGeneralMetricC0KoszulLower_zero_local_differentiableAt period
      hPeriod metric patch coordinate first second lower)

private theorem fderiv_regularFrameLocalCovariantDerivative_reconstruction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    fderiv Real
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
        ∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
              second (patch.coordinateMap coordinate) •
            fderiv Real
              (pulledRegularFrameVector period hPeriod metric patch upper)
              coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) := by
  let coefficient (upper : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first second
      (patch.coordinateMap current)
  let frame (upper : Fin 4) : CoordinateVector → CoordinateVector :=
    pulledRegularFrameVector period hPeriod metric patch upper
  let term (upper : Fin 4) : CoordinateVector → CoordinateVector := fun current =>
    coefficient upper current • frame upper current
  have hCoefficient (upper : Fin 4) :
      DifferentiableAt Real (coefficient upper) coordinate :=
    regularGeneralMetricC0Christoffel_zero_local_differentiableAt period hPeriod
      metric patch coordinate upper first second
  have hFrame (upper : Fin 4) :
      DifferentiableAt Real (frame upper) coordinate :=
    pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate upper
  have hTerm (upper : Fin 4) :
      DifferentiableAt Real (term upper) coordinate :=
    (hCoefficient upper).smul (hFrame upper)
  have hTermDerivative (upper : Fin 4) :
      fderiv Real (term upper) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        coefficient upper coordinate •
            fderiv Real (frame upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) +
          fderiv Real (coefficient upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) • frame upper coordinate := by
    have hProduct := fderiv_smul (hCoefficient upper) (hFrame upper)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hProduct
    change fderiv Real (coefficient upper • frame upper) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hFunction :
      regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second =
        fun current => ∑ upper : Fin 4, term upper current := by
    funext current
    exact (regularGeneralMetricC0Christoffel_zero_reconstructs period hPeriod
      metric patch current first second).symm
  rw [hFunction]
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun upper _ => hTerm upper)
  have hApplied := congrArg
    (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
      derivativeMap
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) hSum
  rw [hApplied]
  simp only [sum_apply]
  calc
    (∑ upper : Fin 4,
      fderiv Real (term upper) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) =
        ∑ upper : Fin 4,
          (coefficient upper coordinate •
              fderiv Real (frame upper) coordinate
                (pulledRegularFrameVector period hPeriod metric patch derivative
                  coordinate) +
            fderiv Real (coefficient upper) coordinate
                (pulledRegularFrameVector period hPeriod metric patch derivative
                  coordinate) • frame upper coordinate) := by
      apply Finset.sum_congr rfl
      intro upper _
      exact hTermDerivative upper
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [show ∀ upper : Fin 4,
          fderiv Real (coefficient upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) =
            regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
              derivative upper first second (patch.coordinateMap coordinate) by
        intro upper
        exact fderiv_regularGeneralMetricC0Christoffel_zero_local period hPeriod
          metric patch coordinate derivative upper first second]
      dsimp only [coefficient, frame]
      abel

private theorem regularFrameChristoffelProduct_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted
                first second (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
                derivative contracted (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      ∑ contracted : Fin 4,
        regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted
              first second (patch.coordinateMap coordinate) •
          regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch derivative contracted coordinate := by
  simp_rw [← regularGeneralMetricC0Christoffel_zero_reconstructs period hPeriod
    metric patch coordinate derivative]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem regularFrameSecondCovariantDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
        (∑ upper : Fin 4,
          (∑ contracted : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod metric 0
                  contracted first second (patch.coordinateMap coordinate) *
              regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
                  derivative contracted (patch.coordinateMap coordinate)) •
            pulledRegularFrameVector period hPeriod metric patch upper
              coordinate) =
      localCovariantDerivativeVectorField period hPeriod metric.metric patch
        (pulledRegularFrameVector period hPeriod metric patch derivative)
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first second) coordinate := by
  unfold localCovariantDerivativeVectorField
  rw [fderiv_regularFrameLocalCovariantDerivative_reconstruction period hPeriod
    metric patch coordinate derivative first second]
  rw [regularFrameChristoffelProduct_reconstructs period hPeriod metric patch
    coordinate derivative first second]
  rw [← regularGeneralMetricC0Christoffel_zero_reconstructs period hPeriod
    metric patch coordinate first second]
  change _ =
    (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
      (∑ contracted : Fin 4,
        regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted
              first second (patch.coordinateMap coordinate) •
          fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch contracted)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate)) +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)
        (∑ contracted : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted
                first second (patch.coordinateMap coordinate) •
            pulledRegularFrameVector period hPeriod metric patch contracted
              coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [regularFrameLocalCovariantDerivativeVector, smul_add]
  rw [Finset.sum_add_distrib]
  abel

private theorem regularFrameStructureChristoffelProduct_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
                contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
                contracted lower (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch contracted lower coordinate := by
  simp_rw [← regularGeneralMetricC0Christoffel_zero_reconstructs period hPeriod
    metric patch coordinate]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem regularFrameBracketCovariantDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
                contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
                contracted lower (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      localCovariantDerivativeVectorField period hPeriod metric.metric patch
        (VectorField.lieBracket Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second))
        (pulledRegularFrameVector period hPeriod metric patch lower)
        coordinate := by
  rw [regularFrameStructureChristoffelProduct_reconstructs period hPeriod
    metric patch coordinate first second lower]
  unfold localCovariantDerivativeVectorField
  rw [regularFrameLocalLieBracket_eq_sum period hPeriod metric patch coordinate
    first second]
  rw [map_sum]
  change _ = _ +
    localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
      coordinate
      (∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch contracted
            coordinate)
      (pulledRegularFrameVector period hPeriod metric patch lower coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) •
        regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          contracted lower coordinate) =
    (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) •
        fderiv Real
          (pulledRegularFrameVector period hPeriod metric patch lower)
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch contracted
            coordinate)) +
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          localLeviCivitaChristoffelApply period hPeriod metric.metric patch
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch contracted
              coordinate)
            (pulledRegularFrameVector period hPeriod metric patch lower
              coordinate)
  simp_rw [regularFrameLocalCovariantDerivativeVector, smul_add]
  rw [Finset.sum_add_distrib]

/-- At the physical metric, the nonholonomic regular-frame Riemann
components reconstruct the existing intrinsic Riemann vector. -/
theorem regularGeneralMetricC0Riemann_zero_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (lower first second : Fin 4) :
    (∑ upper : Fin 4,
        regularGeneralMetricC0Riemann period hPeriod metric 0 upper lower first
              second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      localLeviCivitaRiemannVector period hPeriod metric.metric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  let frame (upper : Fin 4) :=
    pulledRegularFrameVector period hPeriod metric patch upper coordinate
  let firstDerivative := ∑ upper : Fin 4,
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0 first
        upper second lower (patch.coordinateMap coordinate) • frame upper
  let secondDerivative := ∑ upper : Fin 4,
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0 second
        upper first lower (patch.coordinateMap coordinate) • frame upper
  let firstProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted
            second lower (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
            contracted (patch.coordinateMap coordinate)) • frame upper
  let secondProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric 0 contracted first
            lower (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper second
            contracted (patch.coordinateMap coordinate)) • frame upper
  let bracketProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
            contracted lower (patch.coordinateMap coordinate)) • frame upper
  have hExpansion :
      (∑ upper : Fin 4,
        regularGeneralMetricC0Riemann period hPeriod metric 0 upper lower first
              second (patch.coordinateMap coordinate) • frame upper) =
        (firstDerivative + firstProduct) -
          (secondDerivative + secondProduct) - bracketProduct := by
    unfold regularGeneralMetricC0Riemann
    dsimp only [firstDerivative, secondDerivative, firstProduct, secondProduct,
      bracketProduct]
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      regularFrameStructureCoefficientContinuous_apply, sub_smul, add_smul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_smul]
    abel
  rw [hExpansion]
  have hFirstCovariant :
      firstDerivative + firstProduct =
        localCovariantDerivativeVectorField period hPeriod metric.metric patch
          (pulledRegularFrameVector period hPeriod metric patch first)
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch second lower) coordinate := by
    exact regularFrameSecondCovariantDerivative_reconstructs period hPeriod
      metric patch coordinate first second lower
  have hSecondCovariant :
      secondDerivative + secondProduct =
        localCovariantDerivativeVectorField period hPeriod metric.metric patch
          (pulledRegularFrameVector period hPeriod metric patch second)
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch first lower) coordinate := by
    exact regularFrameSecondCovariantDerivative_reconstructs period hPeriod
      metric patch coordinate second first lower
  have hBracketCovariant :
      bracketProduct =
        localCovariantDerivativeVectorField period hPeriod metric.metric patch
          (VectorField.lieBracket Real
            (pulledRegularFrameVector period hPeriod metric patch first)
            (pulledRegularFrameVector period hPeriod metric patch second))
          (pulledRegularFrameVector period hPeriod metric patch lower)
          coordinate := by
    exact regularFrameBracketCovariantDerivative_reconstructs period hPeriod
      metric patch coordinate first second lower
  rw [hFirstCovariant, hSecondCovariant, hBracketCovariant]
  have hFirstFunction :
      regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          first lower =
        localCovariantDerivativeVectorField period hPeriod metric.metric patch
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch lower) := rfl
  have hSecondFunction :
      regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          second lower =
        localCovariantDerivativeVectorField period hPeriod metric.metric patch
          (pulledRegularFrameVector period hPeriod metric patch second)
          (pulledRegularFrameVector period hPeriod metric patch lower) := rfl
  rw [hFirstFunction, hSecondFunction]
  exact localCovariantDerivativeVectorField_curvature period hPeriod metric.metric
      patch coordinate
      (pulledRegularFrameVector period hPeriod metric patch first)
      (pulledRegularFrameVector period hPeriod metric patch second)
      (pulledRegularFrameVector period hPeriod metric patch lower)
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate first)
      (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
        coordinate second)
      (pulledRegularFrameVector_contDiff period hPeriod metric patch lower)

/-- Component form of `regularGeneralMetricC0Riemann_zero_reconstructs`. -/
theorem regularGeneralMetricC0Riemann_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper lower first second : Fin 4) :
    regularGeneralMetricC0Riemann period hPeriod metric 0 upper lower first
        second (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (localLeviCivitaRiemannVector period hPeriod metric.metric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch first
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate)) upper := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  have hReconstruction := congrArg (fun vector => basis.repr vector upper)
    (regularGeneralMetricC0Riemann_zero_reconstructs period hPeriod metric
      patch coordinate lower first second)
  rw [map_sum] at hReconstruction
  simp_rw [map_smul] at hReconstruction
  change (∑ index : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric 0 index lower first
            second (patch.coordinateMap coordinate) *
        basis.repr
          (pulledRegularFrameVector period hPeriod metric patch index
            coordinate) upper) =
    basis.repr
      (localLeviCivitaRiemannVector period hPeriod metric.metric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate))
      upper at hReconstruction
  have hCoordinate (index : Fin 4) :
      basis.repr
          (pulledRegularFrameVector period hPeriod metric patch index coordinate)
          upper = if index = upper then 1 else 0 := by
    rw [← pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      index]
    exact basis.repr_self_apply index upper
  simp_rw [hCoordinate] at hReconstruction
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hReconstruction

/-- The regular-frame Ricci contraction is the existing intrinsic Ricci
bilinear form on the pulled frame. -/
theorem regularGeneralMetricC0Ricci_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    regularGeneralMetricC0Ricci period hPeriod metric 0 first second
        (patch.coordinateMap coordinate) =
      localRicciCurvatureBilinearMap period hPeriod metric.metric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second
          coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  unfold regularGeneralMetricC0Ricci
  change (∑ contracted : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric 0 contracted first
        contracted second (patch.coordinateMap coordinate)) = _
  change _ = localRicciCurvatureVector period hPeriod metric.metric patch
    coordinate
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)
  unfold localRicciCurvatureVector
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (∑ contracted : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric 0 contracted first
        contracted second (patch.coordinateMap coordinate)) =
    ∑ contracted : Fin 4,
      basis.repr
        (localLeviCivitaRiemannVector period hPeriod metric.metric patch
          coordinate (basis contracted)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch first
            coordinate)) contracted
  apply Finset.sum_congr rfl
  intro contracted _
  rw [show basis contracted =
      pulledRegularFrameVector period hPeriod metric patch contracted
        coordinate by
    exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      contracted]
  exact regularGeneralMetricC0Riemann_zero_apply period hPeriod metric patch
    coordinate contracted first contracted second

/-- Matrix view of the physical regular-frame Ricci coefficients. -/
def regularGeneralMetricC0RicciMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) : CoordinateMatrix :=
  fun first second =>
    localRicciCurvatureBilinearMap period hPeriod metric.metric patch
      coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate)

set_option maxHeartbeats 300000 in
theorem regularGeneralMetricC0RicciMatrix_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    regularGeneralMetricC0RicciMatrix period hPeriod metric patch coordinate
        first second =
      localRicciCurvatureBilinearMap period hPeriod metric.metric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second
          coordinate) := by
  rfl

set_option maxHeartbeats 300000 in
theorem regularGeneralMetricC0RicciMatrix_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0RicciMatrix period hPeriod metric patch coordinate =
      (regularFrameChangeMatrix period hPeriod metric patch coordinate).transpose *
        localRicciCurvatureMatrix period hPeriod metric.metric patch coordinate *
        regularFrameChangeMatrix period hPeriod metric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let form := localRicciCurvatureBilinearMap period hPeriod metric.metric patch
    coordinate
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real (Fin 4)) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
        localRicciCurvatureMatrix period hPeriod metric.metric patch
          coordinate := by
    exact localRicciCurvatureBilinearMap_toMatrix period hPeriod metric.metric
      patch coordinate
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        regularGeneralMetricC0RicciMatrix period hPeriod metric patch
          coordinate := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first =
        pulledRegularFrameVector period hPeriod metric patch first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        first]
    rw [show basis second =
        pulledRegularFrameVector period hPeriod metric patch second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        second]
    rfl
  rw [hLocal, hMatrix] at hCongruence
  change regularGeneralMetricC0RicciMatrix period hPeriod metric patch
      coordinate =
    ((Pi.basisFun Real (Fin 4)).toMatrix basis).transpose *
      localRicciCurvatureMatrix period hPeriod metric.metric patch coordinate *
      (Pi.basisFun Real (Fin 4)).toMatrix basis
  exact hCongruence.symm

set_option maxHeartbeats 300000 in
/-- The C2 regular-frame scalar at the physical metric is the intrinsic
local scalar curvature. -/
theorem regularGeneralMetricC0ScalarCurvature_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric 0
        (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod metric.metric patch coordinate := by
  unfold regularGeneralMetricC0ScalarCurvature localScalarCurvature
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply]
  simp_rw [regularGeneralMetricC0Ricci_zero_apply period hPeriod metric patch
    coordinate]
  have hInvariant := matrixEntryContraction_congruence
    (regularFrameChangeMatrix period hPeriod metric patch coordinate)
    (localMetricMatrix period hPeriod metric.metric patch coordinate)
    (localRicciCurvatureMatrix period hPeriod metric.metric patch coordinate)
    (regularFrameChangeMatrix_isUnit period hPeriod metric patch coordinate)
  rw [← regularFrameMetricMatrix_congruence period hPeriod metric patch
      coordinate,
    ← regularGeneralMetricC0RicciMatrix_congruence period hPeriod metric patch
      coordinate] at hInvariant
  simpa only [matrixEntryContraction, regularGeneralMetricC0RicciMatrix,
    localRicciCurvatureMatrix, regularFrameMetricInverseMatrix,
    regularFrameMetricInverseMatrixMap] using hInvariant

/-- The physical member of the C2 family is exactly the existing global
smooth scalar curvature, as a continuous field on the whole quotient. -/
theorem regularGeneralMetricC0ScalarCurvature_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothScalarCurvature period hPeriod metric.metric) := by
  apply ContinuousMap.ext
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  change regularGeneralMetricC0ScalarCurvature period hPeriod metric 0
      (patch.coordinateMap coordinate) =
    globalSmoothScalarCurvature period hPeriod metric.metric
      (patch.coordinateMap coordinate)
  rw [regularGeneralMetricC0ScalarCurvature_zero_apply period hPeriod metric
      patch coordinate,
    globalSmoothScalarCurvature_apply_local period hPeriod metric.metric patch
      coordinate]

/-! ## Einstein--Hilbert density and action -/

def regularGeneralMetricC0Volume
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (regularGeneralMetricC2Volume period hPeriod metric variation)

theorem regularGeneralMetricC0Volume_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC0Volume period hPeriod metric)
      (regularGeneralMetricC2Domain period hPeriod metric) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous
    period hPeriod).contDiff.contDiffOn.comp
      (regularGeneralMetricC2Volume_contDiffOn_two period hPeriod metric)
      (fun _ _ => Set.mem_univ _)

theorem regularGeneralMetricC0Volume_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC0Volume period hPeriod metric 0 =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume := by
  unfold regularGeneralMetricC0Volume
  rw [regularGeneralMetricC2Volume_zero]
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod
    metric.volume

def regularGeneralMetricC0Constant (value : Real) :
    C0Scalar period hPeriod :=
  ⟨fun _ => value, continuous_const⟩

def regularGeneralMetricC0EinsteinHilbertDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  regularGeneralMetricC0Volume period hPeriod metric variation *
    ((1 / (2 * couplings.gravitationalCoupling)) •
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric variation -
        regularGeneralMetricC0Constant period hPeriod
          (2 * couplings.cosmologicalConstant)))

theorem regularGeneralMetricC0EinsteinHilbertDensity_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC0EinsteinHilbertDensity period hPeriod metric
        couplings)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0EinsteinHilbertDensity
  exact (regularGeneralMetricC0Volume_contDiffOn_two period hPeriod metric).mul
    ((regularGeneralMetricC0ScalarCurvature_contDiffOn_two period hPeriod
      metric).sub contDiffOn_const |>.const_smul _)

/-- At the physical metric, the C2-family density is the existing intrinsic
Einstein--Hilbert density, with no restricted metric ansatz. -/
theorem regularGeneralMetricC0EinsteinHilbertDensity_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0EinsteinHilbertDensity period hPeriod metric
        couplings 0 =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularEinsteinHilbertDensityField period hPeriod couplings
          (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
            period hPeriod metric)) := by
  unfold regularGeneralMetricC0EinsteinHilbertDensity
  rw [regularGeneralMetricC0Volume_zero period hPeriod metric,
    regularGeneralMetricC0ScalarCurvature_zero period hPeriod metric]
  apply ContinuousMap.ext
  intro point
  rfl

/-- Integration of continuous scalar densities against the common finite
measure. -/
def regularGeneralMetricC0IntegralCLM
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    C0Scalar period hPeriod →L[Real] Real :=
  (L1.integralCLM
      (α := EffectiveQuotient period hPeriod)
      (E := Real) (μ := measure)).comp
    (ContinuousMap.toLp (1 : ENNReal) measure Real)

theorem regularGeneralMetricC0IntegralCLM_apply
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (field : C0Scalar period hPeriod) :
    regularGeneralMetricC0IntegralCLM period hPeriod measure field =
      ∫ point, field point ∂measure := by
  unfold regularGeneralMetricC0IntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  exact integral_congr_ae
    (ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := Real) measure field)

def regularGeneralMetricC0EinsteinHilbertAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  regularGeneralMetricC0IntegralCLM period hPeriod measure
    (regularGeneralMetricC0EinsteinHilbertDensity period hPeriod metric
      couplings variation)

theorem regularGeneralMetricC0EinsteinHilbertAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric
        measure couplings)
      (regularGeneralMetricC2Domain period hPeriod metric) :=
  (regularGeneralMetricC0IntegralCLM period hPeriod measure).contDiff.contDiffOn
    |>.comp
      (regularGeneralMetricC0EinsteinHilbertDensity_contDiffOn_two
        period hPeriod metric couplings)
      (fun _ _ => Set.mem_univ _)

/-- The physical value of the unrestricted local C2 family is exactly the
pre-existing intrinsic Einstein--Hilbert action. -/
theorem regularGeneralMetricC0EinsteinHilbertAction_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric measure
        couplings 0 =
      intrinsicEinsteinHilbertAction period hPeriod couplings
        (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
          period hPeriod metric)
        measure := by
  unfold regularGeneralMetricC0EinsteinHilbertAction
  rw [regularGeneralMetricC0EinsteinHilbertDensity_zero period hPeriod metric
      couplings,
    regularGeneralMetricC0IntegralCLM_apply period hPeriod measure]
  rfl

/-- Closure gate for P1 of `HESSIAN-GLOBAL-01`: an unrestricted general
metric, a genuine open local chart, C2 parameter dependence, and exact
agreement with the intrinsic physical action. -/
theorem regular_general_metric_c2_einstein_hilbert_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    0 ∈ regularGeneralMetricC2Domain period hPeriod metric ∧
      ContDiffOn Real 2
        (regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric
          measure couplings)
        (regularGeneralMetricC2Domain period hPeriod metric) ∧
      regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric measure
          couplings 0 =
        intrinsicEinsteinHilbertAction period hPeriod couplings
          (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
            period hPeriod metric)
          measure := by
  exact ⟨zero_mem_regularGeneralMetricC2Domain period hPeriod metric,
    regularGeneralMetricC0EinsteinHilbertAction_contDiffOn_two period hPeriod
      metric measure couplings,
    regularGeneralMetricC0EinsteinHilbertAction_zero period hPeriod metric
      measure couplings⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
end JanusFormal
