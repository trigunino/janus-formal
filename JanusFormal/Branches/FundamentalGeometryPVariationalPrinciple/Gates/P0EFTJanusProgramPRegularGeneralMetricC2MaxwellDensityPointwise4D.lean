import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

/-! # Pointwise form of the variable-metric C² Maxwell derivative -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D
open P0EFTJanusProgramPC2MaxwellMatrixContractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

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

def c2ValueAt (field : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  canonicalPhysicalScalarC2JetCoreToContinuous
    period hPeriod field point

/-- Pointwise real matrix represented by a completed relative-metric
direction. -/
def regularGeneralMetricC2RelativeMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  c2FiniteMatrixValueAt period hPeriod 4 direction.1 point

/-- Pointwise real Cartan-curvature matrices in the regular frame. -/
def regularFrameMaxwellCurvatureMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Fin 2 → Matrix4 :=
  fun component first second =>
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
      component first second point

@[simp]
private theorem c2ValueAt_product
    (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first second) point =
      c2ValueAt period hPeriod first point *
        c2ValueAt period hPeriod second point :=
  rfl

@[simp]
private theorem c2ValueAt_add
    (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod (first + second) point =
      c2ValueAt period hPeriod first point +
        c2ValueAt period hPeriod second point :=
  rfl

@[simp]
private theorem c2ValueAt_sum
    {Index : Type*} [Fintype Index]
    (fields : Index → C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod (∑ index, fields index) point =
      ∑ index, c2ValueAt period hPeriod (fields index) point := by
  exact map_sum
    ((ContinuousMap.evalCLM Real point).comp
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod))
    fields Finset.univ

@[simp]
private theorem c2ValueAt_smul
    (scalar : Real) (field : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod (scalar • field) point =
      scalar * c2ValueAt period hPeriod field point := by
  exact map_smul
    ((ContinuousMap.evalCLM Real point).comp
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod))
    scalar field

@[simp]
private theorem c2ValueAt_smooth
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod field) point = field point := by
  unfold c2ValueAt
  rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

private theorem c2MaxwellMatrixContraction_valueAt
    (inverse first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (c2MaxwellMatrixContraction
          period hPeriod inverse first second) point =
      ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        c2ValueAt period hPeriod (inverse μ ρ) point *
          c2ValueAt period hPeriod (inverse ν σ) point *
          c2ValueAt period hPeriod (first μ ν) point *
          c2ValueAt period hPeriod (second ρ σ) point := by
  unfold c2MaxwellMatrixContraction
  simp only [c2ValueAt_sum, c2ValueAt_product]

private theorem c2MaxwellMatrixContractionVelocity_valueAt
    (inverse velocity first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (c2MaxwellMatrixContractionVelocity
          period hPeriod inverse velocity first second) point =
      ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        (c2ValueAt period hPeriod (inverse μ ρ) point *
            c2ValueAt period hPeriod (velocity ν σ) point +
          c2ValueAt period hPeriod (velocity μ ρ) point *
            c2ValueAt period hPeriod (inverse ν σ) point) *
          c2ValueAt period hPeriod (first μ ν) point *
          c2ValueAt period hPeriod (second ρ σ) point := by
  unfold c2MaxwellMatrixContractionVelocity
  simp only [c2ValueAt_sum, c2ValueAt_product, c2ValueAt_add]

private theorem c2FiniteMatrixValueAt_neg
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (-matrix) point =
      -c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  rfl

@[simp]
private theorem c2ValueAt_matrix_entry
    (matrix : C2Matrix period hPeriod) (row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod (matrix row column) point =
      c2FiniteMatrixValueAt period hPeriod 4 matrix point row column :=
  rfl

private theorem regularFrameMetricInverseC2Matrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularFrameMetricInverseC2Matrix period hPeriod metric) point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point := by
  ext row column
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric row column))
      point = _
  rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

private theorem regularFrameGaugeCurvatureC2Matrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularFrameGaugeCurvatureC2Matrix
          period hPeriod metric potential component) point =
      regularFrameMaxwellCurvatureMatrixAt
        period hPeriod metric potential point component := by
  ext first second
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameGaugeCurvatureCoefficient
          period hPeriod metric potential component first second)) point = _
  rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

private theorem regularGeneralMetricC2InverseDerivative_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
          period hPeriod metric direction) point =
      -(regularGeneralMetricC2RelativeMatrixAt
          period hPeriod metric direction point *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) := by
  have hDerivative :=
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero_apply
      period hPeriod metric direction
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point)
    hDerivative
  rw [c2FiniteMatrixValueAt_neg, c2FiniteMatrixValueAt_product,
    regularFrameMetricInverseC2Matrix_valueAt] at hValue
  change c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
        period hPeriod metric direction) point =
    -(regularGeneralMetricC2RelativeMatrixAt
      period hPeriod metric direction point *
        regularFrameMetricInverseMatrixMap period hPeriod metric point)
  exact hValue

theorem regularGeneralMetricC2VolumeDerivative_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (regularGeneralMetricC2VolumeDerivativeAtZero
          period hPeriod metric direction) point =
      metric.volume point / 2 *
        Matrix.trace
          (regularGeneralMetricC2RelativeMatrixAt
            period hPeriod metric direction point) := by
  rw [regularGeneralMetricC2VolumeDerivativeAtZero]
  rw [generalMetricC2VolumeDensityDerivativeAtZero_apply]
  rw [c2ValueAt_smul]
  change (1 / 2 : Real) *
      (metric.volume point *
        c2ValueAt period hPeriod
          (c2FiniteMatrixTrace period hPeriod 4 direction.1) point) = _
  rw [c2FiniteMatrixTrace_apply, c2ValueAt_sum]
  change (1 / 2 : Real) *
      (metric.volume point *
        ∑ index : Fin 4,
          c2ValueAt period hPeriod (direction.1 index index) point) =
    metric.volume point / 2 *
      ∑ index : Fin 4,
        c2ValueAt period hPeriod (direction.1 index index) point
  ring

private theorem regularGeneralMetricC2MaxwellPairing_zero_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (regularGeneralMetricC2MaxwellPairing
          period hPeriod metric potential potential 0) point =
      maxwellPairingAt
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (regularFrameMaxwellCurvatureMatrixAt
          period hPeriod metric potential point) := by
  rw [regularGeneralMetricC2MaxwellPairing,
    regularGeneralMetricC2InverseMetricMatrix_zero]
  unfold maxwellPairingAt
  unfold regularFrameMaxwellCurvatureMatrixAt
  rw [c2ValueAt_sum]
  simp_rw [c2MaxwellMatrixContraction_valueAt]
  simp_rw [show ∀ row column,
      c2ValueAt period hPeriod
          (regularFrameMetricInverseC2Matrix period hPeriod metric row column)
          point =
        regularFrameMetricInverseMatrixMap period hPeriod metric point
          row column by
    intro row column
    exact congrFun (congrFun
      (regularFrameMetricInverseC2Matrix_valueAt
        period hPeriod metric point) row) column]
  simp_rw [show ∀ component row column,
      c2ValueAt period hPeriod
          (regularFrameGaugeCurvatureC2Matrix period hPeriod metric potential
            component row column) point =
        regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component row column point by
    intro component row column
    exact congrFun (congrFun
      (regularFrameGaugeCurvatureC2Matrix_valueAt
        period hPeriod metric potential component point) row) column]

private theorem regularGeneralMetricC2MaxwellPairingDerivative_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
          period hPeriod metric potential potential direction) point =
      maxwellMetricPairingVelocityAt
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (-(regularGeneralMetricC2RelativeMatrixAt
            period hPeriod metric direction point *
          regularFrameMetricInverseMatrixMap period hPeriod metric point))
        (regularFrameMaxwellCurvatureMatrixAt
          period hPeriod metric potential point) := by
  rw [regularGeneralMetricC2MaxwellPairingDerivativeAtZero_apply_inverse]
  rw [c2ValueAt_sum]
  simp_rw [c2MaxwellMatrixContractionVelocity_valueAt]
  unfold maxwellMetricPairingVelocityAt
  simp_rw [c2ValueAt_matrix_entry]
  rw [regularGeneralMetricC2InverseDerivative_valueAt]
  rw [regularFrameMetricInverseC2Matrix_valueAt]
  simp_rw [show ∀ component row column,
      c2FiniteMatrixValueAt period hPeriod 4
          (regularFrameGaugeCurvatureC2Matrix
            period hPeriod metric potential component) point row column =
        regularFrameMaxwellCurvatureMatrixAt
          period hPeriod metric potential point component row column by
    intro component row column
    exact congrFun (congrFun
      (regularFrameGaugeCurvatureC2Matrix_valueAt
        period hPeriod metric potential component point) row) column]
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
  ring

/-- Pointwise product-rule formula for the actual variable-volume Maxwell
density derivative. -/
theorem regularGeneralMetricC2MaxwellDensityDerivative_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2ValueAt period hPeriod
        (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
          period hPeriod metric potential potential direction) point =
      metric.volume point / 2 *
          Matrix.trace
            (regularGeneralMetricC2RelativeMatrixAt
              period hPeriod metric direction point) *
          maxwellPairingAt
            (regularFrameMetricInverseMatrixMap period hPeriod metric point)
            (regularFrameMaxwellCurvatureMatrixAt
              period hPeriod metric potential point) +
        metric.volume point *
          maxwellMetricPairingVelocityAt
            (regularFrameMetricInverseMatrixMap period hPeriod metric point)
            (-(regularGeneralMetricC2RelativeMatrixAt
                period hPeriod metric direction point *
              regularFrameMetricInverseMatrixMap period hPeriod metric point))
            (regularFrameMaxwellCurvatureMatrixAt
              period hPeriod metric potential point) := by
  rw [regularGeneralMetricC2MaxwellDensityDerivativeAtZero_apply]
  simp only [c2ValueAt_add, c2ValueAt_product]
  rw [regularGeneralMetricC2Volume_zero, c2ValueAt_smooth]
  rw [regularGeneralMetricC2VolumeDerivative_valueAt,
    regularGeneralMetricC2MaxwellPairing_zero_valueAt,
    regularGeneralMetricC2MaxwellPairingDerivative_valueAt]
  ring

/-- After the physical `-1/4` Maxwell normalization, the C² derivative is
exactly the local metric variation previously used to derive the stress. -/
theorem regularGeneralMetricC2MaxwellActionDensityDerivative_eq_localVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    -(1 / 4 : Real) *
        c2ValueAt period hPeriod
          (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
            period hPeriod metric potential potential direction) point =
      localMaxwellMetricVariation
        (metric.volume point)
        (metric.volume point / 2 *
          Matrix.trace
            (regularGeneralMetricC2RelativeMatrixAt
              period hPeriod metric direction point))
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (-(regularGeneralMetricC2RelativeMatrixAt
            period hPeriod metric direction point *
          regularFrameMetricInverseMatrixMap period hPeriod metric point))
        (regularFrameMaxwellCurvatureMatrixAt
          period hPeriod metric potential point) := by
  rw [regularGeneralMetricC2MaxwellDensityDerivative_valueAt]
  unfold localMaxwellMetricVariation
  ring

/-- Gate marker for the pointwise Maxwell action-density derivative. -/
theorem regular_general_metric_c2_maxwell_density_pointwise_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    -(1 / 4 : Real) *
        c2ValueAt period hPeriod
          (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
            period hPeriod metric potential potential direction) point =
      localMaxwellMetricVariation
        (metric.volume point)
        (metric.volume point / 2 *
          Matrix.trace
            (regularGeneralMetricC2RelativeMatrixAt
              period hPeriod metric direction point))
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (-(regularGeneralMetricC2RelativeMatrixAt
            period hPeriod metric direction point *
          regularFrameMetricInverseMatrixMap period hPeriod metric point))
        (regularFrameMaxwellCurvatureMatrixAt
          period hPeriod metric potential point) :=
  regularGeneralMetricC2MaxwellActionDensityDerivative_eq_localVariation
    period hPeriod metric potential direction point

end
end P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
end JanusFormal
