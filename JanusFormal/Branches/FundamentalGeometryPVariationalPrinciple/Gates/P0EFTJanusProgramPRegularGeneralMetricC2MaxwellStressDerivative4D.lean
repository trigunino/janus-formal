import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D

/-! # Exact C² Maxwell action derivative as invariant stress pairing -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- Dense genuine-smooth direction in the completed regular metric core. -/
def regularGeneralMetricC2SmoothDirection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric :=
  smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric tensor

/-- Covariant components of a genuine smooth metric variation. -/
def regularFrameCovariantVariationMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun first second =>
    tensor.tensor point (metric.frame first point) (metric.frame second point)

private theorem regularFrameMetricMatrix_mul_relative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameMetricMatrixMap period hPeriod metric point *
        regularGeneralMetricC2RelativeMatrixAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection
            period hPeriod metric tensor) point =
      regularFrameCovariantVariationMatrixAt
        period hPeriod metric tensor point := by
  ext row column
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hExpansion := regularGeneralMetricC0MetricCoefficient_apply_expansion
    period hPeriod metric direction row column point
  have hSmooth :=
    candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth
      period hPeriod metric tensor row column point
  have hInstalled :
      (∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          ((1 : Matrix4) middle column +
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
              (direction.1 middle column) point)) =
        regularFrameMetricMatrixMap period hPeriod metric point row column +
          regularFrameCovariantVariationMatrixAt
            period hPeriod metric tensor point row column :=
    hExpansion.symm.trans hSmooth
  have hBase :
      (∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          (1 : Matrix4) middle column) =
        regularFrameMetricMatrixMap period hPeriod metric point row column := by
    exact congrFun (congrFun
      (Matrix.mul_one
        (regularFrameMetricMatrixMap period hPeriod metric point)) row) column
  simp_rw [mul_add] at hInstalled
  rw [Finset.sum_add_distrib, hBase] at hInstalled
  change (∑ middle : Fin 4,
      regularFrameMetricMatrix period hPeriod metric row middle point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (direction.1 middle column) point) =
    regularFrameCovariantVariationMatrixAt
      period hPeriod metric tensor point row column
  exact add_left_cancel hInstalled

/-- On every genuine smooth direction, the stored relative matrix is exactly
`g⁻¹h`. -/
theorem regularGeneralMetricC2RelativeMatrixAt_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2RelativeMatrixAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point *
        regularFrameCovariantVariationMatrixAt
          period hPeriod metric tensor point := by
  let base := regularFrameMetricMatrixMap period hPeriod metric point
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let relative := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric
    (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point
  let variation := regularFrameCovariantVariationMatrixAt
    period hPeriod metric tensor point
  have hBaseRelative : base * relative = variation :=
    regularFrameMetricMatrix_mul_relative_smooth
      period hPeriod metric tensor point
  have hInverseBase : inverse * base = 1 := by
    exact Matrix.nonsing_inv_mul base
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  calc
    relative = 1 * relative := (Matrix.one_mul relative).symm
    _ = (inverse * base) * relative := by rw [hInverseBase]
    _ = inverse * (base * relative) := Matrix.mul_assoc inverse base relative
    _ = inverse * variation := by rw [hBaseRelative]

/-- The physically normalized C² action-density derivative on a smooth
covariant variation is one half the derived finite stress pairing. -/
theorem regularGeneralMetricC2MaxwellActionDensityDerivative_smooth_eq_stress
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    -(1 / 4 : Real) *
        c2ValueAt period hPeriod
          (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
            period hPeriod metric potential potential
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor)) point =
      metric.volume point / 2 *
        variationalMaxwellStressPairing
          (regularFrameMetricInverseMatrixMap period hPeriod metric point)
          (regularFrameMaxwellCurvatureMatrixAt
            period hPeriod metric potential point)
          (regularFrameCovariantVariationMatrixAt
            period hPeriod metric tensor point) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  let inverse := regularFrameMetricInverseMatrixMap
    period hPeriod metric point
  let curvature := regularFrameMaxwellCurvatureMatrixAt
    period hPeriod metric potential point
  let variation := regularFrameCovariantVariationMatrixAt
    period hPeriod metric tensor point
  have hLocal :=
    regularGeneralMetricC2MaxwellActionDensityDerivative_eq_localVariation
      period hPeriod metric potential direction point
  have hRelative :
      regularGeneralMetricC2RelativeMatrixAt
          period hPeriod metric direction point = inverse * variation :=
    regularGeneralMetricC2RelativeMatrixAt_smooth
      period hPeriod metric tensor point
  rw [hRelative] at hLocal
  have hLocal' :
      -(1 / 4 : Real) *
          c2ValueAt period hPeriod
            (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
              period hPeriod metric potential potential direction) point =
        localMaxwellMetricVariation (metric.volume point)
          (metric.volume point / 2 *
            metricTraceVariation inverse variation)
          inverse (inverseMetricVelocity inverse variation) curvature := by
    simpa [metricTraceVariation, inverseMetricVelocity, direction, inverse,
      curvature, variation] using hLocal
  calc
    _ = localMaxwellMetricVariation (metric.volume point)
          (metric.volume point / 2 *
            metricTraceVariation inverse variation)
          inverse (inverseMetricVelocity inverse variation) curvature := hLocal'
    _ = metric.volume point / 2 *
          variationalMaxwellStressPairing inverse curvature variation :=
      localMaxwellMetricVariation_eq_stressPairing
        (metric.volume point) inverse curvature variation

/-- The same derivative is the invariant pairing with the globally
reconstructed Maxwell stress tensor. -/
theorem regularGeneralMetricC2MaxwellActionDensityDerivative_smooth_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    -(1 / 4 : Real) *
        c2ValueAt period hPeriod
          (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
            period hPeriod metric potential potential
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor)) point =
      metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric
          (regularGeneralMetricMaxwellStressTensor period hPeriod metric
            potential) tensor point := by
  rw [regularGeneralMetricC2MaxwellActionDensityDerivative_smooth_eq_stress]
  apply congrArg (metric.volume point / 2 * ·)
  change variationalMaxwellStressPairing
      (regularFrameMetricInverseMatrixMap period hPeriod metric point)
      (fun component first second =>
        regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first second point)
      (fun first second => tensor.tensor point
        (metric.frame first point) (metric.frame second point)) = _
  exact regularGeneralMetricMaxwellStress_variation_invariant
    period hPeriod metric potential tensor point

/-- Physically normalized integrated Maxwell action on the genuine metric
chart. -/
def regularGeneralMetricC2IntegratedMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  -(1 / 4 : Real) *
    regularGeneralMetricC2IntegratedMaxwellPairing
      period hPeriod metric measure potential potential direction

/-- Exact Fréchet derivative of the physical integrated Maxwell action. -/
def regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  -(1 / 4 : Real) •
    regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
      period hPeriod metric measure potential potential

theorem regularGeneralMetricC2IntegratedMaxwellAction_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2IntegratedMaxwellAction
        period hPeriod metric measure potential)
      (regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
        period hPeriod metric measure potential) 0 := by
  change HasFDerivAt
    (fun direction => -(1 / 4 : Real) *
      regularGeneralMetricC2IntegratedMaxwellPairing
        period hPeriod metric measure potential potential direction)
    (-(1 / 4 : Real) •
      regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
        period hPeriod metric measure potential potential) 0
  exact (regularGeneralMetricC2IntegratedMaxwellPairing_hasFDerivAt_zero
    period hPeriod metric measure potential potential).const_mul
      (-(1 / 4 : Real))

/-- On every genuine smooth direction, the integrated action derivative is
the invariant integrated Maxwell stress pairing. -/
theorem regularGeneralMetricC2IntegratedMaxwellActionDerivative_smooth_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
        period hPeriod metric measure potential
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      ∫ point, metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric
          (regularGeneralMetricMaxwellStressTensor period hPeriod metric
            potential) tensor point ∂measure := by
  rw [regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero,
    smul_apply]
  change -(1 / 4 : Real) *
      regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
        period hPeriod metric measure potential potential
          (regularGeneralMetricC2SmoothDirection
            period hPeriod metric tensor) = _
  rw [regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero_apply,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    regularGeneralMetricC2MaxwellActionDensityDerivative_smooth_invariant
      period hPeriod metric potential tensor point

/-- Gate marker: the true variable-metric Maxwell action differentiates to
the global invariant Maxwell stress on every dense smooth direction. -/
theorem regular_general_metric_c2_maxwell_stress_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    HasFDerivAt
        (regularGeneralMetricC2IntegratedMaxwellAction
          period hPeriod metric measure potential)
        (regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
          period hPeriod metric measure potential) 0 ∧
      regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
          period hPeriod metric measure potential
          (regularGeneralMetricC2SmoothDirection
            period hPeriod metric tensor) =
        ∫ point, metric.volume point / 2 *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricMaxwellStressTensor period hPeriod metric
              potential) tensor point ∂measure :=
  ⟨regularGeneralMetricC2IntegratedMaxwellAction_hasFDerivAt_zero
      period hPeriod metric measure potential,
    regularGeneralMetricC2IntegratedMaxwellActionDerivative_smooth_invariant
      period hPeriod metric measure potential tensor⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
end JanusFormal
