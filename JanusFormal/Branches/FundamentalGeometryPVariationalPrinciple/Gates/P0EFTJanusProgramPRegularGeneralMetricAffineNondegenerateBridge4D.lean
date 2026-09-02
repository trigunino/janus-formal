import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

/-!
# Affine nondegenerate metric bridge

For a genuine smooth symmetric variation in the existing relative C² open
domain, the affine tensor `g + h` has a pointwise musical equivalence.  The
Lorentz-signature stability needed for a `SmoothGeneralLorentzMetric` is not
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev CotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

private def c2ScalarValueAtLinearMap
    (point : EffectiveQuotient period hPeriod) :
    C2Scalar period hPeriod →ₗ[Real] Real where
  toFun value := (value.1 point).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def c2ScalarValueAt
    (value : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  c2ScalarValueAtLinearMap period hPeriod point value

def c2FiniteMatrixValueAt
    (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    Matrix (Fin dimension) (Fin dimension) Real :=
  fun row column => c2ScalarValueAt period hPeriod (matrix row column) point

theorem c2FiniteMatrixValueAt_add
    (dimension : Nat)
    (first second : C2FiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod dimension (first + second) point =
      c2FiniteMatrixValueAt period hPeriod dimension first point +
        c2FiniteMatrixValueAt period hPeriod dimension second point :=
  rfl

theorem c2FiniteMatrixValueAt_product
    (dimension : Nat)
    (first second : C2FiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod dimension
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first second) point =
      c2FiniteMatrixValueAt period hPeriod dimension first point *
        c2FiniteMatrixValueAt period hPeriod dimension second point := by
  ext row column
  change
    (((c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first second)
          row column).1 point).1 =
      ∑ middle : Fin dimension,
        ((first row middle).1 point).1 *
          ((second middle column).1 point).1
  rw [c2FiniteMatrixProduct_apply]
  change
    c2ScalarValueAtLinearMap period hPeriod point
        (∑ middle : Fin dimension,
          canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (first row middle) (second middle column)) =
      ∑ middle : Fin dimension,
        ((first row middle).1 point).1 *
          ((second middle column).1 point).1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  rfl

theorem c2FiniteMatrixValueAt_identity
    (dimension : Nat)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod dimension
        (c2FiniteMatrixIdentity period hPeriod dimension) point = 1 := by
  ext row column
  change smoothFiniteMatrixIdentity period hPeriod dimension row column point =
    (1 : Matrix (Fin dimension) (Fin dimension) Real) row column
  simp [smoothFiniteMatrixIdentity,
    P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField,
    Matrix.one_apply]

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

/-- The genuine smooth variation, embedded in the completed relative C² core. -/
def regularGeneralMetricSmoothC2Variation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod
      (RegularFrame period hPeriod metric) metric.metric :=
  smoothToGeneralMetricRelativeC2Core period hPeriod
    (RegularFrame period hPeriod metric) metric.metric tensor

theorem regularGeneralMetricSmoothC2Variation_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod
        (RegularFrame period hPeriod metric).count
        (regularGeneralMetricSmoothC2Variation
          period hPeriod metric tensor).1 point =
      finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        (raisedGeneralMetricTensorAt
          period hPeriod metric.metric tensor point) := by
  change (fun row column =>
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric tensor
          row column point) = _
  exact smoothGeneralMetricRelativeEndomorphismMatrix_apply period hPeriod
    (RegularFrame period hPeriod metric) metric.metric tensor point

private theorem regularGeneralMetricExtendedMatrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod
        (RegularFrame period hPeriod metric).count
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric
          (regularGeneralMetricSmoothC2Variation
            period hPeriod metric tensor)) point =
      1 + finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        (raisedGeneralMetricTensorAt
          period hPeriod metric.metric tensor point) := by
  unfold generalMetricRelativeC2ExtendedMatrix
  rw [c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_identity,
    regularGeneralMetricSmoothC2Variation_valueAt]

/-- Pointwise relative endomorphism of the affine tensor `g + h`. -/
def regularGeneralMetricAffineRelativeEndomorphismAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  ContinuousLinearMap.id Real (TangentFiber period hPeriod point) +
    raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point

private theorem regularGeneralMetricAffineRelativeEndomorphismAt_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point)
    (hVector : regularGeneralMetricAffineRelativeEndomorphismAt
      period hPeriod metric tensor point vector = 0) :
    vector = 0 := by
  let frame := RegularFrame period hPeriod metric
  let variation := regularGeneralMetricSmoothC2Variation
    period hPeriod metric tensor
  let relative := raisedGeneralMetricTensorAt
    period hPeriod metric.metric tensor point
  let matrix := 1 + finiteFrameEndomorphismMatrixAt
    period hPeriod frame metric.metric point relative
  let inverseMatrix := c2FiniteMatrixValueAt period hPeriod frame.count
    (generalMetricRelativeC2InverseMatrix period hPeriod frame metric.metric
      variation) point
  let coefficients : Fin frame.count → Real := fun index =>
    generalMetricFiniteFrameCoefficientAt period hPeriod frame metric.metric
      point index vector
  have hInverseC2 := generalMetricRelativeC2Inverse_mul_extended
    period hPeriod frame metric.metric variation hDomain
  have hInverse := congrArg
    (fun current => c2FiniteMatrixValueAt
      period hPeriod frame.count current point) hInverseC2
  rw [c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_identity,
    regularGeneralMetricExtendedMatrix_valueAt] at hInverse
  change inverseMatrix * matrix = 1 at hInverse
  have hReconstruct :
      vector = ∑ index : Fin frame.count,
        coefficients index • frame.vectorAt point index :=
    generalMetricFiniteFrameCoefficientAt_reconstructs
      period hPeriod frame metric.metric point vector
  have hRelativeMulVec (row : Fin frame.count) :
      Matrix.mulVec
          (finiteFrameEndomorphismMatrixAt period hPeriod frame
            metric.metric point relative) coefficients row =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point row (relative vector) := by
    unfold Matrix.mulVec dotProduct
    rw [hReconstruct]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro column _
    change
      generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point row (relative (frame.vectorAt point column)) *
          coefficients column =
        coefficients column *
          generalMetricFiniteFrameCoefficientAt period hPeriod frame
            metric.metric point row (relative (frame.vectorAt point column))
    ring
  have hMatrixVector : Matrix.mulVec matrix coefficients = 0 := by
    funext row
    change (Matrix.mulVec
        (1 + finiteFrameEndomorphismMatrixAt period hPeriod frame
          metric.metric point relative) coefficients) row = 0
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    change coefficients row +
      Matrix.mulVec
          (finiteFrameEndomorphismMatrixAt period hPeriod frame
            metric.metric point relative) coefficients row = 0
    rw [hRelativeMulVec]
    calc
      coefficients row +
          generalMetricFiniteFrameCoefficientAt period hPeriod frame
            metric.metric point row (relative vector) =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point row (vector + relative vector) := by
            rw [map_add]
      _ = generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point row
          (regularGeneralMetricAffineRelativeEndomorphismAt
            period hPeriod metric tensor point vector) := by
            rfl
      _ = 0 := by rw [hVector]; exact map_zero _
  have hCoefficients : coefficients = 0 := by
    have hApply :
        Matrix.mulVec inverseMatrix
            (Matrix.mulVec matrix coefficients) = coefficients := by
      rw [Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]
    rw [hMatrixVector] at hApply
    simpa using hApply.symm
  rw [hReconstruct, hCoefficients]
  simp

theorem regularGeneralMetricAffineRelativeEndomorphismAt_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point) := by
  intro first second hEqual
  have hZero :
      regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  exact sub_eq_zero.mp
    (regularGeneralMetricAffineRelativeEndomorphismAt_eq_zero
      period hPeriod metric tensor hDomain point (first - second) hZero)

/-- Relative endomorphism transported to the regular four-frame. -/
def regularGeneralMetricAffineRelativeCoordinateEndomorphismAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (Fin 4 → Real) →L[Real] (Fin 4 → Real) :=
  (metric.frameEquiv point).symm.toContinuousLinearMap.comp
    ((regularGeneralMetricAffineRelativeEndomorphismAt
      period hPeriod metric tensor point).comp
        (metric.frameEquiv point).toContinuousLinearMap)

theorem regularGeneralMetricAffineRelativeCoordinateEndomorphismAt_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (regularGeneralMetricAffineRelativeCoordinateEndomorphismAt
        period hPeriod metric tensor point) := by
  intro first second hEqual
  apply (metric.frameEquiv point).injective
  apply regularGeneralMetricAffineRelativeEndomorphismAt_injective
    period hPeriod metric tensor hDomain point
  apply (metric.frameEquiv point).symm.injective
  simpa [regularGeneralMetricAffineRelativeCoordinateEndomorphismAt] using hEqual

/-- The relative affine endomorphism as a continuous linear equivalence. -/
def regularGeneralMetricAffineRelativeEquivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod point :=
  (metric.frameEquiv point).symm.trans
    ((LinearEquiv.ofInjectiveEndo
      (regularGeneralMetricAffineRelativeCoordinateEndomorphismAt
        period hPeriod metric tensor point).toLinearMap
      (regularGeneralMetricAffineRelativeCoordinateEndomorphismAt_injective
        period hPeriod metric tensor hDomain point)).toContinuousLinearEquiv.trans
          (metric.frameEquiv point))

@[simp]
theorem regularGeneralMetricAffineRelativeEquivAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricAffineRelativeEquivAt
        period hPeriod metric tensor hDomain point vector =
      regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point vector := by
  simp [regularGeneralMetricAffineRelativeEquivAt,
    regularGeneralMetricAffineRelativeCoordinateEndomorphismAt]

/-- Pointwise musical equivalence of the affine tensor `g + h`. -/
def regularGeneralMetricAffineMusical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      CotangentFiber period hPeriod point :=
  (regularGeneralMetricAffineRelativeEquivAt
    period hPeriod metric tensor hDomain point).trans
      (metric.metric.musical point)

@[simp]
theorem regularGeneralMetricAffineMusical_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricAffineMusical period hPeriod metric tensor hDomain
        point vector =
      metric.metric.musical point
        (regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point vector) := by
  rw [regularGeneralMetricAffineMusical]
  simp

theorem regularGeneralMetricAffineMusical_toContinuousLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricAffineMusical
        period hPeriod metric tensor hDomain point :
      TangentFiber period hPeriod point →L[Real]
        CotangentFiber period hPeriod point) =
      (metric.metric.musical point).toContinuousLinearMap +
        tensor.tensor point := by
  apply ContinuousLinearMap.ext
  intro vector
  change regularGeneralMetricAffineMusical
      period hPeriod metric tensor hDomain point vector = _
  rw [regularGeneralMetricAffineMusical_apply]
  change metric.metric.musical point
      (vector + (metric.metric.musical point).symm
        (tensor.tensor point vector)) =
    metric.metric.musical point vector + tensor.tensor point vector
  rw [map_add]
  simp

/-- Smooth tensor and its certified pointwise musical, without a premature
Lorentz-signature claim. -/
structure SmoothAffineNondegenerateMetric where
  tensor : SmoothSymmetricCovariantTwoTensor period hPeriod
  musical : ∀ point, TangentFiber period hPeriod point ≃L[Real]
    CotangentFiber period hPeriod point
  musical_eq_tensor : ∀ point,
    (musical point : TangentFiber period hPeriod point →L[Real]
      CotangentFiber period hPeriod point) = tensor.tensor point

/-- The affine tensor `g + h` with its pointwise nondegenerate musical. -/
def regularGeneralMetricAffineNondegenerateMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    SmoothAffineNondegenerateMetric period hPeriod where
  tensor := metric.metric.tensor + tensor
  musical := regularGeneralMetricAffineMusical
    period hPeriod metric tensor hDomain
  musical_eq_tensor := by
    intro point
    rw [regularGeneralMetricAffineMusical_toContinuousLinearMap]
    change (metric.metric.musical point).toContinuousLinearMap +
        tensor.tensor point = metric.metric.tensor.tensor point +
          tensor.tensor point
    rw [metric.metric.musical_eq_tensor point]

@[simp]
theorem regularGeneralMetricAffineNondegenerateMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    (regularGeneralMetricAffineNondegenerateMetric
      period hPeriod metric tensor hDomain).tensor =
      metric.metric.tensor + tensor :=
  rfl

/-- Gate marker: the relative affine endomorphism is injective everywhere and
the exact affine tensor has a certified pointwise musical equivalence. -/
theorem regular_general_metric_affine_nondegenerate_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    (∀ point : EffectiveQuotient period hPeriod,
      Function.Injective
        (regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point)) ∧
      ∃ affine : SmoothAffineNondegenerateMetric period hPeriod,
        affine.tensor = metric.metric.tensor + tensor := by
  refine ⟨?_, ⟨regularGeneralMetricAffineNondegenerateMetric
    period hPeriod metric tensor hDomain, rfl⟩⟩
  intro point
  exact regularGeneralMetricAffineRelativeEndomorphismAt_injective
    period hPeriod metric tensor hDomain point

end

end P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
end JanusFormal
