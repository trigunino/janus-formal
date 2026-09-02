import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D

/-!
# Intrinsic lift of the identity-centred C² root

The completed `4 × 4` root is evaluated pointwise and conjugated through the
genuine frame stored in a regular Lorentz metric.  Its square is then exactly
the affine relative endomorphism `I + g⁻¹h`.  Metric self-adjointness of the
selected branch remains an explicit final condition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev Matrix4 :=
  Matrix (Fin 4) (Fin 4) Real

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

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

/-- The smooth intrinsic variation in the concrete four-dimensional C² matrix
core supplied by the regular frame. -/
def regularGeneralMetricC2VariationMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    C2Matrix period hPeriod :=
  (regularGeneralMetricSmoothC2Variation
    period hPeriod metric tensor).1

theorem regularGeneralMetricC2VariationMatrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) point =
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

/-- Membership in the identity-centred C² root chart. -/
def RegularGeneralMetricC2IdentityRootAdmissible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop :=
  regularGeneralMetricC2VariationMatrix period hPeriod metric tensor ∈
    c2IdentityRootPerturbationDomain period hPeriod

/-- Completed root matrix evaluated at one spacetime point. -/
def regularGeneralMetricC2IdentityRootMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  c2FiniteMatrixValueAt period hPeriod 4
    (c2IdentityRootBranch period hPeriod
      (regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor)) point

private def matrix4ContinuousLinearMap (matrix : Matrix4) :
    (Fin 4 → Real) →L[Real] (Fin 4 → Real) :=
  LinearMap.toContinuousLinearMap matrix.mulVecLin

/-- Pointwise intrinsic root obtained by conjugating the evaluated matrix with
the regular frame. -/
def regularGeneralMetricC2IdentityRootAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  (metric.frameEquiv point).toContinuousLinearMap.comp
    ((matrix4ContinuousLinearMap
      (regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point)).comp
      (metric.frameEquiv point).symm.toContinuousLinearMap)

@[simp]
theorem regularGeneralMetricC2IdentityRootAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point vector =
      metric.frameEquiv point
        (Matrix.mulVec
          (regularGeneralMetricC2IdentityRootMatrixAt
            period hPeriod metric tensor point)
          ((metric.frameEquiv point).symm vector)) :=
  rfl

/-- For the genuine regular frame, the canonical finite-frame coefficients are
exactly the coordinates supplied by `frameEquiv.symm`. -/
theorem regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (row : Fin 4)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameCoefficientAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point row vector =
      (metric.frameEquiv point).symm vector row := by
  let coefficients : Fin 4 → Real := fun index =>
    generalMetricFiniteFrameCoefficientAt period hPeriod
      (RegularFrame period hPeriod metric) metric.metric point index vector
  have hFrameRepresentation :
      metric.frameEquiv point coefficients =
        ∑ index : Fin 4,
          coefficients index •
            (RegularFrame period hPeriod metric).vectorAt point index := by
    calc
      metric.frameEquiv point coefficients =
          metric.frameEquiv point
            (∑ index : Fin 4,
              coefficients index • (Pi.basisFun Real (Fin 4)) index) := by
        congr 1
        exact ((Pi.basisFun Real (Fin 4)).sum_repr coefficients).symm
      _ = ∑ index : Fin 4,
          coefficients index •
            metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index) := by
        simp only [map_sum, map_smul]
      _ = ∑ index : Fin 4,
          coefficients index •
            (RegularFrame period hPeriod metric).vectorAt point index := by
        apply Finset.sum_congr rfl
        intro index _
        rw [regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
          RegularGeneralLorentzMetric.frame_eq_basisFun]
  have hReconstruct :=
    generalMetricFiniteFrameCoefficientAt_reconstructs
      period hPeriod (RegularFrame period hPeriod metric)
        metric.metric point vector
  have hImage : metric.frameEquiv point coefficients = vector := by
    rw [hFrameRepresentation]
    exact hReconstruct.symm
  have hCoordinates : coefficients = (metric.frameEquiv point).symm vector := by
    apply (metric.frameEquiv point).injective
    rw [hImage, (metric.frameEquiv point).apply_symm_apply]
  exact congrFun hCoordinates row

/-- Matrix encoding of the lifted root is exactly the evaluated C² root. -/
theorem regularGeneralMetricC2IdentityRootAt_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point) =
      regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point := by
  ext row column
  rw [finiteFrameEndomorphismMatrixAt_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  simp [regularGeneralMetricC2IdentityRootAt_apply,
    regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
    RegularGeneralLorentzMetric.frame_eq_basisFun,
    Pi.basisFun_apply]

private theorem regularGeneralMetricAffineRelativeEndomorphismAt_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (row column : Fin 4) :
    finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        (regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point) row column =
      (1 : Matrix4) row column +
        finiteFrameEndomorphismMatrixAt period hPeriod
          (RegularFrame period hPeriod metric) metric.metric point
          (raisedGeneralMetricTensorAt
            period hPeriod metric.metric tensor point) row column := by
  rw [finiteFrameEndomorphismMatrixAt_apply]
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (RegularFrame period hPeriod metric) metric.metric point row
      ((RegularFrame period hPeriod metric).vectorAt point column +
        raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point
          ((RegularFrame period hPeriod metric).vectorAt point column)) = _
  rw [map_add,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  simp [regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
    RegularGeneralLorentzMetric.frame_eq_basisFun,
    Matrix.one_apply, Pi.single_apply]

/-- Exact pointwise square identity after lifting the completed root into the
tangent bundle. -/
theorem regularGeneralMetricC2IdentityRootAt_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point).comp
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point) =
      regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point := by
  apply finiteFrameEndomorphismMatrixAt_injective period hPeriod
    (RegularFrame period hPeriod metric) metric.metric point
  unfold RegularFrame
  rw [finiteFrameEndomorphismMatrixAt_comp]
  ext row column
  rw [Matrix.mul_apply]
  have hRootMatrix := regularGeneralMetricC2IdentityRootAt_matrix
    period hPeriod metric tensor point
  have hRootEntry (first second : Fin 4) :=
    congrFun (congrFun hRootMatrix first) second
  simp_rw [hRootEntry]
  rw [regularGeneralMetricAffineRelativeEndomorphismAt_matrix]
  change
    (∑ index : Fin 4,
      regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point row index *
        regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point index column) =
      (1 : Matrix4) row column +
        finiteFrameEndomorphismMatrixAt period hPeriod
          (RegularFrame period hPeriod metric) metric.metric point
          (raisedGeneralMetricTensorAt
            period hPeriod metric.metric tensor point) row column
  have hC2 := c2IdentityRootBranch_square period hPeriod hRoot
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hC2
  rw [show c2FiniteMatrixSquare period hPeriod 4
      (c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor)) =
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor))
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) by rfl,
    c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_identity] at hValue
  have hMatrixSquare := hValue.trans
    (congrArg (fun matrix => 1 + matrix)
      (regularGeneralMetricC2VariationMatrix_valueAt
        period hPeriod metric tensor point))
  have hEntry := congrFun (congrFun hMatrixSquare row) column
  simpa [regularGeneralMetricC2IdentityRootMatrixAt,
    regularGeneralMetricC2VariationMatrix, Matrix.mul_apply,
    Matrix.add_apply, Fin.sum_univ_four] using hEntry

/-- The sole property not supplied by the full C² square-root chart. -/
def RegularGeneralMetricC2IdentityRootIsSelfAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point first second,
    metric.metric.musical point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point first) second =
      metric.metric.musical point first
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point second)

/-- Root package consumed by the affine Lorentz-congruence bridge. -/
def regularGeneralMetricC2IdentityAffineRootData
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (hSelfAdjoint : RegularGeneralMetricC2IdentityRootIsSelfAdjoint
      period hPeriod metric tensor) :
    RegularGeneralMetricAffineRootData period hPeriod metric tensor where
  root := regularGeneralMetricC2IdentityRootAt period hPeriod metric tensor
  square := regularGeneralMetricC2IdentityRootAt_square
    period hPeriod metric tensor hRoot
  selfAdjoint := hSelfAdjoint

/-- Once self-adjointness is established, Gate 328 produces the genuine affine
Lorentz metric. -/
def regularGeneralMetricC2IdentityAffineLorentzMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (hNondegenerate : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (hSelfAdjoint : RegularGeneralMetricC2IdentityRootIsSelfAdjoint
      period hPeriod metric tensor) :
    SmoothGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricAffineLorentzMetric period hPeriod metric tensor
    (regularGeneralMetricC2IdentityAffineRootData
      period hPeriod metric tensor hRoot hSelfAdjoint) hNondegenerate

@[simp]
theorem regularGeneralMetricC2IdentityAffineLorentzMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (hNondegenerate : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (hSelfAdjoint : RegularGeneralMetricC2IdentityRootIsSelfAdjoint
      period hPeriod metric tensor) :
    (regularGeneralMetricC2IdentityAffineLorentzMetric period hPeriod metric
      tensor hRoot hNondegenerate hSelfAdjoint).tensor =
        metric.metric.tensor + tensor :=
  rfl

/-- Gate marker: the completed identity root now has an exact intrinsic square;
only its base-metric self-adjointness remains before Lorentz packaging. -/
theorem regular_general_metric_c2_identity_root_lift_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    (∀ point,
      (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point).comp
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point) =
        regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point) ∧
      (RegularGeneralMetricC2IdentityRootIsSelfAdjoint
          period hPeriod metric tensor →
        ∀ hNondegenerate : regularGeneralMetricSmoothC2Variation
            period hPeriod metric tensor ∈
          generalMetricRelativeC2OpenDomain period hPeriod
            (RegularFrame period hPeriod metric) metric.metric,
          ∃ varied : SmoothGeneralLorentzMetric period hPeriod,
            varied.tensor = metric.metric.tensor + tensor) := by
  refine ⟨regularGeneralMetricC2IdentityRootAt_square
    period hPeriod metric tensor hRoot, ?_⟩
  intro hSelfAdjoint hNondegenerate
  exact ⟨regularGeneralMetricC2IdentityAffineLorentzMetric period hPeriod
    metric tensor hRoot hNondegenerate hSelfAdjoint, rfl⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
end JanusFormal
