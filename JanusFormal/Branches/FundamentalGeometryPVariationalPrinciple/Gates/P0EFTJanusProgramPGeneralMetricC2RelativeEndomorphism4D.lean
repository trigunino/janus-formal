import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VariationCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothInverseMusical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D

/-!
# Relative-endomorphism C² presentation of general metric variations

Relative to an arbitrary smooth Lorentz base metric, a symmetric variation
`h` defines the intrinsic endomorphism `g⁻¹h`.  Existing smooth inverse-musical
and redundant-frame reconstruction maps give its exact smooth coefficient
matrix.  The C² lift is faithful and belongs to the intrinsic projector
corner, without choosing a global tangent frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev effectiveBackground : EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

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

/-- The smooth vector `g⁻¹(h(v_column, ·))`. -/
def generalMetricRaisedFrameVector
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (column : Fin frame.count) :
    EffectiveD8SmoothVectorField (effectiveBackground period hPeriod) :=
  effectiveD8SmoothInverseMusical (effectiveBackground period hPeriod)
    baseMetric
    (generalMetricFrameCovector period hPeriod frame tensor column)

@[simp]
theorem generalMetricRaisedFrameVector_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (column : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricRaisedFrameVector
        period hPeriod frame baseMetric tensor column point =
      inverseMetricSharp period hPeriod baseMetric point
        (tensor.tensor point (frame.vectorAt point column)) :=
  rfl

/-- Smooth redundant-frame matrix of the intrinsic endomorphism `g⁻¹h`. -/
def smoothGeneralMetricRelativeEndomorphismMatrix
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothFiniteMatrix period hPeriod frame.count :=
  fun row column =>
    generalMetricFiniteFrameCoefficient period hPeriod frame baseMetric
      (generalMetricRaisedFrameVector
        period hPeriod frame baseMetric tensor column) row

theorem smoothGeneralMetricRelativeEndomorphismMatrix_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (fun row column =>
      smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric tensor row column point) =
      finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point
        (raisedGeneralMetricTensorAt
          period hPeriod baseMetric tensor point) := by
  funext row column
  rfl

@[simp]
theorem smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric tensor row column point =
      finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point
        (raisedGeneralMetricTensorAt
          period hPeriod baseMetric tensor point) row column := by
  exact congrFun (congrFun
    (smoothGeneralMetricRelativeEndomorphismMatrix_apply
      period hPeriod frame baseMetric tensor point) row) column

theorem smoothGeneralMetricRelativeEndomorphismMatrix_add
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric (first + second) =
      smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric first +
        smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric second := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hRaised :
      generalMetricRaisedFrameVector
          period hPeriod frame baseMetric (first + second) column point =
        generalMetricRaisedFrameVector
            period hPeriod frame baseMetric first column point +
          generalMetricRaisedFrameVector
            period hPeriod frame baseMetric second column point := by
    change (baseMetric.musical point).symm
        (first.tensor point (frame.vectorAt point column) +
          second.tensor point (frame.vectorAt point column)) =
      (baseMetric.musical point).symm
          (first.tensor point (frame.vectorAt point column)) +
        (baseMetric.musical point).symm
          (second.tensor point (frame.vectorAt point column))
    exact map_add (baseMetric.musical point).symm _ _
  change generalMetricFiniteFrameCoefficientAt
      period hPeriod frame baseMetric point row
        (generalMetricRaisedFrameVector
          period hPeriod frame baseMetric (first + second) column point) = _
  rw [hRaised, map_add]
  rfl

theorem smoothGeneralMetricRelativeEndomorphismMatrix_smul
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric (scalar • tensor) =
      scalar • smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric tensor := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hRaised :
      generalMetricRaisedFrameVector
          period hPeriod frame baseMetric (scalar • tensor) column point =
        scalar • generalMetricRaisedFrameVector
          period hPeriod frame baseMetric tensor column point := by
    change (baseMetric.musical point).symm
        (scalar • tensor.tensor point (frame.vectorAt point column)) =
      scalar • (baseMetric.musical point).symm
        (tensor.tensor point (frame.vectorAt point column))
    exact map_smul (baseMetric.musical point).symm scalar _
  change generalMetricFiniteFrameCoefficientAt
      period hPeriod frame baseMetric point row
        (generalMetricRaisedFrameVector
          period hPeriod frame baseMetric (scalar • tensor) column point) = _
  rw [hRaised, map_smul]
  rfl

/-- Faithful linear C² encoding of `g⁻¹h`. -/
def smoothGeneralMetricRelativeEndomorphismToC2
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      C2FiniteMatrix period hPeriod frame.count where
  toFun tensor :=
    smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric tensor)
  map_add' first second := by
    rw [smoothGeneralMetricRelativeEndomorphismMatrix_add, map_add]
  map_smul' scalar tensor := by
    rw [smoothGeneralMetricRelativeEndomorphismMatrix_smul, map_smul]
    rfl

theorem smoothGeneralMetricRelativeEndomorphismToC2_injective
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (smoothGeneralMetricRelativeEndomorphismToC2
        period hPeriod frame baseMetric) := by
  intro first second hEqual
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  have hMatrix :
      finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point
          (raisedGeneralMetricTensorAt
            period hPeriod baseMetric first point) =
        finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point
          (raisedGeneralMetricTensorAt
            period hPeriod baseMetric second point) := by
    funext row column
    have hEntry :
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (smoothGeneralMetricRelativeEndomorphismMatrix
              period hPeriod frame baseMetric first row column) =
          smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (smoothGeneralMetricRelativeEndomorphismMatrix
              period hPeriod frame baseMetric second row column) :=
      congrFun (congrFun hEqual row) column
    have hCoefficient :=
      smoothToCanonicalPhysicalScalarC2JetCore_injective
        period hPeriod hEntry
    have hPoint := congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point)
      hCoefficient
    have hFirstApply := congrFun (congrFun
      (smoothGeneralMetricRelativeEndomorphismMatrix_apply
        period hPeriod frame baseMetric first point) row) column
    have hSecondApply := congrFun (congrFun
      (smoothGeneralMetricRelativeEndomorphismMatrix_apply
        period hPeriod frame baseMetric second point) row) column
    exact hFirstApply.symm.trans (hPoint.trans hSecondApply)
  have hRaised := finiteFrameEndomorphismMatrixAt_injective
    period hPeriod frame baseMetric point hMatrix
  apply ContinuousLinearMap.ext
  intro vector
  have hVector := DFunLike.congr_fun hRaised vector
  change (baseMetric.musical point).symm
      (first.tensor point vector) =
    (baseMetric.musical point).symm
      (second.tensor point vector) at hVector
  exact (baseMetric.musical point).symm.injective hVector

theorem smoothGeneralMetricRelativeEndomorphism_corner
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothFiniteFrameProjectorCoefficients
          period hPeriod frame baseMetric)
        (smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor) =
      smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor ∧
    smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor)
        (smoothFiniteFrameProjectorCoefficients
          period hPeriod frame baseMetric) =
      smoothGeneralMetricRelativeEndomorphismMatrix
        period hPeriod frame baseMetric tensor := by
  constructor <;> funext row column <;>
    apply SmoothQuotientField.ext period hPeriod Real <;> intro point
  · have hCorner := finiteFrameEndomorphismMatrixAt_left_projector
      period hPeriod frame baseMetric point
        (raisedGeneralMetricTensorAt
          period hPeriod baseMetric tensor point)
    have hEntry := congrFun (congrFun hCorner row) column
    simp only [smoothFiniteMatrixProduct,
      smoothFiniteFrameProjectorCoefficients,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
      smoothScalarFieldMul_apply, finiteFrameProjectorCoefficient_apply,
      smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply]
    simpa [Matrix.mul_apply, finiteFrameProjectorMatrixAt,
      finiteFrameEndomorphismMatrixAt] using hEntry
  · have hCorner := finiteFrameEndomorphismMatrixAt_right_projector
      period hPeriod frame baseMetric point
        (raisedGeneralMetricTensorAt
          period hPeriod baseMetric tensor point)
    have hEntry := congrFun (congrFun hCorner row) column
    simp only [smoothFiniteMatrixProduct,
      smoothFiniteFrameProjectorCoefficients,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
      smoothScalarFieldMul_apply, finiteFrameProjectorCoefficient_apply,
      smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply]
    simpa [Matrix.mul_apply, finiteFrameProjectorMatrixAt,
      finiteFrameEndomorphismMatrixAt] using hEntry

theorem smoothGeneralMetricRelativeEndomorphismToC2_corner
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame baseMetric)
        (smoothGeneralMetricRelativeEndomorphismToC2
          period hPeriod frame baseMetric tensor) =
      smoothGeneralMetricRelativeEndomorphismToC2
          period hPeriod frame baseMetric tensor ∧
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (smoothGeneralMetricRelativeEndomorphismToC2
          period hPeriod frame baseMetric tensor)
        (c2FiniteFrameProjector period hPeriod frame baseMetric) =
      smoothGeneralMetricRelativeEndomorphismToC2
        period hPeriod frame baseMetric tensor := by
  constructor
  · change c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothFiniteFrameProjectorCoefficients
            period hPeriod frame baseMetric))
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothGeneralMetricRelativeEndomorphismMatrix
            period hPeriod frame baseMetric tensor)) =
      smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor)
    rw [c2FiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToC2 period hPeriod frame.count)
      (smoothGeneralMetricRelativeEndomorphism_corner
        period hPeriod frame baseMetric tensor).1
  · change c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothGeneralMetricRelativeEndomorphismMatrix
            period hPeriod frame baseMetric tensor))
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothFiniteFrameProjectorCoefficients
            period hPeriod frame baseMetric)) =
      smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor)
    rw [c2FiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToC2 period hPeriod frame.count)
      (smoothGeneralMetricRelativeEndomorphism_corner
        period hPeriod frame baseMetric tensor).2

/-- Summary gate for the faithful multiplicative relative presentation. -/
theorem general_metric_c2_relative_endomorphism_gate
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
        (smoothGeneralMetricRelativeEndomorphismToC2
          period hPeriod frame baseMetric) ∧
      (∀ tensor,
        c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count
            (c2FiniteFrameProjector period hPeriod frame baseMetric)
            (smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame baseMetric tensor) =
          smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame baseMetric tensor ∧
        c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count
            (smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame baseMetric tensor)
            (c2FiniteFrameProjector period hPeriod frame baseMetric) =
          smoothGeneralMetricRelativeEndomorphismToC2
            period hPeriod frame baseMetric tensor) := by
  exact ⟨smoothGeneralMetricRelativeEndomorphismToC2_injective
      period hPeriod frame baseMetric,
    smoothGeneralMetricRelativeEndomorphismToC2_corner
      period hPeriod frame baseMetric⟩

end

end P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
end JanusFormal
