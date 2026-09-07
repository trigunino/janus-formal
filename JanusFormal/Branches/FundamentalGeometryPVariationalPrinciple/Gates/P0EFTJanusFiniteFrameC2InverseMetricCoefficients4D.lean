import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricContraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D

/-! # The actual inverse metric on the redundant dual family

The inverse of the extended relative endomorphism acts on the fixed inverse
metric coefficients. The resulting C² matrix depends smoothly on the metric
variation and agrees with the genuine inverse musical map on smooth inputs.
The redundant Gram matrix is never inverted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusFiniteFrameMetricContraction4D

private theorem affine_inverse_evaluation
    {V W : Type*} [AddCommGroup V] [Module Real V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W] [ContinuousAdd W]
    (base varied : V ≃L[Real] W) (difference : V →L[Real] W)
    (hVaried : (varied : V →L[Real] W) = (base : V →L[Real] W) + difference)
    (covector : W) :
    varied.symm covector + base.symm (difference (varied.symm covector)) =
      base.symm covector := by
  apply base.injective
  rw [map_add, base.apply_symm_apply, base.apply_symm_apply]
  have h := congrArg (fun operator : V →L[Real] W => operator (varied.symm covector)) hVaried
  simpa only [ContinuousLinearEquiv.coe_coe, add_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h.symm

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

/-- Coefficients of the actual inverse metric, in the fixed reconstructed dual. -/
def smoothFiniteFrameInverseMetricMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothFiniteMatrix period hPeriod frame.count :=
  fun row column => finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric row column

private theorem smoothFiniteFrameInverseMetricMatrix_equation
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation) :
    smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric +
      smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric variation)
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric) =
      smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let theta := generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric point
  have hMetricAt : (metric.musical point : _ →L[Real] _) =
      (baseMetric.musical point : _ →L[Real] _) + variation.tensor point := by
    rw [metric.musical_eq_tensor point, baseMetric.musical_eq_tensor point, hMetric]
    rfl
  have hInverse := affine_inverse_evaluation
    (V := TangentFiber period hPeriod point) (W := TangentFiber period hPeriod point →L[Real] Real)
    (baseMetric.musical point) (metric.musical point) (variation.tensor point) hMetricAt (theta column)
  have hPair := finiteFrameCovector_pairing period hPeriod frame baseMetric point
    ((theta row).comp ((inverseMetricSharp period hPeriod baseMetric point).comp (variation.tensor point)))
    (inverseMetricSharp period hPeriod metric point (theta column))
  have hValue := congrArg (theta row) hInverse
  simp only [map_add] at hValue
  change theta row (inverseMetricSharp period hPeriod metric point (theta column)) +
      theta row (inverseMetricSharp period hPeriod baseMetric point
        (variation.tensor point (inverseMetricSharp period hPeriod metric point (theta column)))) =
    theta row (inverseMetricSharp period hPeriod baseMetric point (theta column)) at hValue
  simp only [ContinuousLinearMap.comp_apply] at hPair
  rw [hPair] at hValue
  change smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric row column point +
    smoothFiniteMatrixProduct period hPeriod frame.count
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric variation)
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric) row column point = _
  simpa only [smoothFiniteFrameInverseMetricMatrix, smoothFiniteMatrixProduct,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, finiteFrameInverseMetricCoefficient_apply,
    smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply,
    finiteFrameEndomorphismMatrixAt_apply, raisedGeneralMetricTensorAt,
    ContinuousLinearMap.comp_apply, inverseMetricContraction, inverseMetricSharp, theta] using hValue

local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric

/-- Smooth inverse coefficients on the genuine open C² metric domain. -/
def finiteFrameInverseMetricC2Coefficients (variation : Model) :
    C2FiniteMatrix period hPeriod frame.count :=
  c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
    (generalMetricRelativeC2InverseMatrix period hPeriod frame baseMetric variation)
    (smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))

theorem finiteFrameInverseMetricC2Coefficients_contDiffOn :
    ContDiffOn Real ∞ (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) := by
  exact ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count).contDiff.comp_contDiffOn
    (generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod frame baseMetric)).clm_apply
      contDiffOn_const

theorem finiteFrameInverseMetricC2Coefficients_equation
    (variation : Model)
    (hVariation : variation ∈ generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) :
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame baseMetric variation)
      (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric variation) =
    smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric) := by
  unfold finiteFrameInverseMetricC2Coefficients
  rw [← c2FiniteMatrixProduct_assoc, generalMetricRelativeC2Extended_mul_inverse
    period hPeriod frame baseMetric variation hVariation, c2FiniteMatrixProduct_identity_left]

/-- The completed coefficients equal the genuine smooth inverse, throughout the domain. -/
theorem finiteFrameInverseMetricC2Coefficients_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) :
    finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
    smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric) := by
  let input := smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation
  have hCandidate : c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame baseMetric input)
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric)) =
    smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric) := by
    change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count +
        smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric variation))
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric)) = _
    rw [map_add, add_apply, c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_smooth,
      ← (smoothFiniteMatrixToC2 period hPeriod frame.count).map_add,
      smoothFiniteFrameInverseMetricMatrix_equation period hPeriod frame baseMetric variation metric hMetric]
  have hUnit : (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame baseMetric input)).IsInvertible := hVariation
  exact hUnit.injective ((finiteFrameInverseMetricC2Coefficients_equation period hPeriod frame
    baseMetric input hVariation).trans hCandidate.symm)

/-- C⁰ readout of each inverse coefficient is a genuine smooth function of the C² metric. -/
def finiteFrameInverseMetricC0Coefficient (row column : Fin frame.count) (variation : Model) :
    C(EffectiveQuotient period hPeriod, Real) :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric variation row column)

theorem finiteFrameInverseMetricC0Coefficient_contDiffOn (row column : Fin frame.count) :
    ContDiffOn Real ∞ (finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric row column)
      (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) := by
  have h := (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp_contDiffOn
    ((contDiff_apply Real (C2Scalar period hPeriod) column).comp_contDiffOn
      ((contDiff_apply Real (Fin frame.count → C2Scalar period hPeriod) row).comp_contDiffOn
        (finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame baseMetric)))
  exact h

theorem finiteFrameInverseMetricC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (row column : Fin frame.count) :
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric row column
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric row column) := by
  unfold finiteFrameInverseMetricC0Coefficient
  rw [finiteFrameInverseMetricC2Coefficients_smooth period hPeriod frame baseMetric variation metric
    hMetric hVariation]
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod _

end
end P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
end JanusFormal
