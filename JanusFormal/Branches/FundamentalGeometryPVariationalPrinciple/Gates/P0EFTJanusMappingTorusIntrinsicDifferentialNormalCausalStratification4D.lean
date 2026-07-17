import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusNormalCausalStratificationReduction4D

/-!
# Intrinsic Lorentz form on the differential normal line

The normal fiber is a quotient of the ambient tangent fiber, so a Lorentz
form does not descend by evaluating arbitrary representatives.  This gate
isolates the exact missing geometric datum: the continuous orthogonal lift
of that quotient.  From it, the actual intrinsic quotient Lorentz metric
gives the required continuous quadratic form and the full causal
stratification.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusNormalCausalStratificationReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev ThroatTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev AmbientTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev ThroatDifferentialRange
    (point : ThroatBase period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

/-- Exact missing bridge.  `lift` is the metric-orthogonal representative of
each differential-normal quotient class.  Its squared length is required to
vary continuously on the already constructed total-space topology. -/
structure ContinuousOrthogonalDifferentialNormalLift where
  lift : ∀ point : ThroatBase period hPeriod,
    DifferentialNormalFiber period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point
  represents : ∀ (point : ThroatBase period hPeriod)
      (normal : DifferentialNormalFiber period hPeriod point),
    (ThroatDifferentialRange period hPeriod point).mkQ (lift point normal) =
      normal
  orthogonal : ∀ (point : ThroatBase period hPeriod)
      (normal : DifferentialNormalFiber period hPeriod point)
      (tangent : ThroatTangent period hPeriod point),
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (lift point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0
  continuous_metric_square : Continuous
    (fun normal : DifferentialNormalTotalSpace period hPeriod =>
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod normal.1)
        (lift normal.1 normal.2) (lift normal.1 normal.2))

/-- Squared intrinsic Lorentz length of the orthogonal representative. -/
def intrinsicDifferentialNormalQuadraticValue
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod)
    (normal : DifferentialNormalTotalSpace period hPeriod) : Real :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
    (fixedThroatQuotientInclusion period hPeriod normal.1)
    (bridge.lift normal.1 normal.2) (bridge.lift normal.1 normal.2)

theorem intrinsicDifferentialNormalQuadraticValue_eq_metric
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod)
    (normal : DifferentialNormalTotalSpace period hPeriod) :
    intrinsicDifferentialNormalQuadraticValue period hPeriod bridge normal =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod normal.1)
        (bridge.lift normal.1 normal.2) (bridge.lift normal.1 normal.2) :=
  rfl

/-- Orthogonality makes the metric pairing independent of the chosen
ambient representative of the quotient class. -/
theorem intrinsicDifferentialNormalQuadraticValue_eq_metric_of_represents
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod)
    (point : ThroatBase period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (representative : AmbientTangent period hPeriod point)
    (hRepresentative :
      (ThroatDifferentialRange period hPeriod point).mkQ representative =
        normal) :
    intrinsicDifferentialNormalQuadraticValue period hPeriod bridge
        ⟨point, normal⟩ =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (bridge.lift point normal) representative := by
  have hQuotient :
      (ThroatDifferentialRange period hPeriod point).mkQ representative =
        (ThroatDifferentialRange period hPeriod point).mkQ
          (bridge.lift point normal) :=
    hRepresentative.trans (bridge.represents point normal).symm
  have hDifference : representative - bridge.lift point normal ∈
      ThroatDifferentialRange period hPeriod point :=
    (Submodule.Quotient.eq
      (ThroatDifferentialRange period hPeriod point)).1 hQuotient
  rcases hDifference with ⟨tangent, hTangent⟩
  have hRepresentativeEq :
      representative = bridge.lift point normal +
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent := by
    have hTangent' :
        mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point tangent =
          representative - bridge.lift point normal :=
      hTangent
    rw [hTangent']
    abel
  rw [hRepresentativeEq]
  simp [intrinsicDifferentialNormalQuadraticValue,
    bridge.orthogonal point normal tangent]

/-- The genuine intrinsic quotient metric instantiates the quadratic-form
interface once its canonical orthogonal quotient lift is supplied. -/
def intrinsicDifferentialNormalQuadraticForm
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod) :
    ContinuousDifferentialNormalQuadraticForm period hPeriod where
  value := intrinsicDifferentialNormalQuadraticValue period hPeriod bridge
  continuous_value := bridge.continuous_metric_square
  zero_section := by
    intro point
    simp [intrinsicDifferentialNormalQuadraticValue]
  map_smul := by
    intro point scalar normal
    simp [intrinsicDifferentialNormalQuadraticValue, pow_two]
    ring

theorem intrinsicDifferentialNormalQuadraticForm_value
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod)
    (normal : DifferentialNormalTotalSpace period hPeriod) :
    (intrinsicDifferentialNormalQuadraticForm period hPeriod bridge).value normal =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod normal.1)
        (bridge.lift normal.1 normal.2) (bridge.lift normal.1 normal.2) :=
  rfl

/-- Complete conditional closure of the normal causal-stratification gate. -/
theorem intrinsicDifferentialNormalCausalStratification
    (bridge : ContinuousOrthogonalDifferentialNormalLift period hPeriod) :
    let form := intrinsicDifferentialNormalQuadraticForm period hPeriod bridge
    IsOpen (normalSpacelikeStratum period hPeriod form) ∧
      IsOpen (normalTimelikeStratum period hPeriod form) ∧
      IsClosed (normalNullStratum period hPeriod form) ∧
      IsOpen (normalNonNullStratum period hPeriod form) ∧
      IsClosed (normalJointStratum period hPeriod form) ∧
      normalJointStratum period hPeriod form ⊆
        normalNullStratum period hPeriod form ∧
      normalSpacelikeStratum period hPeriod form ∪
          normalTimelikeStratum period hPeriod form ∪
          normalNullStratum period hPeriod form = univ := by
  exact normalCausalStratification_of_continuousQuadraticForm period hPeriod
    (intrinsicDifferentialNormalQuadraticForm period hPeriod bridge)

end

end P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D
end JanusFormal
