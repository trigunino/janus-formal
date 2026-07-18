import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D

/-!
# PT stability of throat nondegeneracy and transversality

The intrinsic PT differential is a continuous-linear equivalence.  Its
pointwise pullback therefore preserves and reflects nondegeneracy.  Applied
to general-metric throat traces, naturality closes PT and PT/exchange
stability of the exact no-tangential-radical condition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev ThroatTangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

/-- The intrinsic throat PT differential as a genuine linear equivalence. -/
def throatPTDerivativeEquiv
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point ≃L[Real]
      ThroatTangentFiber period hPeriod
        (fixedThroatPT period hPeriod point) :=
  (fixedThroatPTDiffeomorph period hPeriod).mfderivToContinuousLinearEquiv
    (I := throatCoverModelWithCorners)
    (J := throatCoverModelWithCorners) (by simp) point

@[simp]
theorem throatPTDerivativeEquiv_apply
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    throatPTDerivativeEquiv period hPeriod point vector =
      throatPTDerivative period hPeriod point vector :=
  rfl

/-- Pointwise intrinsic PT pullback preserves and reflects nondegeneracy. -/
theorem throatPTTensorPullbackValue_injective_iff
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    Function.Injective
        (throatPTTensorPullbackValue period hPeriod tensor point) ↔
      Function.Injective
        (tensor.tensor (fixedThroatPT period hPeriod point)) := by
  constructor
  · intro hPullback first second hEqual
    have hPreimage :
        (throatPTDerivativeEquiv period hPeriod point).symm first =
          (throatPTDerivativeEquiv period hPeriod point).symm second := by
      apply hPullback
      apply ContinuousLinearMap.ext
      intro vector
      have hEvaluate := congrArg
        (fun covector =>
          covector (throatPTDerivativeEquiv period hPeriod point vector))
        hEqual
      simpa only [throatPTTensorPullbackValue_apply,
        ← throatPTDerivativeEquiv_apply,
        ContinuousLinearEquiv.apply_symm_apply] using hEvaluate
    exact (throatPTDerivativeEquiv period hPeriod point).symm.injective hPreimage
  · intro hTensor first second hEqual
    apply (throatPTDerivativeEquiv period hPeriod point).injective
    apply hTensor
    apply ContinuousLinearMap.ext
    intro vector
    have hEvaluate := congrArg
      (fun covector =>
        covector ((throatPTDerivativeEquiv period hPeriod point).symm vector))
      hEqual
    simpa only [throatPTTensorPullbackValue_apply,
      ← throatPTDerivativeEquiv_apply,
      ContinuousLinearEquiv.apply_symm_apply] using hEvaluate

/-- Exact pointwise nondegeneracy predicate for the intrinsic PT pullback.
No arbitrary smooth pullback section is postulated. -/
def ThroatPTPullbackIsNondegenerate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point, Function.Injective
    (throatPTTensorPullbackValue period hPeriod tensor point)

/-- Global pointwise PT pullback nondegeneracy is equivalent to the original
smooth throat tensor's nondegeneracy. -/
theorem throatPTPullbackIsNondegenerate_iff
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    ThroatPTPullbackIsNondegenerate period hPeriod tensor ↔
      ThroatTensorIsNondegenerate period hPeriod tensor := by
  constructor
  · intro hPullback point
    have hAtPT :=
      (throatPTTensorPullbackValue_injective_iff period hPeriod tensor
        (fixedThroatPT period hPeriod point)).1
        (hPullback (fixedThroatPT period hPeriod point))
    rw [fixedThroatPT_involutive period hPeriod point] at hAtPT
    exact hAtPT
  · intro hTensor point
    exact (throatPTTensorPullbackValue_injective_iff
      period hPeriod tensor point).2
        (hTensor (fixedThroatPT period hPeriod point))

/-- The trace of a PT-pulled metric is nondegenerate exactly when the
original metric's throat trace is nondegenerate. -/
theorem generalLorentzMetricThroatTrace_pt_nondegenerate_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ThroatTensorIsNondegenerate period hPeriod
        (generalLorentzMetricThroatTrace period hPeriod
          (smoothGeneralLorentzMetricPTPullback period hPeriod metric)) ↔
      ThroatTensorIsNondegenerate period hPeriod
        (generalLorentzMetricThroatTrace period hPeriod metric) := by
  have hNatural :
      ThroatTensorIsNondegenerate period hPeriod
          (generalLorentzMetricThroatTrace period hPeriod
            (smoothGeneralLorentzMetricPTPullback period hPeriod metric)) ↔
        ThroatPTPullbackIsNondegenerate period hPeriod
          (generalLorentzMetricThroatTrace period hPeriod metric) := by
    constructor
    · intro hTrace point
      have hValue :
          (generalLorentzMetricThroatTrace period hPeriod
              (smoothGeneralLorentzMetricPTPullback
                period hPeriod metric)).tensor point =
            throatPTTensorPullbackValue period hPeriod
              (generalLorentzMetricThroatTrace period hPeriod metric) point := by
        apply ContinuousLinearMap.ext
        intro first
        apply ContinuousLinearMap.ext
        intro second
        exact generalLorentzMetricThroatTrace_pt_natural
          period hPeriod metric point first second
      rw [← hValue]
      exact hTrace point
    · intro hPullback point
      have hValue :
          (generalLorentzMetricThroatTrace period hPeriod
              (smoothGeneralLorentzMetricPTPullback
                period hPeriod metric)).tensor point =
            throatPTTensorPullbackValue period hPeriod
              (generalLorentzMetricThroatTrace period hPeriod metric) point := by
        apply ContinuousLinearMap.ext
        intro first
        apply ContinuousLinearMap.ext
        intro second
        exact generalLorentzMetricThroatTrace_pt_natural
          period hPeriod metric point first second
      rw [hValue]
      exact hPullback point
  exact hNatural.trans
    (throatPTPullbackIsNondegenerate_iff period hPeriod
      (generalLorentzMetricThroatTrace period hPeriod metric))

/-- The exact no-tangential-radical condition is PT invariant. -/
theorem hasNoTangentialRadical_pt_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    HasNoTangentialRadical period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric) ↔
      HasNoTangentialRadical period hPeriod metric :=
  (throatTrace_nondegenerate_iff_no_tangential_radical period hPeriod
      (smoothGeneralLorentzMetricPTPullback period hPeriod metric)).symm.trans
    ((generalLorentzMetricThroatTrace_pt_nondegenerate_iff
        period hPeriod metric).trans
      (throatTrace_nondegenerate_iff_no_tangential_radical
        period hPeriod metric))

/-- PT together with sector exchange preserves the domain on which both
induced throat metrics are nondegenerate. -/
theorem hasNoTangentialRadical_ptExchange_iff
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    (HasNoTangentialRadical period hPeriod
          (smoothGeneralLorentzMetricPTExchange period hPeriod metrics).1 ∧
        HasNoTangentialRadical period hPeriod
          (smoothGeneralLorentzMetricPTExchange period hPeriod metrics).2) ↔
      (HasNoTangentialRadical period hPeriod metrics.1 ∧
        HasNoTangentialRadical period hPeriod metrics.2) := by
  simp only [smoothGeneralLorentzMetricPTExchange]
  rw [hasNoTangentialRadical_pt_iff period hPeriod metrics.2,
    hasNoTangentialRadical_pt_iff period hPeriod metrics.1]
  exact and_comm

end

end P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D
end JanusFormal
