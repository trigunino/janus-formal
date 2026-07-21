import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D

/-!
# Exact overlap criterion for local holonomic diagonal metrics

Two local pulled-back diagonal tensors agree on an overlap exactly when the
canonical frame transition preserves the diagonal model pairing.  This gate
isolates the genuine cocycle condition required for global tensor descent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalHolonomicDiagonalGluingCriterion4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusLocalFrameNoGo4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusHolonomicDiagonalSharp4D
open P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- A model transition is an isometry of one holonomic diagonal pairing. -/
def PreservesHolonomicDiagonalPair
    (magnitude : HolonomicCoefficients)
    (transition : CoverCoordinates ≃L[Real] CoverCoordinates) : Prop :=
  ∀ first second,
    holonomicDiagonalPair magnitude (transition first) (transition second) =
      holonomicDiagonalPair magnitude first second

/-- Exact overlap criterion: local tensors glue precisely under diagonal
pairing-preserving frame transitions. -/
theorem localHolonomicDiagonalTensor_eq_iff_transition_preserves
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (firstAnchor secondAnchor point : EffectiveQuotient period hPeriod)
    (hFirst : point ∈
      localTangentFrameDomain period hPeriod firstAnchor)
    (hSecond : point ∈
      localTangentFrameDomain period hPeriod secondAnchor) :
    localHolonomicDiagonalTensor period hPeriod magnitude hPositive
        firstAnchor point hFirst =
      localHolonomicDiagonalTensor period hPeriod magnitude hPositive
        secondAnchor point hSecond ↔
      PreservesHolonomicDiagonalPair (magnitude point)
        (localFrameTransition period hPeriod firstAnchor secondAnchor point
          hFirst hSecond) := by
  constructor
  · intro hTensor first second
    let firstTangent :=
      (localTangentCoordinateEquiv period hPeriod firstAnchor point hFirst).symm
        first
    let secondTangent :=
      (localTangentCoordinateEquiv period hPeriod firstAnchor point hFirst).symm
        second
    have hAtFirst := congrArg
      (fun tensor => tensor firstTangent) hTensor
    have hAtSecond := congrArg
      (fun covector => covector secondTangent) hAtFirst
    rw [localHolonomicDiagonalTensor_apply,
      localHolonomicDiagonalTensor_apply] at hAtSecond
    simpa [firstTangent, secondTangent, localFrameTransition] using hAtSecond.symm
  · intro hPreserves
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    rw [localHolonomicDiagonalTensor_apply,
      localHolonomicDiagonalTensor_apply]
    rw [← localFrameTransition_coordinates period hPeriod firstAnchor
      secondAnchor point hFirst hSecond first,
      ← localFrameTransition_coordinates period hPeriod firstAnchor
        secondAnchor point hFirst hSecond second]
    exact (hPreserves _ _).symm

/-- Global cocycle contract required to descend the local diagonal metrics. -/
def HolonomicDiagonalGluingCondition
    (magnitude : SmoothQuotientField period hPeriod Coefficients4) : Prop :=
  ∀ firstAnchor secondAnchor point
      (hFirst : point ∈
        localTangentFrameDomain period hPeriod firstAnchor)
      (hSecond : point ∈
        localTangentFrameDomain period hPeriod secondAnchor),
    PreservesHolonomicDiagonalPair (magnitude point)
      (localFrameTransition period hPeriod firstAnchor secondAnchor point
        hFirst hSecond)

theorem holonomicDiagonalGluingCondition_iff_local_tensors_eq
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index) :
    HolonomicDiagonalGluingCondition period hPeriod magnitude ↔
      ∀ firstAnchor secondAnchor point
        (hFirst : point ∈
          localTangentFrameDomain period hPeriod firstAnchor)
        (hSecond : point ∈
          localTangentFrameDomain period hPeriod secondAnchor),
        localHolonomicDiagonalTensor period hPeriod magnitude hPositive
            firstAnchor point hFirst =
          localHolonomicDiagonalTensor period hPeriod magnitude hPositive
            secondAnchor point hSecond := by
  constructor
  · intro hGluing firstAnchor secondAnchor point hFirst hSecond
    exact (localHolonomicDiagonalTensor_eq_iff_transition_preserves
      period hPeriod magnitude hPositive firstAnchor secondAnchor point
      hFirst hSecond).2 (hGluing firstAnchor secondAnchor point hFirst hSecond)
  · intro hTensors firstAnchor secondAnchor point hFirst hSecond
    exact (localHolonomicDiagonalTensor_eq_iff_transition_preserves
      period hPeriod magnitude hPositive firstAnchor secondAnchor point
      hFirst hSecond).1
      (hTensors firstAnchor secondAnchor point hFirst hSecond)

end

end P0EFTJanusMappingTorusLocalHolonomicDiagonalGluingCriterion4D
end JanusFormal
