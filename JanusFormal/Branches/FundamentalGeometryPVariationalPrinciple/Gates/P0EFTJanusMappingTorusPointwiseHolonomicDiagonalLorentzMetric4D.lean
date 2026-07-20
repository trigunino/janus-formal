import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalHolonomicDiagonalGluingCriterion4D

/-!
# Canonical pointwise holonomic diagonal Lorentz metric

Choosing the tangent-trivialization patch centered at each point produces a
global pointwise musical and tensor family.  They are nondegenerate and
Lorentzian.  Under the exact overlap cocycle they agree with every local
realization.  Smoothness of the assembled family is not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPointwiseHolonomicDiagonalLorentzMetric4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D
open P0EFTJanusMappingTorusLocalHolonomicDiagonalGluingCriterion4D

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

/-- Pointwise musical obtained from the canonical patch centered at the same
point. -/
def pointwiseHolonomicDiagonalMusical
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
  localHolonomicDiagonalMusical period hPeriod magnitude hPositive point point
    (anchor_mem_localTangentFrameDomain period hPeriod point)

/-- Global pointwise covariant tensor family selected by the centered local
patches. -/
def pointwiseHolonomicDiagonalTensor
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index) :
    CovariantTwoTensorField period hPeriod :=
  fun point =>
    (pointwiseHolonomicDiagonalMusical period hPeriod magnitude hPositive point
      ).toContinuousLinearMap

theorem pointwiseHolonomicDiagonalTensor_eq_musical
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    pointwiseHolonomicDiagonalTensor period hPeriod magnitude hPositive point =
      (pointwiseHolonomicDiagonalMusical period hPeriod magnitude hPositive
        point).toContinuousLinearMap :=
  rfl

theorem pointwiseHolonomicDiagonalTensor_nondegenerate
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    FiberIsNondegenerate period hPeriod
      (pointwiseHolonomicDiagonalTensor period hPeriod magnitude hPositive
        point) := by
  rw [pointwiseHolonomicDiagonalTensor_eq_musical]
  exact (pointwiseHolonomicDiagonalMusical period hPeriod magnitude hPositive
    point).injective

theorem pointwiseHolonomicDiagonalTensor_lorentzian
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    FiberIsLorentzian period hPeriod
      (pointwiseHolonomicDiagonalTensor period hPeriod magnitude hPositive
        point) :=
  localHolonomicDiagonalTensor_lorentzian period hPeriod magnitude hPositive
    point point (anchor_mem_localTangentFrameDomain period hPeriod point)

/-- Under the overlap cocycle, the centered pointwise tensor equals every
local pulled-back tensor containing that point. -/
theorem pointwiseHolonomicDiagonalTensor_eq_local
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (hGluing : HolonomicDiagonalGluingCondition period hPeriod magnitude)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    pointwiseHolonomicDiagonalTensor period hPeriod magnitude hPositive point =
      localHolonomicDiagonalTensor period hPeriod magnitude hPositive
        anchor point hPoint := by
  exact (holonomicDiagonalGluingCondition_iff_local_tensors_eq
    period hPeriod magnitude hPositive).1 hGluing point anchor point
      (anchor_mem_localTangentFrameDomain period hPeriod point) hPoint

end

end P0EFTJanusMappingTorusPointwiseHolonomicDiagonalLorentzMetric4D
end JanusFormal
