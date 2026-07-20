import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalFrameNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicDiagonalVolumeBridge4D

/-!
# Local intrinsic realization of the holonomic diagonal metric

On every canonical tangent-trivialization patch, the exact holonomic model
musical pulls back to the genuine tangent fiber.  The resulting local tensor
is nondegenerate and Lorentzian.  No global smooth frame is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D

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
open P0EFTJanusMappingTorusHolonomicDiagonalMusical4D
open P0EFTJanusMappingTorusHolonomicDiagonalLorentzFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

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

/-- Pullback of the exact holonomic diagonal musical through one canonical
local tangent trivialization. -/
def localHolonomicDiagonalMusical
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point ≃L[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
  let coordinates :=
    localTangentCoordinateEquiv period hPeriod anchor point hPoint
  coordinates.trans
    ((holonomicDiagonalMusical (magnitude point)
      (fun index => ne_of_gt (hPositive point index))).trans
      (coordinates.symm.arrowCongr
        (ContinuousLinearEquiv.refl Real Real)))

/-- Genuine local covariant tensor represented by the pulled-back musical. -/
def localHolonomicDiagonalTensor
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point →L[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
  (localHolonomicDiagonalMusical period hPeriod magnitude hPositive
    anchor point hPoint).toContinuousLinearMap

/-- Local Lorentz frame obtained by composing the tangent trivialization with
the explicit square-root-scaled holonomic frame. -/
def localHolonomicDiagonalLorentzFrame
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point ≃L[Real] CoverCoordinates :=
  (localTangentCoordinateEquiv period hPeriod anchor point hPoint).trans
    (holonomicDiagonalLorentzFrame (magnitude point) (hPositive point))

theorem localHolonomicDiagonalTensor_apply
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor)
    (first second : TangentFiber period hPeriod point) :
    localHolonomicDiagonalTensor period hPeriod magnitude hPositive
        anchor point hPoint first second =
      holonomicDiagonalPair (magnitude point)
        (localTangentCoordinateEquiv period hPeriod anchor point hPoint first)
        (localTangentCoordinateEquiv period hPeriod anchor point hPoint second) := by
  rfl

/-- Each local realization has Lorentz inertia `(3,1)` on the actual tangent
fiber. -/
theorem localHolonomicDiagonalTensor_lorentzian
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    FiberIsLorentzian period hPeriod
      (localHolonomicDiagonalTensor period hPeriod magnitude hPositive
        anchor point hPoint) := by
  refine ⟨localHolonomicDiagonalLorentzFrame period hPeriod magnitude hPositive
    anchor point hPoint, ?_⟩
  intro first second
  rw [localHolonomicDiagonalTensor_apply]
  exact holonomicDiagonalPair_eq_modelMinkowskiPair
    (magnitude point) (hPositive point) _ _

@[simp]
theorem localHolonomicDiagonalMusical_inverse
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    localHolonomicDiagonalMusical period hPeriod magnitude hPositive
        anchor point hPoint
        ((localHolonomicDiagonalMusical period hPeriod magnitude hPositive
          anchor point hPoint).symm covector) = covector := by
  simp

end

end P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D
end JanusFormal
