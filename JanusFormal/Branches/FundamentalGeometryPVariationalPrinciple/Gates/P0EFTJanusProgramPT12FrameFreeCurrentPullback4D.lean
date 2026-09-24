import Mathlib.Geometry.Manifold.VectorField.Pullback
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-! Genuine smooth coordinate pullback of tangent currents.
Only the patch's local diffeomorphism is used; no metric or global basis is required. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (patch : SmoothHolonomicFrameChart4 period hPeriod)

/-- The actual coordinate derivative, with its inverse furnished by the patch. -/
def frameFreeCoordinateDerivativeEquiv (coordinate : Vector4) :
    TangentSpace (modelWithCornersSelf Real Vector4) coordinate ≃L[Real]
      TangentSpace coverModelWithCorners (patch.coordinateMap coordinate) :=
  patch.coordinateMap_isLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) coordinate

theorem frameFreeCoordinateDerivativeEquiv_coe (coordinate : Vector4) :
    (frameFreeCoordinateDerivativeEquiv period hPeriod patch coordinate :
      TangentSpace (modelWithCornersSelf Real Vector4) coordinate →L[Real]
        TangentSpace coverModelWithCorners (patch.coordinateMap coordinate)) =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate :=
  patch.coordinateMap_isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (by simp) coordinate

variable (vector : SmoothTangentField period hPeriod)

def frameFreeCurrentPullback : Vector4 → Vector4 :=
  VectorField.mpullback (modelWithCornersSelf Real Vector4)
    coverModelWithCorners patch.coordinateMap vector

theorem frameFreeCurrentPullback_apply (coordinate : Vector4) :
    frameFreeCurrentPullback period hPeriod patch vector coordinate =
      (frameFreeCoordinateDerivativeEquiv period hPeriod patch coordinate).symm
        (vector (patch.coordinateMap coordinate)) := by
  change (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
    patch.coordinateMap coordinate).inverse _ = _
  rw [← frameFreeCoordinateDerivativeEquiv_coe, ContinuousLinearMap.inverse_equiv]
  rfl

theorem frameFreeCurrentPullback_contDiff :
    ContDiff Real ∞ (frameFreeCurrentPullback period hPeriod patch vector) := by
  change ContDiff Real ∞ (VectorField.mpullback
    (modelWithCornersSelf Real Vector4) coverModelWithCorners patch.coordinateMap vector)
  apply contMDiff_vectorSpace_iff_contDiff.mp
  apply vector.contMDiff_toFun.mpullback_vectorField patch.coordinateMap_contMDiff
  · intro coordinate
    rw [← frameFreeCoordinateDerivativeEquiv_coe]
    exact ContinuousLinearMap.isInvertible_equiv
  · simp

theorem frameFreeCurrentPullback_pushforward (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (frameFreeCurrentPullback period hPeriod patch vector coordinate) =
      vector (patch.coordinateMap coordinate) := by
  rw [← frameFreeCoordinateDerivativeEquiv_coe, frameFreeCurrentPullback_apply]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

/-- Ordinary differentiation in the chart recovers the intrinsic scalar differential. -/
theorem frameFreeCurrentPullback_scalarDifferential
    (field : SmoothQuotientField period hPeriod Real) (coordinate : Vector4) :
    fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate
        (frameFreeCurrentPullback period hPeriod patch vector coordinate) =
      scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
        (vector (patch.coordinateMap coordinate)) := by
  have hChain := mfderiv_comp coordinate
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp))
  have hApplied := congrArg
    (fun derivative => derivative (frameFreeCurrentPullback period hPeriod patch vector coordinate))
    hChain
  rw [mfderiv_eq_fderiv] at hApplied
  change fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate
    (frameFreeCurrentPullback period hPeriod patch vector coordinate) =
    scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (frameFreeCurrentPullback period hPeriod patch vector coordinate)) at hApplied
  rw [frameFreeCurrentPullback_pushforward] at hApplied
  exact hApplied

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
