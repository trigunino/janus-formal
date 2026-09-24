import Mathlib.Geometry.Manifold.VectorField.Pullback
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-! Smooth lifting of quotient tangent fields and continuous genuine radial coordinates.
The lift uses the inverse of the actual quotient derivative; its regularity is proved,
rather than supplied as a hypothesis. -/
namespace JanusFormal.P0EFTJanusProgramPT12LiftedFrameContinuity4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveCover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The genuine inverse-derivative pullback is a smooth cover tangent field. -/
def liftedQuotientTangentField (vector : SmoothTangentField period hPeriod) :
    ContMDiffSection coverModelWithCorners CoverCoordinates ∞
      (fun point : EffectiveCover period hPeriod => TangentSpace coverModelWithCorners point) where
  toFun := VectorField.mpullback coverModelWithCorners coverModelWithCorners
    (mappingTorusMk (reflectedSphereData period hPeriod)) vector
  contMDiff_toFun := by
    have hProjection : ContMDiff coverModelWithCorners coverModelWithCorners ∞
        (mappingTorusMk (reflectedSphereData period hPeriod)) :=
      (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff.of_le (by simp)
    apply vector.contMDiff_toFun.mpullback_vectorField hProjection
    · intro point
      rw [← quotientProjectionDerivativeEquiv_coe]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp

theorem liftedQuotientTangentField_apply (vector : SmoothTangentField period hPeriod)
    (point : EffectiveCover period hPeriod) :
    liftedQuotientTangentField period hPeriod vector point =
      (quotientProjectionDerivativeEquiv period hPeriod point).symm
        (vector (mappingTorusMk (reflectedSphereData period hPeriod) point)) := by
  change (mfderiv coverModelWithCorners coverModelWithCorners
    (mappingTorusMk (reflectedSphereData period hPeriod)) point).inverse _ = _
  rw [← quotientProjectionDerivativeEquiv_coe, ContinuousLinearMap.inverse_equiv]
  rfl

theorem liftedQuotientTangentField_projection (vector : SmoothTangentField period hPeriod)
    (point : EffectiveCover period hPeriod) :
    quotientProjectionDerivativeEquiv period hPeriod point
        (liftedQuotientTangentField period hPeriod vector point) =
      vector (mappingTorusMk (reflectedSphereData period hPeriod) point) := by
  rw [liftedQuotientTangentField_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem liftedQuotientTangentField_contMDiff (vector : SmoothTangentField period hPeriod) :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point : EffectiveCover period hPeriod =>
        (⟨point, liftedQuotientTangentField period hPeriod vector point⟩ :
          TangentBundle coverModelWithCorners (EffectiveCover period hPeriod))) :=
  (liftedQuotientTangentField period hPeriod vector).contMDiff_toFun

/-- Ambient derivative coordinates of the lifted vector are smooth. -/
theorem liftedQuotientTangentField_ambient_contMDiff (vector : SmoothTangentField period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, EuclideanR4 × Real) ∞
      (fun point : EffectiveCover period hPeriod =>
        coverAmbientDerivative period hPeriod point
          (liftedQuotientTangentField period hPeriod vector point)) := by
  have h := (contMDiff_snd_tangentBundle_modelSpace
    (EuclideanR4 × Real) 𝓘(Real, EuclideanR4 × Real)).comp
      (((coverAmbientMap_contMDiff period hPeriod).contMDiff_tangentMap (by simp)).comp
        (liftedQuotientTangentField_contMDiff period hPeriod vector))
  exact h

def liftedQuotientRadialCoordinates (vector : SmoothTangentField period hPeriod)
    (point : EffectiveCover period hPeriod) : EuclideanR4 :=
  genuineStableRadialTangentEquiv period hPeriod point
    (liftedQuotientTangentField period hPeriod vector point)

theorem liftedQuotientRadialCoordinates_apply (vector : SmoothTangentField period hPeriod)
    (point : EffectiveCover period hPeriod) :
    liftedQuotientRadialCoordinates period hPeriod vector point =
      (coverAmbientDerivative period hPeriod point
        (liftedQuotientTangentField period hPeriod vector point)).1 +
      (coverAmbientDerivative period hPeriod point
        (liftedQuotientTangentField period hPeriod vector point)).2 • sphereAmbientMap point.fiber :=
  genuineStableRadialTangentEquiv_apply period hPeriod point _

/-- Pointwise radial equivalences yield continuous coordinates on every smooth lifted field. -/
theorem liftedQuotientRadialCoordinates_continuous (vector : SmoothTangentField period hPeriod) :
    Continuous (liftedQuotientRadialCoordinates period hPeriod vector) := by
  have hAmbient := (liftedQuotientTangentField_ambient_contMDiff period hPeriod vector).continuous
  have hSphere : Continuous (fun point : EffectiveCover period hPeriod => sphereAmbientMap point.fiber) :=
    (coverAmbientMap_contMDiff period hPeriod).continuous.fst
  have h := hAmbient.fst.add (hAmbient.snd.smul hSphere)
  exact h.congr fun point => (liftedQuotientRadialCoordinates_apply period hPeriod vector point).symm

end
end JanusFormal.P0EFTJanusProgramPT12LiftedFrameContinuity4D
