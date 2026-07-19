import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

/-!
# Pointwise stable radial tangent equivalence on the genuine D8 cover

At a point of the actual `S³ × ℝ` cover, the differential of the standard
sphere inclusion spans the hyperplane orthogonal to the unit radius.  Adding
the radial line therefore gives a genuine linear equivalence with ambient
Euclidean four-space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusStableRadialTangentTrivialization4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev SphereCoordinates := EuclideanSpace Real (Fin 3)

/-- Differential of the genuine standard-sphere inclusion at the cover
fiber point transported by `unitThreeSphereHomeomorph`. -/
def sphereInclusionDerivative (point : UnitThreeSphere) :
    SphereCoordinates →L[Real] EuclideanR4 where
  toFun vector :=
    mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point) vector
  map_add' first second := by
    exact (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point)).map_add first second
  map_smul' scalar vector := by
    exact (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point)).map_smul scalar vector
  cont := by
    exact (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point)).continuous

theorem sphereInclusionDerivative_range (point : UnitThreeSphere) :
    (sphereInclusionDerivative point).range =
      (Real ∙ sphereAmbientMap point)ᗮ := by
  ext vector
  constructor
  · rintro ⟨preimage, rfl⟩
    have hMem :
        mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
            ((↑) : StandardSphere → EuclideanR4)
            (unitThreeSphereHomeomorph point) preimage ∈
          (Real ∙ (unitThreeSphereHomeomorph point : EuclideanR4))ᗮ := by
      rw [← range_mfderiv_coe_sphere (n := 3)
        (unitThreeSphereHomeomorph point)]
      exact ⟨preimage, rfl⟩
    change sphereInclusionDerivative point preimage ∈
      (Real ∙ sphereAmbientMap point)ᗮ at hMem
    exact hMem
  · intro hVector
    have hMem : vector ∈
        (Real ∙ (unitThreeSphereHomeomorph point : EuclideanR4))ᗮ := by
      simpa [sphereAmbientMap] using hVector
    rw [← range_mfderiv_coe_sphere (n := 3)
      (unitThreeSphereHomeomorph point)] at hMem
    obtain ⟨preimage, hPreimage⟩ := hMem
    change sphereInclusionDerivative point preimage = vector at hPreimage
    exact ⟨preimage, hPreimage⟩

theorem sphereInclusionDerivative_injective (point : UnitThreeSphere) :
    Function.Injective (sphereInclusionDerivative point) := by
  intro first second hEqual
  exact (mfderiv_coe_sphere_injective (n := 3)
    (unitThreeSphereHomeomorph point)) hEqual

/-- Stable radial map
`(u, τ) ↦ dι_q(u) + τ q` at a point of the actual `S³ × ℝ` cover. -/
def stableRadialTangentMap
    (point : EffectiveCover period hPeriod) :
    CoverCoordinates →L[Real] EuclideanR4 :=
  (sphereInclusionDerivative point.fiber).comp
      (ContinuousLinearMap.fst Real SphereCoordinates Real) +
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.snd Real SphereCoordinates Real)
      (sphereAmbientMap point.fiber)

@[simp]
theorem stableRadialTangentMap_apply
    (point : EffectiveCover period hPeriod) (input : CoverCoordinates) :
    stableRadialTangentMap period hPeriod point input =
      sphereInclusionDerivative point.fiber input.1 +
        input.2 • sphereAmbientMap point.fiber := by
  rfl

theorem stableRadialTangentMap_injective
    (point : EffectiveCover period hPeriod) :
    Function.Injective (stableRadialTangentMap period hPeriod point) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro input hZero
  have hSum :
      sphereInclusionDerivative point.fiber input.1 +
          input.2 • sphereAmbientMap point.fiber = 0 := by
    simpa using hZero
  have hTangent :
      sphereInclusionDerivative point.fiber input.1 ∈
        (Real ∙ sphereAmbientMap point.fiber)ᗮ := by
    rw [← sphereInclusionDerivative_range]
    exact ⟨input.1, rfl⟩
  have hRadialEq :
      input.2 • sphereAmbientMap point.fiber =
        -sphereInclusionDerivative point.fiber input.1 := by
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hSum)
  have hRadialOrthogonal :
      input.2 • sphereAmbientMap point.fiber ∈
        (Real ∙ sphereAmbientMap point.fiber)ᗮ := by
    rw [hRadialEq]
    exact Submodule.neg_mem _ hTangent
  have hInner :
      inner Real (sphereAmbientMap point.fiber)
          (input.2 • sphereAmbientMap point.fiber) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      hRadialOrthogonal
  rw [real_inner_smul_right] at hInner
  have hPointNe : sphereAmbientMap point.fiber ≠ 0 := by
    exact ne_zero_of_mem_unit_sphere
      (unitThreeSphereHomeomorph point.fiber)
  have hInnerNe :
      inner Real (sphereAmbientMap point.fiber)
          (sphereAmbientMap point.fiber) ≠ 0 :=
    inner_self_ne_zero.mpr hPointNe
  have hTime : input.2 = 0 :=
    (mul_eq_zero.mp hInner).resolve_right hInnerNe
  have hSpatialImage : sphereInclusionDerivative point.fiber input.1 = 0 := by
    simpa [hTime] using hSum
  have hSpatial : input.1 = 0 := by
    apply sphereInclusionDerivative_injective point.fiber
    simpa using hSpatialImage
  exact Prod.ext hSpatial hTime

/-- The stable radial map is a pointwise continuous linear equivalence.
Smooth dependence on `point`, deck equivariance and descent through the
orientation-reversing mapping-torus quotient are not asserted here. -/
def stableRadialTangentEquiv
    (point : EffectiveCover period hPeriod) :
    CoverCoordinates ≃L[Real] EuclideanR4 :=
  (LinearMap.linearEquivOfInjective
    (stableRadialTangentMap period hPeriod point).toLinearMap
    (stableRadialTangentMap_injective period hPeriod point)
    (by simp [CoverCoordinates, EuclideanR4])).toContinuousLinearEquiv

@[simp]
theorem stableRadialTangentEquiv_apply
    (point : EffectiveCover period hPeriod) (input : CoverCoordinates) :
    stableRadialTangentEquiv period hPeriod point input =
      stableRadialTangentMap period hPeriod point input := by
  rfl

end

end P0EFTJanusMappingTorusStableRadialTangentTrivialization4D
end JanusFormal
