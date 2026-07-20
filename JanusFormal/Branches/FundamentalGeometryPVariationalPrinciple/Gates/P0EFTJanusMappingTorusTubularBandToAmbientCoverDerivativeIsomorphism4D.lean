import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D

/-!
# Differential certificate from the tubular band to the ambient cover
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private def openSubtypePartialDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners Real E H) (U : TopologicalSpace.Opens M) (base : U) :
    PartialDiffeomorph I I U M ∞ := by
  letI : Nonempty U := ⟨base⟩
  exact
    { __ := U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        intro point hPoint
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
        apply contMDiffWithinAt_id.congr_of_mem _ hPoint
        intro target hTarget
        exact U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_right_inv
          Subtype.val hTarget }

private def partialDiffeomorphProd
    {E H M E' H' M' F G N F' G' N' : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M']
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace G]
    [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup F'] [NormedSpace Real F'] [TopologicalSpace G']
    [TopologicalSpace N'] [ChartedSpace G' N']
    {I : ModelWithCorners Real E H} {I' : ModelWithCorners Real E' H'}
    {J : ModelWithCorners Real F G} {J' : ModelWithCorners Real F' G'}
    {n : ℕ∞}
    (Φ : PartialDiffeomorph I I' M M' n)
    (Ψ : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn

private def ambientCoverProductDiffeomorph :
    AmbientCover period hPeriod ≃ₘ^∞⟮coverModelWithCorners,
      coverModelWithCorners⟯ UnitThreeSphere × Real where
  toEquiv := (coverHomeomorphProd (reflectedSphereData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPeriod))

private theorem productTubularBandInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (Prod.map (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere)
        (id : Real → Real)) := by
  intro point
  let fiberMap := openSubtypePartialDiffeomorph (𝓡 3)
    equatorialSphericalBandOpen point.1
  let timeMap :=
    (Diffeomorph.refl (modelWithCornersSelf Real Real) Real ∞).toPartialDiffeomorph
  refine ⟨partialDiffeomorphProd fiberMap timeMap,
    ⟨Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
  rintro ⟨fiber, time⟩ -
  rfl

/-- Include the open tubular band in the ambient mapping-torus cover. -/
def tubularBandSpacetimeToAmbientCover
    (point : equatorialSphericalBandOpen × Real) : AmbientCover period hPeriod :=
  (ambientCoverProductDiffeomorph period hPeriod).symm
    (Prod.map (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere)
      (id : Real → Real) point)

theorem tubularBandSpacetimeToAmbientCover_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (tubularBandSpacetimeToAmbientCover period hPeriod) := by
  intro point
  have hFirst := productTubularBandInclusion_isLocalDiffeomorph point
  have hSecond := (ambientCoverProductDiffeomorph period hPeriod).symm
    |>.isLocalDiffeomorph
      (Prod.map (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere)
        (id : Real → Real) point)
  exact hFirst.comp coverModelWithCorners _ hSecond

theorem tubularBandSpacetimeToAmbientCover_derivative_isomorphism
    (point : equatorialSphericalBandOpen × Real) :
    ∃ derivative : TangentSpace coverModelWithCorners point ≃L[Real]
        TangentSpace coverModelWithCorners
          (tubularBandSpacetimeToAmbientCover period hPeriod point),
      (derivative : TangentSpace coverModelWithCorners point →L[Real]
        TangentSpace coverModelWithCorners
          (tubularBandSpacetimeToAmbientCover period hPeriod point)) =
        mfderiv coverModelWithCorners coverModelWithCorners
          (tubularBandSpacetimeToAmbientCover period hPeriod) point := by
  let hLocal := tubularBandSpacetimeToAmbientCover_isLocalDiffeomorph
    period hPeriod point
  let derivative := hLocal.mfderivToContinuousLinearEquiv (by simp)
  exact ⟨derivative,
    hLocal.mfderivToContinuousLinearEquiv_coe (by simp)⟩

private def analyticPartialDiffeomorphToSmooth
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoverModel M] [ChartedSpace CoverModel N]
    (Φ : PartialDiffeomorph coverModelWithCorners coverModelWithCorners M N ω) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners M N ∞ where
  __ := Φ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.of_le (by simp)
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le (by simp)

private theorem localDiffeomorphSmooth_of_analytic
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoverModel M] [ChartedSpace CoverModel N]
    {function : M → N}
    (hFunction : IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω function) :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞ function := by
  intro point
  rcases hFunction point with ⟨Φ, hPoint, hEq⟩
  exact ⟨analyticPartialDiffeomorphToSmooth Φ, hPoint, hEq⟩

/-- Tubular-band coordinates mapped to the ambient mapping-torus quotient. -/
def tubularBandSpacetimeToAmbient
    (point : equatorialSphericalBandOpen × Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (reflectedSphereData period hPeriod)
    (tubularBandSpacetimeToAmbientCover period hPeriod point)

theorem tubularBandSpacetimeToAmbient_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (tubularBandSpacetimeToAmbient period hPeriod) := by
  intro point
  have hCover := tubularBandSpacetimeToAmbientCover_isLocalDiffeomorph
    period hPeriod point
  have hProjection := localDiffeomorphSmooth_of_analytic
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (tubularBandSpacetimeToAmbientCover period hPeriod point)
  exact hCover.comp coverModelWithCorners _ hProjection

theorem tubularBandSpacetimeToAmbient_derivative_isomorphism
    (point : equatorialSphericalBandOpen × Real) :
    ∃ derivative : TangentSpace coverModelWithCorners point ≃L[Real]
        TangentSpace coverModelWithCorners
          (tubularBandSpacetimeToAmbient period hPeriod point),
      (derivative : TangentSpace coverModelWithCorners point →L[Real]
        TangentSpace coverModelWithCorners
          (tubularBandSpacetimeToAmbient period hPeriod point)) =
        mfderiv coverModelWithCorners coverModelWithCorners
          (tubularBandSpacetimeToAmbient period hPeriod) point := by
  let hLocal := tubularBandSpacetimeToAmbient_isLocalDiffeomorph
    period hPeriod point
  let derivative := hLocal.mfderivToContinuousLinearEquiv (by simp)
  exact ⟨derivative,
    hLocal.mfderivToContinuousLinearEquiv_coe (by simp)⟩

end
end P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
end JanusFormal
