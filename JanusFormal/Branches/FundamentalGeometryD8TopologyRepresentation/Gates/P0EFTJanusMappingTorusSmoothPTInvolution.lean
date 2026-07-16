import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusPTInvolution
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold

/-!
# Smooth PT involutions on the effective mapping-torus manifolds

The continuous time reversal already defined on the orbit quotients is lifted
through the covering local diffeomorphisms.  This proves that the same PT maps
are analytic diffeomorphisms of the actual three- and four-dimensional smooth
quotients.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothPTInvolution

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold

section GeneralDescent

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X]

/-- A smooth self-inverse lift descends smoothly through the covering-induced
mapping-torus atlas. -/
theorem mappingTorusTimeReversal_contMDiff
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (hSymm : data.monodromy.symm = data.monodromy)
    (hReverse : ContMDiff I I n (timeReverseCover data)) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    ContMDiff I I n (mappingTorusTimeReversal data hSymm) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  have hProjection :=
    mappingTorus_projection_isLocalDiffeomorph I n data hDeck
  have hLift : ContMDiff I I n
      (fun point => mappingTorusMk data (timeReverseCover data point)) :=
    hProjection.contMDiff.comp hReverse
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective data quotientPoint
  have hLocal := hProjection anchor
  have hLocalLift : ContMDiffAt I I n
      ((fun point => mappingTorusMk data (timeReverseCover data point)) ∘
        hLocal.localInverse)
      (mappingTorusMk data anchor) :=
    hLift.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hLocalLift.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with point hPoint
  rw [Function.comp_apply, ← mappingTorusTimeReversal_mk]
  exact congrArg (mappingTorusTimeReversal data hSymm) hPoint.symm

end GeneralDescent

section ConcreteQuotients

open P0EFTJanusReflectionFixedThroat

variable (period : ℝ) (hPeriod : period ≠ 0)

private theorem reflectedSphereProductTimeReverse_contMDiff :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (fun point : UnitThreeSphere × ℝ => (point.1, -point.2)) := by
  exact (contMDiff_id.prodMap contDiff_neg.contMDiff).congr fun _ => rfl

private theorem fixedThroatProductTimeReverse_contMDiff :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (fun point : EquatorialTwoSphere × ℝ => (point.1, -point.2)) := by
  exact (contMDiff_id.prodMap contDiff_neg.contMDiff).congr fun _ => rfl

/-- Time reversal is analytic on the reflected-sphere cover. -/
theorem reflectedSphereCover_timeReverse_contMDiff :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (timeReverseCover (reflectedSphereData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hComposite := hInv.comp
    (reflectedSphereProductTimeReverse_contMDiff.comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext <;> rfl

/-- Time reversal is analytic on the fixed-throat cover. -/
theorem fixedThroatCover_timeReverse_contMDiff :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (timeReverseCover (fixedEquatorData period hPeriod)) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hComposite := hInv.comp
    (fixedThroatProductTimeReverse_contMDiff.comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext <;> rfl

/-- PT is analytic on the effective four-dimensional quotient. -/
theorem reflectedSpherePT_contMDiff :
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (reflectedSpherePT period hPeriod) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  exact mappingTorusTimeReversal_contMDiff coverModelWithCorners ω
    (reflectedSphereData period hPeriod)
    (reflectedSphereCover_deck_contMDiff period hPeriod)
    sphereReflection_symm
    (reflectedSphereCover_timeReverse_contMDiff period hPeriod)

/-- PT is analytic on the effective three-dimensional throat quotient. -/
theorem fixedThroatPT_contMDiff :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (fixedThroatPT period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  exact mappingTorusTimeReversal_contMDiff throatCoverModelWithCorners ω
    (fixedEquatorData period hPeriod)
    (fixedThroatCover_deck_contMDiff period hPeriod)
    (fixedEquatorMonodromy_symm period hPeriod)
    (fixedThroatCover_timeReverse_contMDiff period hPeriod)

/-- The quotient PT involution as an analytic diffeomorphism. -/
def reflectedSpherePTDiffeomorph :
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    MappingTorus (reflectedSphereData period hPeriod) ≃ₘ^ω⟮
      coverModelWithCorners, coverModelWithCorners⟯
      MappingTorus (reflectedSphereData period hPeriod) := by
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  exact
    { toEquiv :=
        { toFun := reflectedSpherePT period hPeriod
          invFun := reflectedSpherePT period hPeriod
          left_inv := reflectedSpherePT_involutive period hPeriod
          right_inv := reflectedSpherePT_involutive period hPeriod }
      contMDiff_toFun := reflectedSpherePT_contMDiff period hPeriod
      contMDiff_invFun := reflectedSpherePT_contMDiff period hPeriod }

/-- The throat PT involution as an analytic diffeomorphism. -/
def fixedThroatPTDiffeomorph :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    MappingTorus (fixedEquatorData period hPeriod) ≃ₘ^ω⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      MappingTorus (fixedEquatorData period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  exact
    { toEquiv :=
        { toFun := fixedThroatPT period hPeriod
          invFun := fixedThroatPT period hPeriod
          left_inv := fixedThroatPT_involutive period hPeriod
          right_inv := fixedThroatPT_involutive period hPeriod }
      contMDiff_toFun := fixedThroatPT_contMDiff period hPeriod
      contMDiff_invFun := fixedThroatPT_contMDiff period hPeriod }

end ConcreteQuotients

end

end P0EFTJanusMappingTorusSmoothPTInvolution
end JanusFormal
