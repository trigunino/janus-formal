import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeBRST4D

/-!
# Global zero modes of the abelian gauge differential on D8

The effective reflected-sphere mapping torus is connected.  On this actual
quotient, a smooth `U(1)^2` ghost has vanishing intrinsic exterior derivative
exactly when it is globally constant.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

noncomputable local instance standardUnitThreeSphereConnectedSpace :
    ConnectedSpace StandardUnitThreeSphere := by
  have hRank : 1 < Module.rank Real EuclideanR4 := by
    rw [← Module.finrank_eq_rank]
    norm_num [finrank_euclideanSpace_fin]
  exact Subtype.connectedSpace
    (isConnected_sphere hRank (0 : EuclideanR4) (r := (1 : Real)) (by norm_num))

noncomputable local instance unitThreeSphereConnectedSpace :
    ConnectedSpace UnitThreeSphere :=
  unitThreeSphereHomeomorph.symm.surjective.connectedSpace
    unitThreeSphereHomeomorph.symm.continuous

noncomputable local instance effectiveCoverConnectedSpace :
    ConnectedSpace (EffectiveCover period hPeriod) :=
  (coverHomeomorphProd (sphereData period hPeriod)).symm.surjective.connectedSpace
    (coverHomeomorphProd (sphereData period hPeriod)).symm.continuous

noncomputable local instance effectiveQuotientConnectedSpace :
    ConnectedSpace (EffectiveQuotient period hPeriod) :=
  inferInstance

/-- The genuine reflected-sphere mapping torus has a point. -/
theorem effectiveQuotient_nonempty :
    Nonempty (MappingTorus (reflectedSphereData period hPeriod)) :=
  inferInstance

/-- On the boundaryless D8 quotient, a smooth real field with zero intrinsic
derivative is locally constant.  The proof is the ordinary mean-value theorem
in a convex ball contained in each extended chart. -/
private theorem realField_isLocallyConstant_of_mvfderiv_eq_zero
    (field : SmoothQuotientField period hPeriod Real)
    (hDerivative : ∀ point,
      mvfderiv coverModelWithCorners field.toFun point = 0) :
    IsLocallyConstant field.toFun := by
  have hMFDeriv : ∀ point,
      mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
        field.toFun point = 0 := by
    intro point
    apply ContinuousLinearMap.ext
    intro tangent
    apply (NormedSpace.fromTangentSpace (field.toFun point)).injective
    have hApply := congrArg (fun derivative => derivative tangent)
      (hDerivative point)
    simpa [mvfderiv] using hApply
  refine (IsLocallyConstant.iff_exists_open field.toFun).2 ?_
  intro point
  let center : CoverCoordinates := extChartAt coverModelWithCorners point point
  obtain ⟨radius, hRadius, hBall⟩ :=
    Metric.isOpen_iff.mp
      (isOpen_extChartAt_target point) center
      (mem_extChartAt_target point)
  let coordinateFunction : CoverCoordinates → Real :=
    field.toFun ∘ (extChartAt coverModelWithCorners point).symm
  have hChartAt (coordinate : CoverCoordinates)
      (hCoordinate : coordinate ∈ Metric.ball center radius) :
      MDifferentiableAt (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners
        (extChartAt coverModelWithCorners point).symm coordinate := by
    apply (mdifferentiableWithinAt_extChartAt_symm (hBall hCoordinate)).mdifferentiableAt
    rw [coverModelWithCorners.range_eq_univ]
    exact Filter.univ_mem
  have hFieldAt (coordinate : CoverCoordinates) :
      MDifferentiableAt coverModelWithCorners
        (modelWithCornersSelf Real Real) field.toFun
        ((extChartAt coverModelWithCorners point).symm coordinate) :=
    field.contMDiff_toFun.contMDiffAt.mdifferentiableAt (by simp)
  have hDifferentiableAt (coordinate : CoverCoordinates)
      (hCoordinate : coordinate ∈ Metric.ball center radius) :
      DifferentiableAt Real coordinateFunction coordinate := by
    have hComposition :=
      (hFieldAt coordinate).comp coordinate (hChartAt coordinate hCoordinate)
    simpa [coordinateFunction] using hComposition.differentiableAt
  have hFDerivAt (coordinate : CoverCoordinates)
      (hCoordinate : coordinate ∈ Metric.ball center radius) :
      fderiv Real coordinateFunction coordinate = 0 := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real Real)
      (field.toFun ∘ (extChartAt coverModelWithCorners point).symm) coordinate = 0
    rw [mfderiv_comp coordinate (hFieldAt coordinate)
      (hChartAt coordinate hCoordinate),
      hMFDeriv ((extChartAt coverModelWithCorners point).symm coordinate)]
    apply ContinuousLinearMap.ext
    intro tangent
    rfl
  have hDifferentiableOn :
      DifferentiableOn Real coordinateFunction (Metric.ball center radius) :=
    fun coordinate hCoordinate =>
      (hDifferentiableAt coordinate hCoordinate).differentiableWithinAt
  have hFDerivWithin : ∀ coordinate ∈ Metric.ball center radius,
      fderivWithin Real coordinateFunction (Metric.ball center radius) coordinate = 0 := by
    intro coordinate hCoordinate
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hCoordinate,
      hFDerivAt coordinate hCoordinate]
  let modelBall : Set CoverModel :=
    coverModelWithCorners.toHomeomorph.symm '' Metric.ball center radius
  have hModelBallOpen : IsOpen modelBall := by
    exact coverModelWithCorners.toHomeomorph.symm.isOpenMap _ Metric.isOpen_ball
  have hModelBallTarget : modelBall ⊆ (chartAt CoverModel point).target := by
    rintro modelPoint ⟨coordinate, hCoordinate, rfl⟩
    have hExtendedTarget := hBall hCoordinate
    rw [extChartAt_target] at hExtendedTarget
    exact hExtendedTarget.1
  have hCenter :
      (chartAt CoverModel point).symm
        (coverModelWithCorners.toHomeomorph.symm center) = point := by
    have hExtendedCenter :
        (extChartAt coverModelWithCorners point).symm center = point := by
      dsimp [center]
      exact (extChartAt coverModelWithCorners point).left_inv
        (mem_extChartAt_source point)
    change (extChartAt coverModelWithCorners point).symm center = point
    exact hExtendedCenter
  refine ⟨(chartAt CoverModel point).symm ''
      modelBall, ?_, ?_, ?_⟩
  · exact (chartAt CoverModel point).isOpen_image_symm_of_subset_target
      hModelBallOpen hModelBallTarget
  · refine ⟨coverModelWithCorners.toHomeomorph.symm center, ?_, hCenter⟩
    exact ⟨center, mem_ball_self hRadius, rfl⟩
  · intro nearby hNearby
    rcases hNearby with ⟨modelPoint, hModelPoint, rfl⟩
    rcases hModelPoint with ⟨coordinate, hCoordinate, rfl⟩
    have hConstant :=
      (convex_ball center radius).is_const_of_fderivWithin_eq_zero
        hDifferentiableOn hFDerivWithin hCoordinate (mem_ball_self hRadius)
    change field.toFun ((extChartAt coverModelWithCorners point).symm coordinate) =
      field.toFun ((extChartAt coverModelWithCorners point).symm center) at hConstant
    have hConstantChart :
        field.toFun ((chartAt CoverModel point).symm
          (coverModelWithCorners.toHomeomorph.symm coordinate)) =
        field.toFun ((chartAt CoverModel point).symm
          (coverModelWithCorners.toHomeomorph.symm center)) := by
      change field.toFun ((extChartAt coverModelWithCorners point).symm coordinate) =
        field.toFun ((extChartAt coverModelWithCorners point).symm center)
      exact hConstant
    rw [hCenter] at hConstantChart
    exact hConstantChart

/-- A smooth real field with zero intrinsic derivative is globally constant
on the connected effective D8 quotient. -/
private theorem realField_eq_of_mvfderiv_eq_zero
    (field : SmoothQuotientField period hPeriod Real)
    (hDerivative : ∀ point,
      mvfderiv coverModelWithCorners field.toFun point = 0)
    (first second : EffectiveQuotient period hPeriod) :
    field first = field second :=
  IsLocallyConstant.apply_eq_of_preconnectedSpace
    (realField_isLocallyConstant_of_mvfderiv_eq_zero
      period hPeriod field hDerivative) first second

/-- The kernel of the actual global abelian gauge differential on D8 consists
exactly of the constant `R^2` ghosts. -/
theorem exactGaugePotential_eq_zero_iff_exists_constant
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    exactGaugePotential period hPeriod ghost = 0 ↔
      ∃ value : GaugeLieAlgebra,
        ∀ point : EffectiveQuotient period hPeriod, ghost point = value := by
  constructor
  · intro hZero
    have hComponentConstant (component : Fin 2)
        (first second : EffectiveQuotient period hPeriod) :
        ghostComponent period hPeriod ghost component first =
          ghostComponent period hPeriod ghost component second := by
      apply realField_eq_of_mvfderiv_eq_zero period hPeriod
      intro point
      have hAtPoint := congrArg
        (fun potential => potential.toFun component point) hZero
      change mvfderiv coverModelWithCorners
        (ghostComponent period hPeriod ghost component).toFun point = 0 at hAtPoint
      exact hAtPoint
    let anchor : EffectiveQuotient period hPeriod := Classical.arbitrary _
    refine ⟨ghost anchor, ?_⟩
    intro point
    apply (EuclideanSpace.equiv (Fin 2) Real).injective
    funext component
    exact hComponentConstant component point anchor
  · rintro ⟨value, hConstant⟩
    apply SmoothAbelianGaugePotential.ext
    intro component point tangent
    change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod ghost component).toFun point tangent = 0
    have hComponentFunction :
        (ghostComponent period hPeriod ghost component).toFun =
          fun _ : EffectiveQuotient period hPeriod =>
            EuclideanSpace.proj component value := by
      funext quotientPoint
      exact congrArg (EuclideanSpace.proj component) (hConstant quotientPoint)
    rw [hComponentFunction, mvfderiv_const]
    rfl

end

end P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
end JanusFormal
