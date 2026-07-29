import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanSmoothBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

/-!
# Global smooth Maxwell Cartan action

The finite smooth tangent generators already separate every tangent fiber.
On a patch where one partition weight is nonzero, their values are a rescaled
local frame.  Smooth local-frame coefficients therefore promote the
fiberwise Cartan covectors to genuine smooth gauge potentials.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialCartanGlobalAction4D

set_option autoImplicit false

noncomputable section

open Bundle Filter Module Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGaugePotentialCartanFiber4D
open P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D
open P0EFTJanusMappingTorusGaugePotentialCartanSmoothBundle4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def cartanGhostContraction
    (ghost : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    CInfinityScalarField period hPeriod :=
  ⟨fun point => potential.toFun component point (ghost point),
    (potential.contMDiff_eval component).comp ghost.contMDiff⟩

private def cartanGeneratorValue
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (second : Ghost period hPeriod) :
    CInfinityScalarField period hPeriod :=
  cInfinityScalarLieDerivative period hPeriod first
      (cartanGhostContraction period hPeriod second potential component) -
    cartanGhostContraction period hPeriod
      (smoothGhostLieBracket period hPeriod first second) potential component

@[simp]
private theorem cartanGeneratorValue_apply
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (second : Ghost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    cartanGeneratorValue period hPeriod first potential component second point =
      smoothGaugePotentialCartanFiberCovector
        period hPeriod first potential component point (second point) := by
  rw [smoothGaugePotentialCartanFiberCovector_apply]
  rfl

private def localGeneratorCoefficient
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod)) : Real :=
  finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
    vector.1 vector.2

private theorem localGeneratorCoefficient_contMDiffAt
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod))
    (hPoint :
      vector.1 ∈ finiteTangentGeneratorOpenPatch period hPeriod patch) :
    ContMDiffAt coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (localGeneratorCoefficient period hPeriod patch basisIndex) vector := by
  change
    ContMDiffAt coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (fun current =>
        finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
          current.1 current.2)
      vector
  exact finiteTangentGeneratorLocalCoefficient_contMDiffAt
    period hPeriod patch basisIndex vector hPoint

private def localCartanEvaluation
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod)) : Real :=
  ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
    (localGeneratorCoefficient period hPeriod patch basisIndex vector *
        (finiteTangentGeneratorWeight period hPeriod patch vector.1)⁻¹) *
      cartanGeneratorValue period hPeriod first potential component
        (finiteGeneratorCInfinityGhost period hPeriod
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, basisIndex))) vector.1

private theorem localCartanEvaluation_contMDiffAt
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod))
    (hPoint :
      vector.1 ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0) :
    ContMDiffAt coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (localCartanEvaluation period hPeriod first potential component patch)
      vector := by
  have hProjection :
      ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) => current.1) :=
    Bundle.contMDiff_proj
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
  have hWeightSmooth :
      ContMDiffAt coverModelWithCorners.tangent
        (modelWithCornersSelf Real Real) ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
            finiteTangentGeneratorWeight period hPeriod patch current.1)
        vector :=
    ((finiteTangentGeneratorWeight_contMDiff period hPeriod patch).comp
      hProjection).contMDiffAt
  unfold localCartanEvaluation
  apply ContMDiffAt.sum
  intro basisIndex _
  have hCoefficient :=
    localGeneratorCoefficient_contMDiffAt period hPeriod patch basisIndex
      vector hPoint
  have hGenerator :
      ContMDiffAt coverModelWithCorners.tangent
        (modelWithCornersSelf Real Real) ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
            cartanGeneratorValue period hPeriod first potential component
              (finiteGeneratorCInfinityGhost period hPeriod
                (finiteTangentGeneratorIndexEquivFin period hPeriod
                  (patch, basisIndex))) current.1) vector :=
    ((cartanGeneratorValue period hPeriod first potential component
      (finiteGeneratorCInfinityGhost period hPeriod
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex)))).contMDiff.comp
        hProjection).contMDiffAt
  exact (hCoefficient.mul (hWeightSmooth.inv₀ hWeight)).mul hGenerator

private theorem smoothGaugePotentialCartanFiberCovector_eq_local
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod))
    (hPoint :
      vector.1 ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0) :
    smoothGaugePotentialCartanFiberCovector
        period hPeriod first potential component vector.1 vector.2 =
      localCartanEvaluation period hPeriod first potential component patch
        vector := by
  let covector :=
    smoothGaugePotentialCartanFiberCovector
      period hPeriod first potential component vector.1
  rw [finiteTangentGeneratorLocalVector_reconstructs
    period hPeriod patch vector.1 hPoint vector.2]
  rw [map_sum]
  unfold localCartanEvaluation
  apply Finset.sum_congr rfl
  intro basisIndex _
  rw [map_smul]
  rw [cartanGeneratorValue_apply]
  change
    finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
          vector.1 vector.2 *
        covector
          (finiteTangentGeneratorLocalVector period hPeriod patch basisIndex
            vector.1) =
      (finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
            vector.1 vector.2 *
          (finiteTangentGeneratorWeight period hPeriod patch vector.1)⁻¹) *
        covector
          ((finiteSmoothTangentFrame period hPeriod).vectorAt vector.1
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, basisIndex)))
  rw [finiteSmoothTangentFrame_vectorAt_generator]
  rw [map_smul]
  simp only [smul_eq_mul]
  field_simp

/-- The fiberwise Maxwell Cartan covector is smooth uniformly in every
smooth ghost and smooth gauge potential. -/
def gaugePotentialCartanFiberSmoothness
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    GaugePotentialCartanFiberSmoothness period hPeriod first potential where
  contMDiff_eval := fun component vector => by
    obtain ⟨patch, hPatchBound⟩ :=
      exists_finiteTangentGeneratorWeight_ge_inv_card
        period hPeriod vector.1
    letI : Nonempty (FiniteTangentGeneratorPatch period hPeriod) :=
      ⟨patch⟩
    have hCard :
        0 < Fintype.card (FiniteTangentGeneratorPatch period hPeriod) :=
      Fintype.card_pos
    have hInvCard :
        0 < 1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) :=
      one_div_pos.mpr (by exact_mod_cast hCard)
    have hWeightPos :
        0 < finiteTangentGeneratorWeight period hPeriod patch vector.1 :=
      hInvCard.trans_le hPatchBound
    have hWeight :
        finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0 :=
      ne_of_gt hWeightPos
    have hPoint :
        vector.1 ∈ finiteTangentGeneratorOpenPatch period hPeriod patch := by
      apply finiteTangentGeneratorClosedPatch_subset_openPatch
        period hPeriod patch
      exact subset_closure hWeight
    have hProjection :
        ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
          (fun current : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) => current.1) :=
      Bundle.contMDiff_proj
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
    have hEventuallyPoint :
        ∀ᶠ current in 𝓝 vector,
          current.1 ∈
            finiteTangentGeneratorOpenPatch period hPeriod patch :=
      hProjection.continuous.continuousAt
        (finiteTangentGeneratorOpenPatch_isOpen period hPeriod patch
          |>.mem_nhds hPoint)
    have hWeightSmooth :
        ContMDiffAt coverModelWithCorners.tangent
          (modelWithCornersSelf Real Real) ∞
          (fun current : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) =>
              finiteTangentGeneratorWeight period hPeriod patch current.1)
          vector :=
      ((finiteTangentGeneratorWeight_contMDiff period hPeriod patch).comp
        hProjection).contMDiffAt
    have hEventuallyWeight :
        ∀ᶠ current in 𝓝 vector,
          finiteTangentGeneratorWeight period hPeriod patch current.1 ≠ 0 :=
      hWeightSmooth.continuousAt.eventually_ne hWeight
    apply (localCartanEvaluation_contMDiffAt period hPeriod first potential
      component patch vector hPoint hWeight).congr_of_eventuallyEq
    filter_upwards [hEventuallyPoint, hEventuallyWeight] with
      current hCurrentPoint hCurrentWeight
    exact smoothGaugePotentialCartanFiberCovector_eq_local
      period hPeriod first potential component patch current
      hCurrentPoint hCurrentWeight

/-- The unconditional smooth Maxwell Lie derivative obtained from the
fiberwise Cartan residual. -/
def smoothGaugePotentialCartanAction
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod :=
  smoothGaugePotentialCartanBundle period hPeriod first potential
    (gaugePotentialCartanFiberSmoothness period hPeriod first potential)

@[simp]
theorem smoothGaugePotentialCartanAction_apply
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (second : Ghost period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    (smoothGaugePotentialCartanAction
        period hPeriod first potential).toFun component point (second point) =
      gaugePotentialCartanResidualAt coverModelWithCorners first
        (potential.toFun component) point second := by
  exact smoothGaugePotentialCartanBundle_apply
    period hPeriod first potential
      (gaugePotentialCartanFiberSmoothness period hPeriod first potential)
      component point second

private theorem smoothGaugePotential_eq_of_ghost_eval_eq
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (hEqual : ∀ ghost : Ghost period hPeriod, ∀ component point,
      first.toFun component point (ghost point) =
        second.toFun component point (ghost point)) :
    first = second := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  have hLinear :
      first.toFun component point = second.toFun component point := by
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext_on
      ((finiteSmoothTangentFrame period hPeriod).spansAt point)
    intro vector hVector
    rcases hVector with ⟨index, rfl⟩
    exact hEqual
      (finiteGeneratorCInfinityGhost period hPeriod index) component point
  exact DFunLike.congr_fun hLinear tangent

theorem smoothGaugePotentialCartanAction_add_first
    (first third : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugePotentialCartanAction period hPeriod (first + third) potential =
      smoothGaugePotentialCartanAction period hPeriod first potential +
        smoothGaugePotentialCartanAction period hPeriod third potential := by
  apply smoothGaugePotential_eq_of_ghost_eval_eq period hPeriod
  intro second component point
  change
    (smoothGaugePotentialCartanAction
        period hPeriod (first + third) potential).toFun
          component point (second point) =
      (smoothGaugePotentialCartanAction
          period hPeriod first potential).toFun component point
            (second point) +
        (smoothGaugePotentialCartanAction
          period hPeriod third potential).toFun component point
            (second point)
  rw [smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply]
  exact gaugePotentialCartanResidualAt_add_first coverModelWithCorners
    first third (potential.toFun component) point second
    (first.contMDiff.mdifferentiableAt (by simp))
    (third.contMDiff.mdifferentiableAt (by simp))

theorem smoothGaugePotentialCartanAction_smul_first
    (scalar : Real)
    (first : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugePotentialCartanAction period hPeriod (scalar • first) potential =
      scalar •
        smoothGaugePotentialCartanAction period hPeriod first potential := by
  apply smoothGaugePotential_eq_of_ghost_eval_eq period hPeriod
  intro second component point
  change
    (smoothGaugePotentialCartanAction
        period hPeriod (scalar • first) potential).toFun
          component point (second point) =
      scalar *
        (smoothGaugePotentialCartanAction
          period hPeriod first potential).toFun component point
            (second point)
  rw [smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply]
  exact gaugePotentialCartanResidualAt_smul_first coverModelWithCorners
    scalar first (potential.toFun component) point second
      (first.contMDiff.mdifferentiableAt (by simp))

theorem smoothGaugePotentialCartanAction_add_potential
    (first : Ghost period hPeriod)
    (potential extra : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugePotentialCartanAction period hPeriod first
        (potential + extra) =
      smoothGaugePotentialCartanAction period hPeriod first potential +
        smoothGaugePotentialCartanAction period hPeriod first extra := by
  apply smoothGaugePotential_eq_of_ghost_eval_eq period hPeriod
  intro second component point
  change
    (smoothGaugePotentialCartanAction
        period hPeriod first (potential + extra)).toFun
          component point (second point) =
      (smoothGaugePotentialCartanAction
          period hPeriod first potential).toFun component point
            (second point) +
        (smoothGaugePotentialCartanAction
          period hPeriod first extra).toFun component point
            (second point)
  rw [smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply]
  exact gaugePotentialCartanResidualAt_add_potential coverModelWithCorners
    first (potential.toFun component) (extra.toFun component) point second
    (smoothGaugePotentialEvaluation_mdifferentiableAt
      period hPeriod potential component point second
        (second.contMDiff.mdifferentiableAt (by simp)))
    (smoothGaugePotentialEvaluation_mdifferentiableAt
      period hPeriod extra component point second
        (second.contMDiff.mdifferentiableAt (by simp)))

theorem smoothGaugePotentialCartanAction_smul_potential
    (first : Ghost period hPeriod)
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugePotentialCartanAction period hPeriod first
        (scalar • potential) =
      scalar •
        smoothGaugePotentialCartanAction period hPeriod first potential := by
  apply smoothGaugePotential_eq_of_ghost_eval_eq period hPeriod
  intro second component point
  change
    (smoothGaugePotentialCartanAction
        period hPeriod first (scalar • potential)).toFun
          component point (second point) =
      scalar *
        (smoothGaugePotentialCartanAction
          period hPeriod first potential).toFun component point
            (second point)
  rw [smoothGaugePotentialCartanAction_apply,
    smoothGaugePotentialCartanAction_apply]
  exact gaugePotentialCartanResidualAt_smul_potential coverModelWithCorners
    scalar first (potential.toFun component) point second
    (smoothGaugePotentialEvaluation_mdifferentiableAt
      period hPeriod potential component point second
        (second.contMDiff.mdifferentiableAt (by simp)))

/-- The unconditional Maxwell Cartan operation is bilinear in the smooth
diffeomorphism ghost and the gauge potential. -/
def smoothGaugePotentialCartanActionBilinear :
    Ghost period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
        SmoothAbelianGaugePotential period hPeriod where
  toFun first :=
    { toFun := smoothGaugePotentialCartanAction period hPeriod first
      map_add' :=
        smoothGaugePotentialCartanAction_add_potential period hPeriod first
      map_smul' := fun scalar potential =>
        smoothGaugePotentialCartanAction_smul_potential
          period hPeriod first scalar potential }
  map_add' := fun first third => by
    apply LinearMap.ext
    intro potential
    exact smoothGaugePotentialCartanAction_add_first
      period hPeriod first third potential
  map_smul' := fun scalar first => by
    apply LinearMap.ext
    intro potential
    exact smoothGaugePotentialCartanAction_smul_first
      period hPeriod scalar first potential

end

end P0EFTJanusMappingTorusGaugePotentialCartanGlobalAction4D
end JanusFormal
