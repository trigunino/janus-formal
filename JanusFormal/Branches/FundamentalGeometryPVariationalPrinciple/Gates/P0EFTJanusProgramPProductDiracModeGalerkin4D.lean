import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusInfiniteL2DiracDomain
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Product-Dirac mode Galerkin realization for Program P

This gate works on the established real Hilbert space of square-summable
separated `S² × S¹` Dirac modes.  Projection over the directed set of all
finite mode sets converges strongly without choosing an enumeration.  The
construction is applied simultaneously to nine action blocks; every globally
`C²` full action retains Helmholtz reciprocity at every finite projection, and
both action values and directional Euler forms converge.

The actual squared product-Dirac eigenvalues also define finite quadratic
actions.  They are `C²`, obey Helmholtz, and converge to their spectral series
on the explicit quadratic-form domain.  The mode Hilbert space is an analytic
spectral model; this gate does not claim a Fourier isomorphism with all smooth
global spinor-bundle sections or restore sphere multiplicity labels absent
from `ProductDiracMode`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductDiracModeGalerkin4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusInfiniteL2DiracDomain
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-- Rank-one projection onto one genuine separated Dirac mode. -/
def productModeRankOneProjection (mode : ProductDiracMode) :
    ProductModeHilbert →L[ℝ] ProductModeHilbert :=
  (lp.singleContinuousLinearMap ℝ
    (fun _ : ProductDiracMode => ℝ) 2 mode).comp
      (lp.evalCLM ℝ (fun _ : ProductDiracMode => ℝ) 2 mode)

/-- Projection onto an arbitrary finite set of separated Dirac modes. -/
def productModeFiniteProjection (modes : Finset ProductDiracMode) :
    ProductModeHilbert →L[ℝ] ProductModeHilbert :=
  ∑ mode ∈ modes, productModeRankOneProjection mode

theorem productModeFiniteProjection_apply
    (modes : Finset ProductDiracMode)
    (state : ProductModeHilbert) :
    productModeFiniteProjection modes state =
      ∑ mode ∈ modes, lp.single 2 mode (state mode) := by
  classical
  simp [productModeFiniteProjection, productModeRankOneProjection]
  apply Finset.sum_congr rfl
  intro mode _
  rfl

@[simp]
theorem productModeFiniteProjection_apply_coordinate
    (modes : Finset ProductDiracMode)
    (state : ProductModeHilbert) (coordinate : ProductDiracMode) :
    productModeFiniteProjection modes state coordinate =
      if coordinate ∈ modes then state coordinate else 0 := by
  classical
  rw [productModeFiniteProjection_apply]
  have hEvaluate :
      ((∑ mode ∈ modes,
          lp.single 2 mode (state mode) : ProductModeHilbert) :
        ProductModeHilbert) coordinate =
        ∑ mode ∈ modes,
          (lp.single 2 mode (state mode) :
            ProductModeHilbert) coordinate := by
    change (lp.evalCLM ℝ (fun _ : ProductDiracMode => ℝ) 2 coordinate)
        (∑ mode ∈ modes, lp.single 2 mode (state mode)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro mode _
    rfl
  rw [hEvaluate]
  by_cases hCoordinate : coordinate ∈ modes
  · rw [if_pos hCoordinate, Finset.sum_eq_single coordinate]
    · simp [lp.single_apply]
    · intro other _ hOther
      simp [lp.single_apply, Ne.symm hOther]
    · exact fun hMissing => (hMissing hCoordinate).elim
  · rw [if_neg hCoordinate]
    apply Finset.sum_eq_zero
    intro other hOther
    have hNe : coordinate ≠ other := by
      intro hEqual
      subst other
      exact hCoordinate hOther
    simp [lp.single_apply, hNe]

theorem productModeFiniteProjection_idempotent
    (modes : Finset ProductDiracMode)
    (state : ProductModeHilbert) :
    productModeFiniteProjection modes
        (productModeFiniteProjection modes state) =
      productModeFiniteProjection modes state := by
  ext coordinate
  simp only [productModeFiniteProjection_apply_coordinate]
  split_ifs <;> rfl

/-- The unordered net of all finite-mode projections converges strongly. -/
theorem productModeFiniteProjection_tendsto
    (state : ProductModeHilbert) :
    Tendsto
      (fun modes : Finset ProductDiracMode =>
        productModeFiniteProjection modes state)
      atTop (𝓝 state) := by
  have hProjection :
      (fun modes : Finset ProductDiracMode =>
        productModeFiniteProjection modes state) =
        (fun modes =>
          ∑ mode ∈ modes, lp.single 2 mode (state mode)) := by
    funext modes
    exact productModeFiniteProjection_apply modes state
  rw [hProjection]
  change HasSum
    (fun mode : ProductDiracMode =>
      lp.single 2 mode (state mode)) state
  exact lp.hasSum_single ENNReal.ofNat_ne_top state

/-- Nine copies of the actual separated-mode Hilbert space. -/
abbrev ProgramPProductModeConfiguration :=
  Fin 9 → ProductModeHilbert

/-- Simultaneous finite mode projection in all nine blocks. -/
def configurationProductModeFiniteProjection
    (modes : Finset ProductDiracMode) :
    ProgramPProductModeConfiguration →L[ℝ]
      ProgramPProductModeConfiguration :=
  ContinuousLinearMap.piMap fun _ : Fin 9 =>
    productModeFiniteProjection modes

@[simp]
theorem configurationProductModeFiniteProjection_apply
    (modes : Finset ProductDiracMode)
    (configuration : ProgramPProductModeConfiguration)
    (block : Fin 9) :
    configurationProductModeFiniteProjection modes configuration block =
      productModeFiniteProjection modes (configuration block) :=
  rfl

theorem configurationProductModeFiniteProjection_idempotent
    (modes : Finset ProductDiracMode)
    (configuration : ProgramPProductModeConfiguration) :
    configurationProductModeFiniteProjection modes
        (configurationProductModeFiniteProjection modes configuration) =
      configurationProductModeFiniteProjection modes configuration := by
  funext block
  exact productModeFiniteProjection_idempotent
    modes (configuration block)

/-- The nine-sector finite-mode net converges strongly and simultaneously. -/
theorem configurationProductModeFiniteProjection_tendsto
    (configuration : ProgramPProductModeConfiguration) :
    Tendsto
      (fun modes : Finset ProductDiracMode =>
        configurationProductModeFiniteProjection modes configuration)
      atTop (𝓝 configuration) := by
  rw [tendsto_pi_nhds]
  intro block
  change Tendsto
    (fun modes : Finset ProductDiracMode =>
      productModeFiniteProjection modes (configuration block))
    atTop (𝓝 (configuration block))
  exact productModeFiniteProjection_tendsto (configuration block)

/-- Global `C²` hypothesis on the actual product-mode configuration chart. -/
def ProductModeFullCoupledC2
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration) : Prop :=
  ∀ configuration, FullCoupledC2At blocks configuration

theorem productModeFullCoupledAction_contDiff_two
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks) :
    ContDiff ℝ 2 (fullCoupledAction blocks) := by
  rw [contDiff_iff_contDiffAt]
  intro configuration
  exact fullCoupledAction_contDiffAt blocks configuration
    (hC2 configuration)

/-- Pullback of a full action to one finite separated-mode packet. -/
def productModeGalerkinAction
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (modes : Finset ProductDiracMode)
    (configuration : ProgramPProductModeConfiguration) : ℝ :=
  fullCoupledAction blocks
    (configurationProductModeFiniteProjection modes configuration)

theorem productModeGalerkinAction_contDiff_two
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks)
    (modes : Finset ProductDiracMode) :
    ContDiff ℝ 2 (productModeGalerkinAction blocks modes) := by
  exact (productModeFullCoupledAction_contDiff_two blocks hC2).comp
    (configurationProductModeFiniteProjection modes).contDiff

/-- Every finite separated-mode pullback obeys actual nonlinear Helmholtz
reciprocity. -/
theorem productModeGalerkinAction_helmholtz
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks)
    (modes : Finset ProductDiracMode)
    (configuration : ProgramPProductModeConfiguration) :
    HelmholtzJacobianAt
      (actionGradient (productModeGalerkinAction blocks modes))
      configuration :=
  action_gradient_helmholtz_at
    (productModeGalerkinAction blocks modes) configuration
      (productModeGalerkinAction_contDiff_two
        blocks hC2 modes).contDiffAt

/-- Exact chain-rule Euler form of a separated-mode cutoff action. -/
def productModeGalerkinEulerOneForm
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (modes : Finset ProductDiracMode) :
    EulerOneForm ProgramPProductModeConfiguration :=
  fun configuration =>
    (actionGradient (fullCoupledAction blocks)
      (configurationProductModeFiniteProjection
        modes configuration)).comp
          (configurationProductModeFiniteProjection modes)

theorem productModeGalerkinAction_hasFDerivAt
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks)
    (modes : Finset ProductDiracMode)
    (configuration : ProgramPProductModeConfiguration) :
    HasFDerivAt (productModeGalerkinAction blocks modes)
      (productModeGalerkinEulerOneForm blocks modes configuration)
      configuration := by
  have hAction :
      HasFDerivAt (fullCoupledAction blocks)
        (actionGradient (fullCoupledAction blocks)
          (configurationProductModeFiniteProjection
            modes configuration))
        (configurationProductModeFiniteProjection
          modes configuration) := by
    exact
      ((productModeFullCoupledAction_contDiff_two
        blocks hC2).differentiable
          (by norm_num)
          (configurationProductModeFiniteProjection
            modes configuration)).hasFDerivAt
  exact hAction.comp configuration
    (configurationProductModeFiniteProjection modes).hasFDerivAt

/-- Full action values are recovered as the unordered finite-mode net. -/
theorem productModeGalerkinAction_tendsto
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks)
    (configuration : ProgramPProductModeConfiguration) :
    Tendsto
      (fun modes : Finset ProductDiracMode =>
        productModeGalerkinAction blocks modes configuration)
      atTop (𝓝 (fullCoupledAction blocks configuration)) := by
  exact Filter.Tendsto.comp
    (productModeFullCoupledAction_contDiff_two
      blocks hC2).continuous.continuousAt
    (configurationProductModeFiniteProjection_tendsto configuration)

/-- Every directional Euler value is recovered by the finite-mode net. -/
theorem productModeGalerkinEuler_apply_tendsto
    (blocks :
      FullCoupledActionBlocks ProgramPProductModeConfiguration)
    (hC2 : ProductModeFullCoupledC2 blocks)
    (configuration variation : ProgramPProductModeConfiguration) :
    Tendsto
      (fun modes : Finset ProductDiracMode =>
        productModeGalerkinEulerOneForm
          blocks modes configuration variation)
      atTop
      (𝓝 (actionGradient
        (fullCoupledAction blocks) configuration variation)) := by
  have hAction :=
    productModeFullCoupledAction_contDiff_two blocks hC2
  have hGradient :
      ContDiff ℝ 1 (actionGradient (fullCoupledAction blocks)) := by
    change ContDiff ℝ 1 (fderiv ℝ (fullCoupledAction blocks))
    exact hAction.fderiv_right (by norm_num)
  have hEvaluation : Continuous
      (fun pair :
          ProgramPProductModeConfiguration ×
            ProgramPProductModeConfiguration =>
        actionGradient (fullCoupledAction blocks) pair.1 pair.2) :=
    ((hGradient.comp contDiff_fst).clm_apply contDiff_snd).continuous
  exact Filter.Tendsto.comp hEvaluation.continuousAt
    ((configurationProductModeFiniteProjection_tendsto
      configuration).prodMk_nhds
        (configurationProductModeFiniteProjection_tendsto variation))

/-- Finite quadratic action of the actual squared product-Dirac spectrum in
one selected block. -/
def finiteProductDiracQuadraticAction
    (data : ProductThroatSpectralData)
    (modes : Finset ProductDiracMode)
    (block : Fin 9)
    (configuration : ProgramPProductModeConfiguration) : ℝ :=
  (1 / 2 : ℝ) * ∑ mode ∈ modes,
    productDiracEigenvalueSquared data mode *
      (configuration block mode) ^ 2

theorem finiteProductDiracQuadraticAction_contDiff_two
    (data : ProductThroatSpectralData)
    (modes : Finset ProductDiracMode)
    (block : Fin 9) :
    ContDiff ℝ 2
      (finiteProductDiracQuadraticAction data modes block) := by
  unfold finiteProductDiracQuadraticAction
  have hSum : ContDiff ℝ 2
      (fun configuration : ProgramPProductModeConfiguration =>
        ∑ mode ∈ modes,
          productDiracEigenvalueSquared data mode *
            (configuration block mode) ^ 2) := by
    apply ContDiff.sum
    intro mode _
    have hBlock : ContDiff ℝ 2
        (fun configuration : ProgramPProductModeConfiguration =>
          configuration block) :=
      (ContinuousLinearMap.proj block :
        ProgramPProductModeConfiguration →L[ℝ]
          ProductModeHilbert).contDiff
    have hMode : ContDiff ℝ 2
        (fun configuration : ProgramPProductModeConfiguration =>
          configuration block mode) :=
      (lp.evalCLM ℝ
        (fun _ : ProductDiracMode => ℝ) 2 mode).contDiff.comp
          hBlock
    simpa [smul_eq_mul] using
      ContDiff.const_smul
        (productDiracEigenvalueSquared data mode) (hMode.pow 2)
  simpa [smul_eq_mul] using
    ContDiff.const_smul (1 / 2 : ℝ) hSum

/-- Concrete Helmholtz reciprocity for every finite product-Dirac quadratic
action. -/
theorem finiteProductDiracQuadraticAction_helmholtz
    (data : ProductThroatSpectralData)
    (modes : Finset ProductDiracMode)
    (block : Fin 9)
    (configuration : ProgramPProductModeConfiguration) :
    HelmholtzJacobianAt
      (actionGradient
        (finiteProductDiracQuadraticAction data modes block))
      configuration :=
  action_gradient_helmholtz_at
    (finiteProductDiracQuadraticAction data modes block)
    configuration
    (finiteProductDiracQuadraticAction_contDiff_two
      data modes block).contDiffAt

/-- Explicit quadratic-form domain of the unbounded squared Dirac action. -/
def ProductDiracQuadraticFormDomain
    (data : ProductThroatSpectralData)
    (block : Fin 9) :
    Set ProgramPProductModeConfiguration :=
  { configuration |
    Summable (fun mode : ProductDiracMode =>
      productDiracEigenvalueSquared data mode *
        (configuration block mode) ^ 2) }

/-- Every finite projection belongs to the unbounded quadratic-form domain. -/
theorem configurationProductModeFiniteProjection_mem_formDomain
    (data : ProductThroatSpectralData)
    (modes : Finset ProductDiracMode)
    (block : Fin 9)
    (configuration : ProgramPProductModeConfiguration) :
    configurationProductModeFiniteProjection modes configuration ∈
      ProductDiracQuadraticFormDomain data block := by
  change Summable
    (fun mode : ProductDiracMode =>
      productDiracEigenvalueSquared data mode *
        (configurationProductModeFiniteProjection
          modes configuration block mode) ^ 2)
  apply summable_of_ne_finset_zero (s := modes)
  intro mode hMode
  change productDiracEigenvalueSquared data mode *
      (productModeFiniteProjection
        modes (configuration block) mode) ^ 2 = 0
  rw [productModeFiniteProjection_apply_coordinate, if_neg hMode]
  simp

/-- Spectral quadratic action.  Its analytic assertions below are restricted
to `ProductDiracQuadraticFormDomain`. -/
def productDiracQuadraticAction
    (data : ProductThroatSpectralData)
    (block : Fin 9)
    (configuration : ProgramPProductModeConfiguration) : ℝ :=
  (1 / 2 : ℝ) * ∑' mode : ProductDiracMode,
    productDiracEigenvalueSquared data mode *
      (configuration block mode) ^ 2

/-- On the genuine form domain, arbitrary finite spectral packets converge
to the full product-Dirac quadratic action. -/
theorem finiteProductDiracQuadraticAction_tendsto
    (data : ProductThroatSpectralData)
    (block : Fin 9)
    (configuration : ProgramPProductModeConfiguration)
    (hDomain : configuration ∈
      ProductDiracQuadraticFormDomain data block) :
    Tendsto
      (fun modes : Finset ProductDiracMode =>
        finiteProductDiracQuadraticAction
          data modes block configuration)
      atTop
      (𝓝 (productDiracQuadraticAction
        data block configuration)) := by
  change Tendsto
    (fun modes : Finset ProductDiracMode =>
      (1 / 2 : ℝ) * ∑ mode ∈ modes,
        productDiracEigenvalueSquared data mode *
          (configuration block mode) ^ 2)
    atTop
    (𝓝 ((1 / 2 : ℝ) * ∑' mode : ProductDiracMode,
      productDiracEigenvalueSquared data mode *
        (configuration block mode) ^ 2))
  exact tendsto_const_nhds.mul hDomain.hasSum

end

end P0EFTJanusProgramPProductDiracModeGalerkin4D
end JanusFormal
