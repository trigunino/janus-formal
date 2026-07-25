import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.lpSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Sobolev--Galerkin realization of the full Program-P Helmholtz bridge

The common completed coefficient chart is nine copies of real `ℓ²(ℕ)`, one
for each coupled action block.  Canonical finite-mode projections converge
strongly to the identity.  Therefore every globally `C²` nine-block action
has convergent Galerkin action values and directional Euler forms, while every
cutoff action retains the genuine nonlinear Helmholtz symmetry.

This is an infinite-dimensional coefficient/Sobolev model.  Identifying its
nine coordinates with the actual global Janus bundles is a separate geometric
Fourier--Sobolev transform.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSobolevGalerkinHelmholtz4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-- One completed real mode space.  As in the existing graph-Sobolev gates,
the chosen Sobolev weights are absorbed into the encoded coefficients. -/
abbrev ProgramPModeHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Nine completed mode sectors on one common normed chart. -/
abbrev ProgramPSobolevConfiguration := Fin 9 → ProgramPModeHilbert

/-- Rank-one projection onto one mode. -/
def modeRankOneProjection (mode : ℕ) :
    ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert :=
  (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 mode).comp
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 mode)

@[simp]
theorem modeRankOneProjection_apply
    (mode : ℕ) (state : ProgramPModeHilbert) :
    modeRankOneProjection mode state =
      lp.single 2 mode (state mode) := by
  rfl

/-- Projection onto the first `cutoff` modes. -/
def finiteModeProjection (cutoff : ℕ) :
    ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert :=
  ∑ mode ∈ Finset.range cutoff, modeRankOneProjection mode

theorem finiteModeProjection_apply
    (cutoff : ℕ) (state : ProgramPModeHilbert) :
    finiteModeProjection cutoff state =
      ∑ mode ∈ Finset.range cutoff, lp.single 2 mode (state mode) := by
  classical
  simp [finiteModeProjection]

@[simp]
theorem finiteModeProjection_apply_coordinate
    (cutoff : ℕ) (state : ProgramPModeHilbert) (coordinate : ℕ) :
    finiteModeProjection cutoff state coordinate =
      if coordinate < cutoff then state coordinate else 0 := by
  classical
  rw [finiteModeProjection_apply]
  have hEvaluate :
      ((∑ mode ∈ Finset.range cutoff,
          lp.single 2 mode (state mode) : ProgramPModeHilbert) :
        ProgramPModeHilbert) coordinate =
        ∑ mode ∈ Finset.range cutoff,
          (lp.single 2 mode (state mode) : ProgramPModeHilbert) coordinate := by
    change (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 coordinate)
        (∑ mode ∈ Finset.range cutoff,
          lp.single 2 mode (state mode)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro mode _
    rfl
  rw [hEvaluate]
  by_cases hCoordinate : coordinate ∈ Finset.range cutoff
  · rw [if_pos (Finset.mem_range.mp hCoordinate),
      Finset.sum_eq_single coordinate]
    · simp [lp.single_apply]
    · intro other _ hOther
      simp [lp.single_apply, Ne.symm hOther]
    · exact fun hMissing => (hMissing hCoordinate).elim
  · rw [if_neg (not_lt.mpr (Nat.le_of_not_gt
        (fun h => hCoordinate (Finset.mem_range.mpr h))))]
    apply Finset.sum_eq_zero
    intro other hOther
    have hNe : coordinate ≠ other := by
      intro hEqual
      subst other
      exact hCoordinate hOther
    simp [lp.single_apply, hNe]

/-- A cutoff is an actual projection. -/
theorem finiteModeProjection_idempotent
    (cutoff : ℕ) (state : ProgramPModeHilbert) :
    finiteModeProjection cutoff (finiteModeProjection cutoff state) =
      finiteModeProjection cutoff state := by
  ext coordinate
  simp only [finiteModeProjection_apply_coordinate]
  split_ifs <;> rfl

/-- Finite mode projections converge strongly to the identity on `ℓ²`. -/
theorem finiteModeProjection_tendsto
    (state : ProgramPModeHilbert) :
    Tendsto (fun cutoff => finiteModeProjection cutoff state)
      atTop (𝓝 state) := by
  simpa only [finiteModeProjection_apply] using
    (lp.hasSum_single ENNReal.ofNat_ne_top state).tendsto_sum_nat

/-- Simultaneous cutoff in all nine sectors. -/
def configurationFiniteModeProjection (cutoff : ℕ) :
    ProgramPSobolevConfiguration →L[ℝ] ProgramPSobolevConfiguration :=
  ContinuousLinearMap.piMap fun _ : Fin 9 => finiteModeProjection cutoff

@[simp]
theorem configurationFiniteModeProjection_apply
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration)
    (block : Fin 9) :
    configurationFiniteModeProjection cutoff configuration block =
      finiteModeProjection cutoff (configuration block) :=
  rfl

/-- The simultaneous nine-sector cutoffs converge strongly. -/
theorem configurationFiniteModeProjection_tendsto
    (configuration : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff => configurationFiniteModeProjection cutoff configuration)
      atTop (𝓝 configuration) := by
  rw [tendsto_pi_nhds]
  intro block
  simpa using finiteModeProjection_tendsto (configuration block)

/-- The simultaneous cutoff is idempotent. -/
theorem configurationFiniteModeProjection_idempotent
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) :
    configurationFiniteModeProjection cutoff
        (configurationFiniteModeProjection cutoff configuration) =
      configurationFiniteModeProjection cutoff configuration := by
  funext block
  exact finiteModeProjection_idempotent cutoff (configuration block)

/-- Literal finite coordinate space for all nine sectors at one cutoff. -/
abbrev ProgramPFiniteSobolevConfiguration (cutoff : ℕ) :=
  Fin 9 → Fin cutoff → ℝ

/-- Embed a finite coordinate vector as a finitely supported `ℓ²` state. -/
def finiteModeEmbedding (cutoff : ℕ) :
    (Fin cutoff → ℝ) →L[ℝ] ProgramPModeHilbert :=
  ∑ index : Fin cutoff,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 index.1).comp
      (ContinuousLinearMap.proj index)

/-- Restrict an `ℓ²` state to its first finite coordinates. -/
def finiteModeRestriction (cutoff : ℕ) :
    ProgramPModeHilbert →L[ℝ] (Fin cutoff → ℝ) :=
  ContinuousLinearMap.pi fun index : Fin cutoff =>
    lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 index.1

@[simp]
theorem finiteModeRestriction_apply
    (cutoff : ℕ) (state : ProgramPModeHilbert) (index : Fin cutoff) :
    finiteModeRestriction cutoff state index = state index.1 :=
  rfl

/-- Restriction after finite embedding is exactly the identity. -/
theorem finiteModeRestriction_embedding
    (cutoff : ℕ) (state : Fin cutoff → ℝ) :
    finiteModeRestriction cutoff (finiteModeEmbedding cutoff state) =
      state := by
  ext index
  classical
  simp only [finiteModeRestriction, finiteModeEmbedding,
    ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rw [map_sum]
  simp only [ContinuousLinearMap.proj_apply]
  change (∑ coordinate : Fin cutoff,
      (lp.single 2 coordinate.1 (state coordinate) :
        ProgramPModeHilbert) index.1) =
    state index
  rw [Finset.sum_eq_single index]
  · simp [lp.single_apply]
  · intro other _ hOther
    have hValue : other.1 ≠ index.1 := by
      intro hEqual
      exact hOther (Fin.ext hEqual)
    simp [lp.single_apply, hValue]
  · simp

/-- Embedding after restriction is exactly the canonical cutoff projection. -/
theorem finiteModeEmbedding_restriction
    (cutoff : ℕ) (state : ProgramPModeHilbert) :
    finiteModeEmbedding cutoff (finiteModeRestriction cutoff state) =
      finiteModeProjection cutoff state := by
  ext coordinate
  classical
  rw [finiteModeProjection_apply_coordinate]
  simp only [finiteModeEmbedding, finiteModeRestriction,
    sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  change (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 coordinate)
      (∑ index : Fin cutoff,
        lp.single 2 index.1
          ((ContinuousLinearMap.proj index)
            ((ContinuousLinearMap.pi fun index : Fin cutoff =>
              lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 index.1) state))) =
    _
  rw [map_sum]
  simp only [ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply]
  change (∑ index : Fin cutoff,
      (lp.single 2 index.1 (state index.1) :
        ProgramPModeHilbert) coordinate) =
    if coordinate < cutoff then state coordinate else 0
  by_cases hCoordinate : coordinate < cutoff
  · rw [if_pos hCoordinate]
    let index : Fin cutoff := ⟨coordinate, hCoordinate⟩
    rw [Finset.sum_eq_single index]
    · simp [index, lp.single_apply]
    · intro other _ hOther
      have hValue : other.1 ≠ coordinate := by
        intro hEqual
        apply hOther
        exact Fin.ext hEqual
      simp [lp.single_apply, hValue]
    · simp
  · rw [if_neg hCoordinate]
    apply Finset.sum_eq_zero
    intro index _
    have hValue : index.1 ≠ coordinate := by
      intro hEqual
      exact hCoordinate (hEqual ▸ index.2)
    simp [lp.single_apply, hValue]

/-- Simultaneous embedding of all nine finite sectors. -/
def finiteConfigurationEmbedding (cutoff : ℕ) :
    ProgramPFiniteSobolevConfiguration cutoff →L[ℝ]
      ProgramPSobolevConfiguration :=
  ContinuousLinearMap.piMap fun _ : Fin 9 => finiteModeEmbedding cutoff

/-- Simultaneous restriction of the completed configuration. -/
def finiteConfigurationRestriction (cutoff : ℕ) :
    ProgramPSobolevConfiguration →L[ℝ]
      ProgramPFiniteSobolevConfiguration cutoff :=
  ContinuousLinearMap.piMap fun _ : Fin 9 => finiteModeRestriction cutoff

/-- Finite restriction is a left inverse of the simultaneous embedding. -/
theorem finiteConfigurationRestriction_embedding
    (cutoff : ℕ) (configuration : ProgramPFiniteSobolevConfiguration cutoff) :
    finiteConfigurationRestriction cutoff
        (finiteConfigurationEmbedding cutoff configuration) =
      configuration := by
  funext block
  exact finiteModeRestriction_embedding cutoff (configuration block)

/-- The finite embedding/restriction composite is the simultaneous Galerkin
projection. -/
theorem finiteConfigurationEmbedding_restriction
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) :
    finiteConfigurationEmbedding cutoff
        (finiteConfigurationRestriction cutoff configuration) =
      configurationFiniteModeProjection cutoff configuration := by
  funext block
  exact finiteModeEmbedding_restriction cutoff (configuration block)

/-- Global `C²` certificate for the nine blocks. -/
def FullCoupledC2
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration) : Prop :=
  ∀ configuration, FullCoupledC2At blocks configuration

/-- The assembled action is globally `C²`. -/
theorem fullCoupledAction_contDiff_two
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks) :
    ContDiff ℝ 2 (fullCoupledAction blocks) := by
  rw [contDiff_iff_contDiffAt]
  intro configuration
  exact fullCoupledAction_contDiffAt blocks configuration
    (hC2 configuration)

/-- Galerkin pullback of the complete action. -/
def sobolevGalerkinAction
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) : ℝ :=
  fullCoupledAction blocks
    (configurationFiniteModeProjection cutoff configuration)

/-- The same cutoff action written on its literal finite coordinate space. -/
def literalFiniteGalerkinAction
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (cutoff : ℕ)
    (configuration : ProgramPFiniteSobolevConfiguration cutoff) : ℝ :=
  fullCoupledAction blocks
    (finiteConfigurationEmbedding cutoff configuration)

/-- The completed-space cutoff factors exactly through finite restriction. -/
theorem sobolevGalerkinAction_eq_literalFinite
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) :
    sobolevGalerkinAction blocks cutoff configuration =
      literalFiniteGalerkinAction blocks cutoff
        (finiteConfigurationRestriction cutoff configuration) := by
  rw [sobolevGalerkinAction, literalFiniteGalerkinAction,
    finiteConfigurationEmbedding_restriction]

/-- Every cutoff action remains genuinely `C²`. -/
theorem sobolevGalerkinAction_contDiff_two
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (cutoff : ℕ) :
    ContDiff ℝ 2 (sobolevGalerkinAction blocks cutoff) := by
  exact (fullCoupledAction_contDiff_two blocks hC2).comp
    (configurationFiniteModeProjection cutoff).contDiff

/-- The literal finite-coordinate action is genuinely `C²`. -/
theorem literalFiniteGalerkinAction_contDiff_two
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (cutoff : ℕ) :
    ContDiff ℝ 2 (literalFiniteGalerkinAction blocks cutoff) := by
  exact (fullCoupledAction_contDiff_two blocks hC2).comp
    (finiteConfigurationEmbedding cutoff).contDiff

/-- The literal finite-coordinate realization also obeys actual Helmholtz
reciprocity. -/
theorem literalFiniteGalerkinAction_helmholtz
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (cutoff : ℕ)
    (configuration : ProgramPFiniteSobolevConfiguration cutoff) :
    HelmholtzJacobianAt
      (actionGradient (literalFiniteGalerkinAction blocks cutoff))
      configuration :=
  action_gradient_helmholtz_at
    (literalFiniteGalerkinAction blocks cutoff) configuration
      (literalFiniteGalerkinAction_contDiff_two
        blocks hC2 cutoff).contDiffAt

/-- Every cutoff action obeys the actual nonlinear Helmholtz condition. -/
theorem sobolevGalerkinAction_helmholtz
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) :
    HelmholtzJacobianAt
      (actionGradient (sobolevGalerkinAction blocks cutoff))
      configuration :=
  action_gradient_helmholtz_at
    (sobolevGalerkinAction blocks cutoff) configuration
      (sobolevGalerkinAction_contDiff_two blocks hC2 cutoff).contDiffAt

/-- Galerkin Euler one-form, including the projection of variations required
by the chain rule. -/
def sobolevGalerkinEulerOneForm
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (cutoff : ℕ) :
    EulerOneForm ProgramPSobolevConfiguration :=
  fun configuration =>
    (actionGradient (fullCoupledAction blocks)
      (configurationFiniteModeProjection cutoff configuration)).comp
        (configurationFiniteModeProjection cutoff)

/-- The displayed Galerkin Euler form is the actual Fréchet derivative of the
cutoff action. -/
theorem sobolevGalerkinAction_hasFDerivAt
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (cutoff : ℕ) (configuration : ProgramPSobolevConfiguration) :
    HasFDerivAt (sobolevGalerkinAction blocks cutoff)
      (sobolevGalerkinEulerOneForm blocks cutoff configuration)
      configuration := by
  have hAction :
      HasFDerivAt (fullCoupledAction blocks)
        (actionGradient (fullCoupledAction blocks)
          (configurationFiniteModeProjection cutoff configuration))
        (configurationFiniteModeProjection cutoff configuration) := by
    exact
      ((fullCoupledAction_contDiff_two blocks hC2).differentiable
        (by norm_num)
        (configurationFiniteModeProjection cutoff configuration)).hasFDerivAt
  exact hAction.comp configuration
    (configurationFiniteModeProjection cutoff).hasFDerivAt

/-- Galerkin action values converge to the complete Sobolev action. -/
theorem sobolevGalerkinAction_tendsto
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (configuration : ProgramPSobolevConfiguration) :
    Tendsto (fun cutoff => sobolevGalerkinAction blocks cutoff configuration)
      atTop (𝓝 (fullCoupledAction blocks configuration)) := by
  exact Filter.Tendsto.comp
    (fullCoupledAction_contDiff_two blocks hC2).continuous.continuousAt
      (configurationFiniteModeProjection_tendsto configuration)

/-- Directional Galerkin Euler values converge to the complete Euler form. -/
theorem sobolevGalerkinEulerOneForm_apply_tendsto
    (blocks : FullCoupledActionBlocks ProgramPSobolevConfiguration)
    (hC2 : FullCoupledC2 blocks)
    (configuration variation : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff =>
        sobolevGalerkinEulerOneForm blocks cutoff configuration variation)
      atTop
      (𝓝 (actionGradient (fullCoupledAction blocks) configuration variation)) := by
  have hAction := fullCoupledAction_contDiff_two blocks hC2
  have hGradient :
      ContDiff ℝ 1 (actionGradient (fullCoupledAction blocks)) := by
    change ContDiff ℝ 1 (fderiv ℝ (fullCoupledAction blocks))
    exact hAction.fderiv_right (by norm_num)
  have hEvaluation : Continuous
      (fun pair : ProgramPSobolevConfiguration ×
          ProgramPSobolevConfiguration =>
        actionGradient (fullCoupledAction blocks) pair.1 pair.2) :=
    ((hGradient.comp contDiff_fst).clm_apply contDiff_snd).continuous
  exact Filter.Tendsto.comp hEvaluation.continuousAt
    ((configurationFiniteModeProjection_tendsto configuration).prodMk_nhds
      (configurationFiniteModeProjection_tendsto variation))

/-- Symmetry of one bounded Euler operator with respect to the real Hilbert
pairing. -/
def IsSymmetricSobolevOperator
    (operator : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert) : Prop :=
  ∀ first second,
    inner ℝ (operator first) second =
      inner ℝ (operator second) first

/-- One bounded quadratic operator for every Program-P action block. -/
structure FullCoupledSobolevQuadraticData where
  candidateA : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  matter : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  robin : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  ll : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  einsteinHilbertPlus : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  einsteinHilbertMinus : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  maxwellPlus : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  maxwellMinus : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert
  finiteBV : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert

/-- Self-adjointness data for all nine bounded Euler operators. -/
structure FullCoupledSobolevSymmetric
    (data : FullCoupledSobolevQuadraticData) : Prop where
  candidateA : IsSymmetricSobolevOperator data.candidateA
  matter : IsSymmetricSobolevOperator data.matter
  robin : IsSymmetricSobolevOperator data.robin
  ll : IsSymmetricSobolevOperator data.ll
  einsteinHilbertPlus :
    IsSymmetricSobolevOperator data.einsteinHilbertPlus
  einsteinHilbertMinus :
    IsSymmetricSobolevOperator data.einsteinHilbertMinus
  maxwellPlus : IsSymmetricSobolevOperator data.maxwellPlus
  maxwellMinus : IsSymmetricSobolevOperator data.maxwellMinus
  finiteBV : IsSymmetricSobolevOperator data.finiteBV

/-- Quadratic action carried by one of the nine completed sectors. -/
def sobolevQuadraticBlockAction
    (block : Fin 9)
    (operator : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert)
    (configuration : ProgramPSobolevConfiguration) : ℝ :=
  (1 / 2 : ℝ) *
    inner ℝ (operator (configuration block)) (configuration block)

/-- Bounded quadratic blocks are genuinely smooth on the infinite Hilbert
chart. -/
theorem sobolevQuadraticBlockAction_contDiff_two
    (block : Fin 9)
    (operator : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert) :
    ContDiff ℝ 2 (sobolevQuadraticBlockAction block operator) := by
  unfold sobolevQuadraticBlockAction
  have hCoordinate :
      ContDiff ℝ 2
        (fun configuration : ProgramPSobolevConfiguration =>
          configuration block) :=
    (ContinuousLinearMap.proj block :
      ProgramPSobolevConfiguration →L[ℝ] ProgramPModeHilbert).contDiff
  have hOperator :
      ContDiff ℝ 2
        (fun configuration : ProgramPSobolevConfiguration =>
          operator (configuration block)) :=
    operator.contDiff.comp hCoordinate
  simpa [smul_eq_mul] using
    (ContDiff.const_smul (1 / 2 : ℝ) (hOperator.inner ℝ hCoordinate))

/-- Coordinate projection onto one of the nine completed sectors. -/
def sobolevBlockProjection (block : Fin 9) :
    ProgramPSobolevConfiguration →L[ℝ] ProgramPModeHilbert :=
  ContinuousLinearMap.proj block

/-- Euler functional represented by one symmetric bounded operator. -/
def sobolevQuadraticBlockEuler
    (block : Fin 9)
    (operator : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert)
    (configuration : ProgramPSobolevConfiguration) :
    ProgramPSobolevConfiguration →L[ℝ] ℝ :=
  (innerSL ℝ (operator (configuration block))).comp
    (sobolevBlockProjection block)

/-- A symmetric bounded operator is exactly the actual derivative of its
quadratic block action. -/
theorem sobolevQuadraticBlockAction_hasFDerivAt
    (block : Fin 9)
    (operator : ProgramPModeHilbert →L[ℝ] ProgramPModeHilbert)
    (hSymmetric : IsSymmetricSobolevOperator operator)
    (configuration : ProgramPSobolevConfiguration) :
    HasFDerivAt (sobolevQuadraticBlockAction block operator)
      (sobolevQuadraticBlockEuler block operator configuration)
      configuration := by
  let projection := sobolevBlockProjection block
  have hProjection : HasFDerivAt projection projection configuration :=
    projection.hasFDerivAt
  have hOperator :
      HasFDerivAt (fun point => operator (projection point))
        (operator.comp projection) configuration :=
    operator.hasFDerivAt.comp configuration hProjection
  have hInner :=
    (hOperator.inner ℝ hProjection).const_mul (1 / 2 : ℝ)
  apply hInner.congr_fderiv
  ext variation
  change
    (1 / 2 : ℝ) *
        (inner ℝ (operator (configuration block)) (variation block) +
          inner ℝ (operator (variation block)) (configuration block)) =
      inner ℝ (operator (configuration block)) (variation block)
  rw [hSymmetric (variation block) (configuration block)]
  ring

/-- The nine bounded quadratic functionals on the common chart. -/
def sobolevQuadraticActionBlocks
    (data : FullCoupledSobolevQuadraticData) :
    FullCoupledActionBlocks ProgramPSobolevConfiguration where
  candidateA := sobolevQuadraticBlockAction 0 data.candidateA
  matter := sobolevQuadraticBlockAction 1 data.matter
  robin := sobolevQuadraticBlockAction 2 data.robin
  ll := sobolevQuadraticBlockAction 3 data.ll
  einsteinHilbertPlus :=
    sobolevQuadraticBlockAction 4 data.einsteinHilbertPlus
  einsteinHilbertMinus :=
    sobolevQuadraticBlockAction 5 data.einsteinHilbertMinus
  maxwellPlus := sobolevQuadraticBlockAction 6 data.maxwellPlus
  maxwellMinus := sobolevQuadraticBlockAction 7 data.maxwellMinus
  finiteBV := sobolevQuadraticBlockAction 8 data.finiteBV

/-- The infinite-dimensional nine-block quadratic model inhabits the global
`C²` interface without assumptions. -/
def sobolevQuadraticActionBlocks_c2
    (data : FullCoupledSobolevQuadraticData) :
    FullCoupledC2 (sobolevQuadraticActionBlocks data) := by
  intro configuration
  exact
    { candidateA :=
        (sobolevQuadraticBlockAction_contDiff_two 0 data.candidateA).contDiffAt
      matter :=
        (sobolevQuadraticBlockAction_contDiff_two 1 data.matter).contDiffAt
      robin :=
        (sobolevQuadraticBlockAction_contDiff_two 2 data.robin).contDiffAt
      ll :=
        (sobolevQuadraticBlockAction_contDiff_two 3 data.ll).contDiffAt
      einsteinHilbertPlus :=
        (sobolevQuadraticBlockAction_contDiff_two
          4 data.einsteinHilbertPlus).contDiffAt
      einsteinHilbertMinus :=
        (sobolevQuadraticBlockAction_contDiff_two
          5 data.einsteinHilbertMinus).contDiffAt
      maxwellPlus :=
        (sobolevQuadraticBlockAction_contDiff_two
          6 data.maxwellPlus).contDiffAt
      maxwellMinus :=
        (sobolevQuadraticBlockAction_contDiff_two
          7 data.maxwellMinus).contDiffAt
      finiteBV :=
        (sobolevQuadraticBlockAction_contDiff_two
          8 data.finiteBV).contDiffAt }

/-- Concrete infinite-dimensional Helmholtz theorem for the nine bounded
quadratic blocks. -/
theorem sobolevQuadraticFullAction_helmholtz
    (data : FullCoupledSobolevQuadraticData)
    (configuration : ProgramPSobolevConfiguration) :
    HelmholtzJacobianAt
      (actionGradient
        (fullCoupledAction (sobolevQuadraticActionBlocks data)))
      configuration :=
  fullCoupledAction_helmholtz
    (sobolevQuadraticActionBlocks data) configuration
      (sobolevQuadraticActionBlocks_c2 data configuration)

/-- Actual infinite-dimensional summed action. -/
def sobolevQuadraticFullAction
    (data : FullCoupledSobolevQuadraticData) :
    ProgramPSobolevConfiguration → ℝ :=
  fullCoupledAction (sobolevQuadraticActionBlocks data)

/-- Exact blockwise realization of the nine operator-represented Euler
forms. -/
structure FullCoupledSobolevEulerRealizationAt
    (data : FullCoupledSobolevQuadraticData)
    (configuration : ProgramPSobolevConfiguration) : Prop where
  candidateA :
    HasFDerivAt (sobolevQuadraticBlockAction 0 data.candidateA)
      (sobolevQuadraticBlockEuler 0 data.candidateA configuration)
      configuration
  matter :
    HasFDerivAt (sobolevQuadraticBlockAction 1 data.matter)
      (sobolevQuadraticBlockEuler 1 data.matter configuration)
      configuration
  robin :
    HasFDerivAt (sobolevQuadraticBlockAction 2 data.robin)
      (sobolevQuadraticBlockEuler 2 data.robin configuration)
      configuration
  ll :
    HasFDerivAt (sobolevQuadraticBlockAction 3 data.ll)
      (sobolevQuadraticBlockEuler 3 data.ll configuration)
      configuration
  einsteinHilbertPlus :
    HasFDerivAt
      (sobolevQuadraticBlockAction 4 data.einsteinHilbertPlus)
      (sobolevQuadraticBlockEuler
        4 data.einsteinHilbertPlus configuration)
      configuration
  einsteinHilbertMinus :
    HasFDerivAt
      (sobolevQuadraticBlockAction 5 data.einsteinHilbertMinus)
      (sobolevQuadraticBlockEuler
        5 data.einsteinHilbertMinus configuration)
      configuration
  maxwellPlus :
    HasFDerivAt (sobolevQuadraticBlockAction 6 data.maxwellPlus)
      (sobolevQuadraticBlockEuler 6 data.maxwellPlus configuration)
      configuration
  maxwellMinus :
    HasFDerivAt (sobolevQuadraticBlockAction 7 data.maxwellMinus)
      (sobolevQuadraticBlockEuler 7 data.maxwellMinus configuration)
      configuration
  finiteBV :
    HasFDerivAt (sobolevQuadraticBlockAction 8 data.finiteBV)
      (sobolevQuadraticBlockEuler 8 data.finiteBV configuration)
      configuration

/-- All nine symmetric bounded operators realize their prescribed Euler
forms on the completed chart. -/
def sobolevQuadraticEulerRealizationAt
    (data : FullCoupledSobolevQuadraticData)
    (hSymmetric : FullCoupledSobolevSymmetric data)
    (configuration : ProgramPSobolevConfiguration) :
    FullCoupledSobolevEulerRealizationAt data configuration where
  candidateA := sobolevQuadraticBlockAction_hasFDerivAt
    0 data.candidateA hSymmetric.candidateA configuration
  matter := sobolevQuadraticBlockAction_hasFDerivAt
    1 data.matter hSymmetric.matter configuration
  robin := sobolevQuadraticBlockAction_hasFDerivAt
    2 data.robin hSymmetric.robin configuration
  ll := sobolevQuadraticBlockAction_hasFDerivAt
    3 data.ll hSymmetric.ll configuration
  einsteinHilbertPlus := sobolevQuadraticBlockAction_hasFDerivAt
    4 data.einsteinHilbertPlus hSymmetric.einsteinHilbertPlus configuration
  einsteinHilbertMinus := sobolevQuadraticBlockAction_hasFDerivAt
    5 data.einsteinHilbertMinus hSymmetric.einsteinHilbertMinus configuration
  maxwellPlus := sobolevQuadraticBlockAction_hasFDerivAt
    6 data.maxwellPlus hSymmetric.maxwellPlus configuration
  maxwellMinus := sobolevQuadraticBlockAction_hasFDerivAt
    7 data.maxwellMinus hSymmetric.maxwellMinus configuration
  finiteBV := sobolevQuadraticBlockAction_hasFDerivAt
    8 data.finiteBV hSymmetric.finiteBV configuration

/-- Affine action curve on the completed common chart. -/
def sobolevQuadraticFullActionCurve
    (data : FullCoupledSobolevQuadraticData)
    (configuration variation : ProgramPSobolevConfiguration)
    (parameter : ℝ) : ℝ :=
  sobolevQuadraticFullAction data
    (configuration + parameter • variation)

/-- The abstract full-action Fréchet bridge is inhabited on the completed
nine-sector Sobolev coefficient chart. -/
def sobolevQuadraticConcreteFrechetBridge
    (data : FullCoupledSobolevQuadraticData) :
    ConcreteFullActionFrechetBridge
      ProgramPSobolevConfiguration ProgramPSobolevConfiguration
      (sobolevQuadraticFullActionCurve data) where
  Configuration := ProgramPSobolevConfiguration
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  encodeConfiguration := id
  encodeVariation := id
  blocks := sobolevQuadraticActionBlocks data
  affineCurve := fun configuration variation parameter =>
    configuration + parameter • variation
  affineCurve_zero := by
    intro configuration variation
    simp
  curve_agreement := by
    intro configuration variation parameter
    rfl
  blocks_c2 := sobolevQuadraticActionBlocks_c2 data

@[simp]
theorem sobolevQuadraticFullAction_zero
    (data : FullCoupledSobolevQuadraticData) :
    sobolevQuadraticFullAction data 0 = 0 := by
  simp [sobolevQuadraticFullAction, sobolevQuadraticActionBlocks,
    fullCoupledAction, sobolevQuadraticBlockAction]

/-- Exact normalized uniqueness on the completed chart: once its complete
Euler one-form is fixed, the quadratic Program-P action is the only action
vanishing at the origin. -/
theorem sobolevQuadraticFullAction_unique
    (data : FullCoupledSobolevQuadraticData)
    (action : ProgramPSobolevConfiguration → ℝ)
    (hAction : ∀ configuration,
      HasFDerivAt action
        (actionGradient (sobolevQuadraticFullAction data) configuration)
        configuration)
    (hNormalized : action 0 = 0) :
    action = sobolevQuadraticFullAction data := by
  have hC2 :
      ContDiff ℝ 2 (sobolevQuadraticFullAction data) :=
    fullCoupledAction_contDiff_two
      (sobolevQuadraticActionBlocks data)
      (sobolevQuadraticActionBlocks_c2 data)
  have hFull : ∀ configuration,
      HasFDerivAt (sobolevQuadraticFullAction data)
        (actionGradient (sobolevQuadraticFullAction data) configuration)
        configuration := by
    intro configuration
    exact (hC2.differentiable (by norm_num) configuration).hasFDerivAt
  have hEqOn :=
    convex_actions_same_euler_eqOn_of_eq_at_base
      (domain := (Set.univ : Set ProgramPSobolevConfiguration))
      convex_univ
      (fun configuration _ => hAction configuration)
      (fun configuration _ => hFull configuration)
      (Set.mem_univ (0 : ProgramPSobolevConfiguration))
      (by rw [hNormalized, sobolevQuadraticFullAction_zero])
  funext configuration
  exact hEqOn (Set.mem_univ configuration)

/-- Concrete convergence of the nine-block quadratic Galerkin actions. -/
theorem sobolevQuadraticGalerkinAction_tendsto
    (data : FullCoupledSobolevQuadraticData)
    (configuration : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff =>
        sobolevGalerkinAction (sobolevQuadraticActionBlocks data)
          cutoff configuration)
      atTop (𝓝 (sobolevQuadraticFullAction data configuration)) :=
  sobolevGalerkinAction_tendsto
    (sobolevQuadraticActionBlocks data)
    (sobolevQuadraticActionBlocks_c2 data)
    configuration

/-- Concrete convergence of every directional Euler evaluation. -/
theorem sobolevQuadraticGalerkinEuler_apply_tendsto
    (data : FullCoupledSobolevQuadraticData)
    (configuration variation : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff =>
        sobolevGalerkinEulerOneForm
          (sobolevQuadraticActionBlocks data)
          cutoff configuration variation)
      atTop
      (𝓝 (actionGradient (sobolevQuadraticFullAction data)
        configuration variation)) :=
  sobolevGalerkinEulerOneForm_apply_tendsto
    (sobolevQuadraticActionBlocks data)
    (sobolevQuadraticActionBlocks_c2 data)
    configuration variation

end

end P0EFTJanusProgramPSobolevGalerkinHelmholtz4D
end JanusFormal
