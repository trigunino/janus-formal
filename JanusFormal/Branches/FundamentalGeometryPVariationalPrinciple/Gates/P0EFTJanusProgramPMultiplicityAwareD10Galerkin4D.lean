import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSeparatedSpectrumProperness

/-!
# Multiplicity-aware D10 Galerkin realization for Program P

This gate restores the literal sphere-degeneracy label in the complete D10
mode Hilbert space.  Finite regulator packets embed without collisions,
arbitrary finite packets converge strongly to the identity, and the maximal
positive squared-Dirac realization is closed, coercive and Fredholm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusSeparatedSpectrumProperness

theorem cutoffCircleMode_injective {cutoff : ℕ} :
    Function.Injective (@cutoffCircleMode cutoff) := by
  rintro ⟨first, firstSign⟩ ⟨second, secondSign⟩ h
  cases firstSign <;> cases secondSign
  all_goals simp [cutoffCircleMode] at h ⊢
  · exact Fin.ext h
  · omega
  · omega
  · exact Fin.ext h

theorem truncatedProgramPD10Mode4D_injective
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ} :
    Function.Injective
      (@truncatedProgramPD10Mode4D data sphereCutoff circleCutoff) := by
  rintro ⟨firstLevel, firstMultiplicity, firstCircle, firstRoot⟩
    ⟨secondLevel, secondMultiplicity, secondCircle, secondRoot⟩ h
  have hLevelValue : firstLevel.val = secondLevel.val := by
    simpa [truncatedProgramPD10Mode4D, truncatedD10Mode] using
      congrArg
        (fun mode : ProgramPD10Mode4D data =>
          mode.separatedMode.sphereLevel) h
  have hLevel : firstLevel = secondLevel := Fin.ext hLevelValue
  subst secondLevel
  have hCircle : firstCircle = secondCircle := by
    apply cutoffCircleMode_injective
    simpa [truncatedProgramPD10Mode4D, truncatedD10Mode] using
      congrArg
        (fun mode : ProgramPD10Mode4D data =>
          mode.separatedMode.circleMode) h
  subst secondCircle
  have hRoot : firstRoot = secondRoot := by
    simpa [truncatedProgramPD10Mode4D, truncatedD10Mode] using
      congrArg
        (fun mode : ProgramPD10Mode4D data =>
          mode.separatedMode.rootChoice) h
  subst secondRoot
  have hMultiplicity : firstMultiplicity = secondMultiplicity := by
    cases h
    rfl
  subst secondMultiplicity
  rfl

/-- Exact finite regulator packet inside the complete multiplicity-aware
mode set. -/
def truncatedProgramPD10ModeFinset4D
    (data : ProductThroatSpectralData)
    (sphereCutoff circleCutoff : ℕ) :
    Finset (ProgramPD10Mode4D data) :=
  Finset.univ.image
    (@truncatedProgramPD10Mode4D data sphereCutoff circleCutoff)

@[simp]
theorem truncatedProgramPD10Mode4D_mem_finset
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    truncatedProgramPD10Mode4D mode ∈
      truncatedProgramPD10ModeFinset4D
        data sphereCutoff circleCutoff := by
  classical
  simp [truncatedProgramPD10ModeFinset4D]

/-- No sphere-degeneracy coordinate is lost when the literal regulator packet
is embedded in the global mode set. -/
theorem truncatedProgramPD10ModeFinset4D_card
    (data : ProductThroatSpectralData)
    (sphereCutoff circleCutoff : ℕ) :
    (truncatedProgramPD10ModeFinset4D
      data sphereCutoff circleCutoff).card =
      Fintype.card
        (TruncatedD10Mode data sphereCutoff circleCutoff) := by
  classical
  rw [truncatedProgramPD10ModeFinset4D,
    Finset.card_image_of_injective _
      truncatedProgramPD10Mode4D_injective,
    Finset.card_univ]

/-- Rank-one projection onto one complete D10 coordinate. -/
def programPD10RankOneProjection4D
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    ProgramPD10ModeHilbert4D data →L[ℝ]
      ProgramPD10ModeHilbert4D data :=
  (lp.singleContinuousLinearMap ℝ
    (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode).comp
      (lp.evalCLM ℝ
        (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode)

theorem programPD10RankOneProjection4D_compact
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    IsCompactOperator (programPD10RankOneProjection4D data mode) := by
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM ℝ
        (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode)).clm_comp
      (lp.singleContinuousLinearMap ℝ
        (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode)

/-- Projection onto an arbitrary finite multiplicity-aware D10 packet. -/
def programPD10FiniteProjection4D
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    ProgramPD10ModeHilbert4D data →L[ℝ]
      ProgramPD10ModeHilbert4D data :=
  ∑ mode ∈ modes, programPD10RankOneProjection4D data mode

theorem programPD10FiniteProjection4D_compact
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    IsCompactOperator (programPD10FiniteProjection4D data modes) := by
  induction modes using Finset.induction_on with
  | empty =>
      simp [programPD10FiniteProjection4D]
      exact isCompactOperator_zero
  | @insert mode modes hMode hInduction =>
      rw [programPD10FiniteProjection4D, Finset.sum_insert hMode]
      exact
        (programPD10RankOneProjection4D_compact data mode).add hInduction

/-- Forgetting the multiplicity label has finite fibers. -/
theorem programPD10SeparatedMode_fiber_finite
    (data : ProductThroatSpectralData)
    (separated : ProductDiracMode) :
    Set.Finite
      { mode : ProgramPD10Mode4D data |
        mode.separatedMode = separated } := by
  let embed :
      Fin (sphereMultiplicity data separated.sphereLevel) →
        ProgramPD10Mode4D data :=
    fun index => ⟨separated, index⟩
  rw [show
    { mode : ProgramPD10Mode4D data |
      mode.separatedMode = separated } =
        Set.range embed by
      ext mode
      constructor
      · intro hMode
        rcases mode with ⟨mode, index⟩
        simp only [Set.mem_setOf_eq] at hMode
        subst mode
        exact ⟨index, rfl⟩
      · rintro ⟨index, rfl⟩
        rfl]
  exact Set.finite_range embed

/-- Proper separated spectral growth survives the finite sphere
multiplicities. -/
theorem programPD10SeparatedDiracWeight4D_proper
    (data : ProductThroatSpectralData)
    (R : ℝ) :
    Set.Finite
      { mode : ProgramPD10Mode4D data |
        ‖(separatedDiracWeight
          data mode.separatedMode : ℂ)‖ ≤ R } := by
  let forget :
      ProgramPD10Mode4D data → ProductDiracMode :=
    ProgramPD10Mode4D.separatedMode
  apply Set.Finite.of_finite_fibers forget
  · exact
      (separated_dirac_weight_proper data R).subset (by
        rintro separated ⟨mode, hMode, rfl⟩
        exact hMode)
  · intro separated _
    exact
      (programPD10SeparatedMode_fiber_finite
        data separated).inter_of_right _

/-- The reciprocal squared spectrum vanishes at infinity, including its
literal finite multiplicities. -/
theorem programPD10InverseMultiplier_vanishes_at_infinity
    (data : ProductThroatSpectralData) :
    ∀ ε : ℝ, 0 < ε →
      Set.Finite
        { mode : ProgramPD10Mode4D data |
          ε ≤ ‖(1 /
            productDiracEigenvalueSquared
              data mode.separatedMode : ℝ)‖ } := by
  intro ε hε
  refine
    (programPD10SeparatedDiracWeight4D_proper
      data (Real.sqrt (1 / ε))).subset ?_
  intro mode hMode
  have hSpectrumPos :
      0 <
        productDiracEigenvalueSquared
          data mode.separatedMode :=
    product_spectrum_has_positive_gap
      data mode.separatedMode
  change ε ≤
    ‖(1 /
      productDiracEigenvalueSquared
        data mode.separatedMode : ℝ)‖ at hMode
  rw [Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hSpectrumPos)] at hMode
  have hSpectrum :
      productDiracEigenvalueSquared
          data mode.separatedMode ≤
        1 / ε := by
    apply (le_div_iff₀ hε).2
    simpa [mul_comm] using
      (le_div_iff₀ hSpectrumPos).1 hMode
  change
    ‖(separatedDiracWeight
      data mode.separatedMode : ℂ)‖ ≤
      Real.sqrt (1 / ε)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (separated_dirac_weight_nonnegative
        data mode.separatedMode)]
  exact Real.sqrt_le_sqrt hSpectrum

theorem programPD10FiniteProjection4D_apply
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FiniteProjection4D data modes state =
      ∑ mode ∈ modes, lp.single 2 mode (state mode) := by
  classical
  simp [programPD10FiniteProjection4D,
    programPD10RankOneProjection4D]
  apply Finset.sum_congr rfl
  intro mode _
  rfl

@[simp]
theorem programPD10FiniteProjection4D_apply_coordinate
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data)
    (coordinate : ProgramPD10Mode4D data) :
    programPD10FiniteProjection4D data modes state coordinate =
      if coordinate ∈ modes then state coordinate else 0 := by
  classical
  rw [programPD10FiniteProjection4D_apply]
  have hEvaluate :
      ((∑ mode ∈ modes,
          lp.single 2 mode (state mode) :
            ProgramPD10ModeHilbert4D data) :
        ProgramPD10ModeHilbert4D data) coordinate =
        ∑ mode ∈ modes,
          (lp.single 2 mode (state mode) :
            ProgramPD10ModeHilbert4D data) coordinate := by
    change (lp.evalCLM ℝ
      (fun _ : ProgramPD10Mode4D data => ℝ) 2 coordinate)
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

theorem programPD10FiniteProjection4D_idempotent
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FiniteProjection4D data modes
        (programPD10FiniteProjection4D data modes state) =
      programPD10FiniteProjection4D data modes state := by
  ext coordinate
  simp only [programPD10FiniteProjection4D_apply_coordinate]
  split_ifs <;> rfl

/-- The unordered net of all finite complete-D10 packets converges strongly
to the identity. -/
theorem programPD10FiniteProjection4D_tendsto
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        programPD10FiniteProjection4D data modes state)
      atTop (𝓝 state) := by
  have hProjection :
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        programPD10FiniteProjection4D data modes state) =
        (fun modes =>
          ∑ mode ∈ modes, lp.single 2 mode (state mode)) := by
    funext modes
    exact programPD10FiniteProjection4D_apply data modes state
  rw [hProjection]
  change HasSum
    (fun mode : ProgramPD10Mode4D data =>
      lp.single 2 mode (state mode)) state
  exact lp.hasSum_single ENNReal.ofNat_ne_top state

/-- The single complete multiplicity-aware D10 Hilbert chart shared by all
nine action functionals.  The nine entries of `FullCoupledActionBlocks` are
functionals on this common chart, not nine independent field copies. -/
abbrev ProgramPMultiplicityD10Configuration4D
    (data : ProductThroatSpectralData) :=
  ProgramPD10ModeHilbert4D data

/-- Finite D10 projection on the common Program-P chart. -/
def configurationProgramPD10FiniteProjection4D
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    ProgramPMultiplicityD10Configuration4D data →L[ℝ]
      ProgramPMultiplicityD10Configuration4D data :=
  programPD10FiniteProjection4D data modes

@[simp]
theorem configurationProgramPD10FiniteProjection4D_apply
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    configurationProgramPD10FiniteProjection4D
      data modes configuration =
      programPD10FiniteProjection4D
        data modes configuration :=
  rfl

theorem configurationProgramPD10FiniteProjection4D_idempotent
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    configurationProgramPD10FiniteProjection4D data modes
        (configurationProgramPD10FiniteProjection4D
          data modes configuration) =
      configurationProgramPD10FiniteProjection4D
        data modes configuration := by
  exact programPD10FiniteProjection4D_idempotent
    data modes configuration

theorem configurationProgramPD10FiniteProjection4D_tendsto
    (data : ProductThroatSpectralData)
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        configurationProgramPD10FiniteProjection4D
          data modes configuration)
      atTop (𝓝 configuration) := by
  exact programPD10FiniteProjection4D_tendsto
    data configuration

/-- Global `C²` hypothesis on the complete multiplicity-aware chart. -/
def ProgramPMultiplicityD10FullCoupledC2
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data)) : Prop :=
  ∀ configuration, FullCoupledC2At blocks configuration

theorem programPMultiplicityD10FullCoupledAction_contDiff_two
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks) :
    ContDiff ℝ 2 (fullCoupledAction blocks) := by
  rw [contDiff_iff_contDiffAt]
  intro configuration
  exact fullCoupledAction_contDiffAt blocks configuration
    (hC2 configuration)

/-- Pullback of the full nine-block action to a finite complete-D10 packet. -/
def programPMultiplicityD10GalerkinAction4D
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) : ℝ :=
  fullCoupledAction blocks
    (configurationProgramPD10FiniteProjection4D
      data modes configuration)

theorem programPMultiplicityD10GalerkinAction4D_contDiff_two
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks)
    (modes : Finset (ProgramPD10Mode4D data)) :
    ContDiff ℝ 2
      (programPMultiplicityD10GalerkinAction4D
        data blocks modes) := by
  exact
    (programPMultiplicityD10FullCoupledAction_contDiff_two
      data blocks hC2).comp
        (configurationProgramPD10FiniteProjection4D
          data modes).contDiff

/-- Every finite complete-D10 pullback obeys nonlinear Helmholtz
reciprocity. -/
theorem programPMultiplicityD10GalerkinAction4D_helmholtz
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    HelmholtzJacobianAt
      (actionGradient
        (programPMultiplicityD10GalerkinAction4D
          data blocks modes))
      configuration :=
  action_gradient_helmholtz_at
    (programPMultiplicityD10GalerkinAction4D
      data blocks modes)
    configuration
    (programPMultiplicityD10GalerkinAction4D_contDiff_two
      data blocks hC2 modes).contDiffAt

/-- Exact chain-rule Euler form of the finite complete-D10 action. -/
def programPMultiplicityD10GalerkinEulerOneForm4D
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (modes : Finset (ProgramPD10Mode4D data)) :
    EulerOneForm (ProgramPMultiplicityD10Configuration4D data) :=
  fun configuration =>
    (actionGradient (fullCoupledAction blocks)
      (configurationProgramPD10FiniteProjection4D
        data modes configuration)).comp
          (configurationProgramPD10FiniteProjection4D data modes)

theorem programPMultiplicityD10GalerkinAction4D_hasFDerivAt
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    HasFDerivAt
      (programPMultiplicityD10GalerkinAction4D
        data blocks modes)
      (programPMultiplicityD10GalerkinEulerOneForm4D
        data blocks modes configuration)
      configuration := by
  have hAction :
      HasFDerivAt (fullCoupledAction blocks)
        (actionGradient (fullCoupledAction blocks)
          (configurationProgramPD10FiniteProjection4D
            data modes configuration))
        (configurationProgramPD10FiniteProjection4D
          data modes configuration) := by
    exact
      ((programPMultiplicityD10FullCoupledAction_contDiff_two
        data blocks hC2).differentiable
          (by norm_num)
          (configurationProgramPD10FiniteProjection4D
            data modes configuration)).hasFDerivAt
  exact hAction.comp configuration
    (configurationProgramPD10FiniteProjection4D
      data modes).hasFDerivAt

theorem programPMultiplicityD10GalerkinAction4D_tendsto
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks)
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        programPMultiplicityD10GalerkinAction4D
          data blocks modes configuration)
      atTop (𝓝 (fullCoupledAction blocks configuration)) := by
  exact Filter.Tendsto.comp
    (programPMultiplicityD10FullCoupledAction_contDiff_two
      data blocks hC2).continuous.continuousAt
    (configurationProgramPD10FiniteProjection4D_tendsto
      data configuration)

theorem programPMultiplicityD10GalerkinEuler_apply_tendsto
    (data : ProductThroatSpectralData)
    (blocks :
      FullCoupledActionBlocks
        (ProgramPMultiplicityD10Configuration4D data))
    (hC2 : ProgramPMultiplicityD10FullCoupledC2 data blocks)
    (configuration variation :
      ProgramPMultiplicityD10Configuration4D data) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        programPMultiplicityD10GalerkinEulerOneForm4D
          data blocks modes configuration variation)
      atTop
      (𝓝 (actionGradient
        (fullCoupledAction blocks) configuration variation)) := by
  have hAction :=
    programPMultiplicityD10FullCoupledAction_contDiff_two
      data blocks hC2
  have hGradient :
      ContDiff ℝ 1 (actionGradient (fullCoupledAction blocks)) := by
    change ContDiff ℝ 1 (fderiv ℝ (fullCoupledAction blocks))
    exact hAction.fderiv_right (by norm_num)
  have hEvaluation : Continuous
      (fun pair :
          ProgramPMultiplicityD10Configuration4D data ×
            ProgramPMultiplicityD10Configuration4D data =>
        actionGradient
          (fullCoupledAction blocks) pair.1 pair.2) :=
    ((hGradient.comp contDiff_fst).clm_apply contDiff_snd).continuous
  exact Filter.Tendsto.comp hEvaluation.continuousAt
    ((configurationProgramPD10FiniteProjection4D_tendsto
      data configuration).prodMk_nhds
        (configurationProgramPD10FiniteProjection4D_tendsto
          data variation))

/-- The existing maximal diagonal domain, bundled as a real submodule. -/
def programPD10FredholmModeDomainSubmodule4D
    (data : ProductThroatSpectralData) :
    Submodule ℝ (ProgramPD10ModeHilbert4D data) where
  carrier := programPD10FredholmModeDomain4D data
  zero_mem' := by
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          (0 : ProgramPD10ModeHilbert4D data) mode) 2
    convert
      (zero_memℓp :
        Memℓp (0 : ProgramPD10Mode4D data → ℝ) 2) using 1
    funext mode
    simp
  add_mem' := by
    intro first second hFirst hSecond
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          first mode) 2 at hFirst
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          second mode) 2 at hSecond
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          (first + second) mode) 2
    convert hFirst.add hSecond using 1
    funext mode
    simp [mul_add]
  smul_mem' := by
    intro scalar state hState
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          state mode) 2 at hState
    change Memℓp
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode *
          (scalar • state) mode) 2
    convert hState.const_smul scalar using 1
    funext mode
    simp [smul_eq_mul, mul_left_comm]

@[simp]
theorem programPD10FredholmModeDomainSubmodule4D_coe
    (data : ProductThroatSpectralData) :
    (programPD10FredholmModeDomainSubmodule4D data :
      Set (ProgramPD10ModeHilbert4D data)) =
      programPD10FredholmModeDomain4D data := by
  ext state
  rfl

/-- The multiplicity-aware unbounded squared-Dirac operator on its maximal
diagonal domain. -/
def programPD10FredholmModeOperator4D
    (data : ProductThroatSpectralData) :
    programPD10FredholmModeDomainSubmodule4D data →ₗ[ℝ]
      ProgramPD10ModeHilbert4D data where
  toFun state :=
    ⟨fun mode =>
      productDiracEigenvalueSquared data mode.separatedMode *
        state.1 mode,
      by
        have hState := state.property
        change Memℓp
          (fun mode : ProgramPD10Mode4D data =>
            productDiracEigenvalueSquared data mode.separatedMode *
              state.1 mode) 2 at hState
        exact hState⟩
  map_add' first second := by
    ext mode
    simp [mul_add]
  map_smul' scalar state := by
    ext mode
    simp [smul_eq_mul]
    ring

@[simp]
theorem programPD10FredholmModeOperator4D_apply
    (data : ProductThroatSpectralData)
    (state : programPD10FredholmModeDomainSubmodule4D data)
    (mode : ProgramPD10Mode4D data) :
    programPD10FredholmModeOperator4D data state mode =
      productDiracEigenvalueSquared data mode.separatedMode *
        state.1 mode :=
  rfl

/-- Every finite spectral packet belongs to the maximal operator domain. -/
theorem programPD10FiniteProjection4D_mem_fredholmDomain
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FiniteProjection4D data modes state ∈
      programPD10FredholmModeDomain4D data := by
  change Memℓp
    (fun mode : ProgramPD10Mode4D data =>
      productDiracEigenvalueSquared data mode.separatedMode *
        programPD10FiniteProjection4D data modes state mode) 2
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := modes)
  intro mode hMode
  rw [programPD10FiniteProjection4D_apply_coordinate,
    if_neg hMode]
  simp

/-- Every Hilbert vector is a strong limit of vectors in the maximal
operator domain. -/
theorem programPD10_mem_closure_fredholmModeDomain4D
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) :
    state ∈ closure (programPD10FredholmModeDomain4D data) := by
  apply mem_closure_of_tendsto
    (programPD10FiniteProjection4D_tendsto data state)
  exact Filter.Eventually.of_forall fun modes =>
    programPD10FiniteProjection4D_mem_fredholmDomain
      data modes state

/-- The maximal multiplicity-aware squared-Dirac domain is dense. -/
theorem programPD10FredholmModeDomain4D_dense
    (data : ProductThroatSpectralData) :
    Dense (programPD10FredholmModeDomain4D data) := by
  apply dense_iff_closure_eq.mpr
  exact Set.eq_univ_of_forall fun state =>
    programPD10_mem_closure_fredholmModeDomain4D data state

/-- The diagonal squared-Dirac realization is symmetric on its maximal
domain. -/
theorem programPD10FredholmModeOperator4D_symmetric
    (data : ProductThroatSpectralData)
    (first second :
      programPD10FredholmModeDomainSubmodule4D data) :
    inner ℝ (programPD10FredholmModeOperator4D data first) second.1 =
      inner ℝ first.1
        (programPD10FredholmModeOperator4D data second) := by
  apply tsum_congr
  intro mode
  simp
  ring

/-- Uniform positive lower bound supplied by the sphere factor. -/
def programPD10SpectralGap4D
    (data : ProductThroatSpectralData) : ℝ :=
  1 / data.sphereRadius ^ 2

theorem programPD10SpectralGap4D_pos
    (data : ProductThroatSpectralData) :
    0 < programPD10SpectralGap4D data := by
  exact one_div_pos.mpr
    (sq_pos_of_pos data.sphereRadiusPositive)

theorem programPD10SpectralGap4D_le
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    programPD10SpectralGap4D data ≤
      productDiracEigenvalueSquared data mode.separatedMode := by
  have hRadius :
      0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  have hFirstNat :
      1 ≤ mode.separatedMode.sphereLevel + 1 := by
    omega
  have hSecondNat :
      1 ≤ mode.separatedMode.sphereLevel + 1 +
        monopoleAbsCharge data := by
    omega
  have hFirst :
      (1 : ℝ) ≤
        ((mode.separatedMode.sphereLevel + 1 : ℕ) : ℝ) := by
    exact_mod_cast hFirstNat
  have hSecond :
      (1 : ℝ) ≤
        ((mode.separatedMode.sphereLevel + 1 +
          monopoleAbsCharge data : ℕ) : ℝ) := by
    exact_mod_cast hSecondNat
  have hProduct :
      (1 : ℝ) ≤
        ((mode.separatedMode.sphereLevel + 1 : ℕ) : ℝ) *
          ((mode.separatedMode.sphereLevel + 1 +
            monopoleAbsCharge data : ℕ) : ℝ) := by
    simpa using
      mul_le_mul hFirst hSecond zero_le_one (by positivity)
  unfold programPD10SpectralGap4D
    productDiracEigenvalueSquared sphereEigenvalueSquared
  exact
    ((div_le_div_iff_of_pos_right hRadius).2 hProduct).trans
      (le_add_of_nonneg_right (sq_nonneg _))

theorem programPD10InverseMultiplier_norm_le
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    ‖(1 /
      productDiracEigenvalueSquared
        data mode.separatedMode : ℝ)‖ ≤
      1 / programPD10SpectralGap4D data := by
  rw [Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr
      (product_spectrum_has_positive_gap
        data mode.separatedMode))]
  exact one_div_le_one_div_of_le
    (programPD10SpectralGap4D_pos data)
    (programPD10SpectralGap4D_le data mode)

/-- The diagonal quadratic-form domain, one derivative below the maximal
squared-Dirac operator domain. -/
def programPD10QuadraticFormDomain4D
    (data : ProductThroatSpectralData) :
    Set (ProgramPD10ModeHilbert4D data) :=
  { state |
    Summable (fun mode : ProgramPD10Mode4D data =>
      productDiracEigenvalueSquared data mode.separatedMode *
        (state mode) ^ 2) }

/-- Finite complete-D10 packets lie in the quadratic-form domain. -/
theorem programPD10FiniteProjection4D_mem_quadraticFormDomain
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FiniteProjection4D data modes state ∈
      programPD10QuadraticFormDomain4D data := by
  change Summable
    (fun mode : ProgramPD10Mode4D data =>
      productDiracEigenvalueSquared data mode.separatedMode *
        (programPD10FiniteProjection4D
          data modes state mode) ^ 2)
  apply summable_of_ne_finset_zero (s := modes)
  intro mode hMode
  rw [programPD10FiniteProjection4D_apply_coordinate,
    if_neg hMode]
  simp

/-- The maximal squared-Dirac operator domain is contained in its quadratic
form domain, by the `ℓ² × ℓ² → ℓ¹` Hölder estimate. -/
theorem programPD10FredholmModeDomain4D_subset_quadraticFormDomain
    (data : ProductThroatSpectralData) :
    programPD10FredholmModeDomain4D data ⊆
      programPD10QuadraticFormDomain4D data := by
  intro state hDomain
  let weightedState : ProgramPD10ModeHilbert4D data :=
    ⟨fun mode =>
      productDiracEigenvalueSquared data mode.separatedMode *
        state mode,
      hDomain⟩
  have hProduct :
      Summable (fun mode : ProgramPD10Mode4D data =>
        ‖state mode‖ * ‖weightedState mode‖) :=
    lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num)
      state weightedState
  change Summable
    (fun mode : ProgramPD10Mode4D data =>
      productDiracEigenvalueSquared data mode.separatedMode *
        (state mode) ^ 2)
  apply Summable.of_norm
  simpa [weightedState, pow_two, norm_mul, mul_assoc,
    mul_left_comm, mul_comm] using hProduct

/-- The positive product spectrum gives a trivial kernel on the maximal
domain. -/
theorem programPD10FredholmModeOperator4D_injective
    (data : ProductThroatSpectralData) :
    Function.Injective (programPD10FredholmModeOperator4D data) := by
  intro first second hOperator
  apply Subtype.ext
  ext mode
  have hCoordinate := congrArg
    (fun state : ProgramPD10ModeHilbert4D data => state mode)
    hOperator
  simp only [programPD10FredholmModeOperator4D_apply] at hCoordinate
  exact mul_left_cancel₀
    (ne_of_gt
      (product_spectrum_has_positive_gap
        data mode.separatedMode))
    hCoordinate

/-- Bounded inverse multiplier on the ambient Hilbert space. -/
def programPD10FredholmInverseLinearMap4D
    (data : ProductThroatSpectralData) :
    ProgramPD10ModeHilbert4D data →ₗ[ℝ]
      ProgramPD10ModeHilbert4D data where
  toFun state :=
    ⟨fun mode =>
      (1 /
        productDiracEigenvalueSquared data mode.separatedMode) *
          state mode,
      by
        refine
          (state.2.norm.const_mul
            (1 / programPD10SpectralGap4D data)).mono ?_
        intro mode
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (programPD10InverseMultiplier_norm_le data mode)
          (norm_nonneg (state mode))⟩
  map_add' first second := by
    ext mode
    simp [mul_add]
  map_smul' scalar state := by
    ext mode
    simp [smul_eq_mul, mul_left_comm]

/-- Continuous ambient inverse, with norm controlled by the geometric
spectral gap. -/
def programPD10FredholmInverseCLM4D
    (data : ProductThroatSpectralData) :
    ProgramPD10ModeHilbert4D data →L[ℝ]
      ProgramPD10ModeHilbert4D data :=
  (programPD10FredholmInverseLinearMap4D data).mkContinuous
    (1 / programPD10SpectralGap4D data) (by
      intro state
      rw [← show
        ‖(1 / programPD10SpectralGap4D data : ℝ) • state‖ =
          (1 / programPD10SpectralGap4D data) * ‖state‖ by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (one_div_pos.mpr
            (programPD10SpectralGap4D_pos data))]]
      apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      intro mode
      change
        ‖(1 /
          productDiracEigenvalueSquared data mode.separatedMode) *
            state mode‖ ≤
          ‖(1 / programPD10SpectralGap4D data : ℝ) •
            state mode‖
      rw [norm_mul, norm_smul,
        Real.norm_of_nonneg
          (one_div_pos.mpr
            (programPD10SpectralGap4D_pos data)).le]
      exact mul_le_mul_of_nonneg_right
        (programPD10InverseMultiplier_norm_le data mode)
        (norm_nonneg (state mode)))

@[simp]
theorem programPD10FredholmInverseCLM4D_apply
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data)
    (mode : ProgramPD10Mode4D data) :
    programPD10FredholmInverseCLM4D data state mode =
      (1 /
        productDiracEigenvalueSquared data mode.separatedMode) *
          state mode :=
  rfl

/-- Finite-rank truncation of the bounded Fredholm inverse. -/
def programPD10FiniteInverseTruncation4D
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    ProgramPD10ModeHilbert4D data →L[ℝ]
      ProgramPD10ModeHilbert4D data :=
  (programPD10FredholmInverseCLM4D data).comp
    (programPD10FiniteProjection4D data modes)

@[simp]
theorem programPD10FiniteInverseTruncation4D_apply
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data)
    (mode : ProgramPD10Mode4D data) :
    programPD10FiniteInverseTruncation4D
        data modes state mode =
      if mode ∈ modes then
        (1 /
          productDiracEigenvalueSquared
            data mode.separatedMode) * state mode
      else 0 := by
  simp [programPD10FiniteInverseTruncation4D,
    programPD10FiniteProjection4D_apply_coordinate]

theorem programPD10FiniteInverseTruncation4D_compact
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    IsCompactOperator
      (programPD10FiniteInverseTruncation4D data modes) := by
  exact
    (programPD10FiniteProjection4D_compact
      data modes).clm_comp
        (programPD10FredholmInverseCLM4D data)

theorem programPD10Inverse_sub_finite_truncation_norm_le
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hTail : ∀ mode, mode ∉ modes →
      ‖(1 /
        productDiracEigenvalueSquared
          data mode.separatedMode : ℝ)‖ ≤ ε) :
    ‖programPD10FredholmInverseCLM4D data -
      programPD10FiniteInverseTruncation4D data modes‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro state
  rw [← show ‖(ε : ℝ) • state‖ = ε * ‖state‖ by
    simpa [Real.norm_eq_abs, abs_of_nonneg hε] using
      (norm_smul (ε : ℝ) state)]
  apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
  intro mode
  change
    ‖(1 /
        productDiracEigenvalueSquared
          data mode.separatedMode) * state mode -
      programPD10FiniteInverseTruncation4D
        data modes state mode‖ ≤
      ‖(ε : ℝ) • state mode‖
  by_cases hMode : mode ∈ modes
  · rw [programPD10FiniteInverseTruncation4D_apply,
      if_pos hMode, sub_self]
    simpa only [norm_zero] using
      norm_nonneg ((ε : ℝ) • (state mode : ℝ))
  · rw [programPD10FiniteInverseTruncation4D_apply,
      if_neg hMode, sub_zero, norm_mul, norm_smul]
    simpa only [Real.norm_of_nonneg hε] using
      mul_le_mul_of_nonneg_right
        (hTail mode hMode) (norm_nonneg (state mode))

noncomputable def programPD10InverseDecayModes4D
    (data : ProductThroatSpectralData)
    (n : ℕ) : Finset (ProgramPD10Mode4D data) :=
  (programPD10InverseMultiplier_vanishes_at_infinity
    data (1 / ((n : ℝ) + 1)) (by positivity)).toFinset

theorem programPD10FiniteInverseTruncation4D_norm_sub_inverse_le
    (data : ProductThroatSpectralData)
    (n : ℕ) :
    ‖programPD10FiniteInverseTruncation4D
        data (programPD10InverseDecayModes4D data n) -
      programPD10FredholmInverseCLM4D data‖ ≤
        1 / ((n : ℝ) + 1) := by
  rw [norm_sub_rev]
  apply programPD10Inverse_sub_finite_truncation_norm_le
  · positivity
  · intro mode hMode
    have hNotSuperlevel :
        mode ∉
          { mode : ProgramPD10Mode4D data |
            1 / ((n : ℝ) + 1) ≤
              ‖(1 /
                productDiracEigenvalueSquared
                  data mode.separatedMode : ℝ)‖ } := by
      simpa [programPD10InverseDecayModes4D] using hMode
    exact le_of_lt (not_le.1 hNotSuperlevel)

/-- The inverse of the positive multiplicity-aware squared-Dirac
realization is compact. -/
theorem programPD10FredholmInverseCLM4D_compact
    (data : ProductThroatSpectralData) :
    IsCompactOperator
      (programPD10FredholmInverseCLM4D data) := by
  apply isCompactOperator_of_tendsto
    (l := Filter.atTop)
    (F := fun n : ℕ =>
      programPD10FiniteInverseTruncation4D
        data (programPD10InverseDecayModes4D data n))
    (f := programPD10FredholmInverseCLM4D data)
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    exact squeeze_zero
      (fun n => norm_nonneg _)
      (programPD10FiniteInverseTruncation4D_norm_sub_inverse_le data)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall fun n =>
      programPD10FiniteInverseTruncation4D_compact
        data (programPD10InverseDecayModes4D data n)

theorem programPD10FredholmInverseCLM4D_mem_domain
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FredholmInverseCLM4D data state ∈
      programPD10FredholmModeDomain4D data := by
  change Memℓp
    (fun mode : ProgramPD10Mode4D data =>
      productDiracEigenvalueSquared data mode.separatedMode *
        programPD10FredholmInverseCLM4D data state mode) 2
  have hState :
      Memℓp (fun mode : ProgramPD10Mode4D data => state mode) 2 :=
    lp.memℓp state
  convert hState using 1
  funext mode
  simp [ne_of_gt
    (product_spectrum_has_positive_gap
      data mode.separatedMode)]

/-- Explicit inverse vector, bundled in the maximal operator domain. -/
def programPD10FredholmInverseDomain4D
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FredholmModeDomainSubmodule4D data :=
  ⟨programPD10FredholmInverseCLM4D data state,
    programPD10FredholmInverseCLM4D_mem_domain data state⟩

@[simp]
theorem programPD10FredholmModeOperator4D_inverse
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FredholmModeOperator4D data
      (programPD10FredholmInverseDomain4D data state) = state := by
  ext mode
  simp [programPD10FredholmInverseDomain4D,
    ne_of_gt
      (product_spectrum_has_positive_gap
        data mode.separatedMode)]

@[simp]
theorem programPD10FredholmInverseCLM4D_operator
    (data : ProductThroatSpectralData)
    (state : programPD10FredholmModeDomainSubmodule4D data) :
    programPD10FredholmInverseCLM4D data
      (programPD10FredholmModeOperator4D data state) = state.1 := by
  ext mode
  simp [ne_of_gt
    (product_spectrum_has_positive_gap
      data mode.separatedMode)]

theorem programPD10FredholmModeOperator4D_surjective
    (data : ProductThroatSpectralData) :
    Function.Surjective (programPD10FredholmModeOperator4D data) := by
  intro state
  exact
    ⟨programPD10FredholmInverseDomain4D data state,
      programPD10FredholmModeOperator4D_inverse data state⟩

/-- The maximal positive squared-Dirac realization is algebraically
invertible; hence its kernel and cokernel are both zero. -/
theorem programPD10FredholmModeOperator4D_bijective
    (data : ProductThroatSpectralData) :
    Function.Bijective (programPD10FredholmModeOperator4D data) :=
  ⟨programPD10FredholmModeOperator4D_injective data,
    programPD10FredholmModeOperator4D_surjective data⟩

theorem programPD10FredholmInverseCLM4D_norm_le
    (data : ProductThroatSpectralData) :
    ‖programPD10FredholmInverseCLM4D data‖ ≤
      1 / programPD10SpectralGap4D data := by
  apply LinearMap.mkContinuous_norm_le
  exact (one_div_pos.mpr
    (programPD10SpectralGap4D_pos data)).le

/-- Quantitative coercivity estimate obtained from the bounded inverse. -/
theorem programPD10FredholmModeOperator4D_coercive
    (data : ProductThroatSpectralData)
    (state : programPD10FredholmModeDomainSubmodule4D data) :
    ‖state.1‖ ≤
      (1 / programPD10SpectralGap4D data) *
        ‖programPD10FredholmModeOperator4D data state‖ := by
  rw [← programPD10FredholmInverseCLM4D_operator data state]
  exact
    (programPD10FredholmInverseCLM4D data).le_of_opNorm_le
      (programPD10FredholmInverseCLM4D_norm_le data)
      (programPD10FredholmModeOperator4D data state)

/-- Coordinate graph of the maximal multiplicity-aware squared-Dirac
operator. -/
def programPD10FredholmModeGraph4D
    (data : ProductThroatSpectralData) :
    Set (ProgramPD10ModeHilbert4D data ×
      ProgramPD10ModeHilbert4D data) :=
  { pair | ∀ mode,
    pair.2 mode =
      productDiracEigenvalueSquared data mode.separatedMode *
        pair.1 mode }

theorem programPD10FredholmModeGraph4D_iff
    (data : ProductThroatSpectralData)
    (pair : ProgramPD10ModeHilbert4D data ×
      ProgramPD10ModeHilbert4D data) :
    pair ∈ programPD10FredholmModeGraph4D data ↔
      ∃ state : programPD10FredholmModeDomainSubmodule4D data,
        state.1 = pair.1 ∧
          programPD10FredholmModeOperator4D data state = pair.2 := by
  constructor
  · intro hPair
    have hWeighted : Memℓp
        (fun mode : ProgramPD10Mode4D data =>
          productDiracEigenvalueSquared data mode.separatedMode *
            pair.1 mode) 2 := by
      rw [show
        (fun mode : ProgramPD10Mode4D data =>
          productDiracEigenvalueSquared data mode.separatedMode *
            pair.1 mode) =
          (fun mode => pair.2 mode) by
        funext mode
        exact (hPair mode).symm]
      exact lp.memℓp pair.2
    let state : programPD10FredholmModeDomainSubmodule4D data :=
      ⟨pair.1, hWeighted⟩
    refine ⟨state, rfl, ?_⟩
    ext mode
    exact (hPair mode).symm
  · rintro ⟨state, hState, hOperator⟩ mode
    rw [← hOperator]
    simp [hState]

/-- The maximal multiplicity-aware diagonal realization is closed. -/
theorem programPD10FredholmModeGraph4D_closed
    (data : ProductThroatSpectralData) :
    IsClosed (programPD10FredholmModeGraph4D data) := by
  rw [show programPD10FredholmModeGraph4D data =
      ⋂ mode : ProgramPD10Mode4D data,
        { pair |
          pair.2 mode =
            productDiracEigenvalueSquared
              data mode.separatedMode * pair.1 mode } by
    ext pair
    simp [programPD10FredholmModeGraph4D]]
  apply isClosed_iInter
  intro mode
  exact isClosed_eq
    ((lp.evalCLM ℝ
      (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode).continuous.comp
        continuous_snd)
    (continuous_const.mul
      ((lp.evalCLM ℝ
        (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode).continuous.comp
          continuous_fst))

/-- Closed, densely defined, symmetric and bijective compact-resolvent
Fredholm certificate for the complete multiplicity-aware D10 realization. -/
structure ProgramPD10FredholmCertificate4D
    (data : ProductThroatSpectralData) : Prop where
  domainDense : Dense (programPD10FredholmModeDomain4D data)
  graphClosed : IsClosed (programPD10FredholmModeGraph4D data)
  symmetric : ∀ first second :
      programPD10FredholmModeDomainSubmodule4D data,
    inner ℝ (programPD10FredholmModeOperator4D data first) second.1 =
      inner ℝ first.1
        (programPD10FredholmModeOperator4D data second)
  bijective :
    Function.Bijective (programPD10FredholmModeOperator4D data)
  inverseContinuous :
    Continuous (programPD10FredholmInverseCLM4D data)
  inverseCompact :
    IsCompactOperator (programPD10FredholmInverseCLM4D data)

theorem programPD10FredholmCertificate4D
    (data : ProductThroatSpectralData) :
    ProgramPD10FredholmCertificate4D data where
  domainDense := programPD10FredholmModeDomain4D_dense data
  graphClosed := programPD10FredholmModeGraph4D_closed data
  symmetric := programPD10FredholmModeOperator4D_symmetric data
  bijective := programPD10FredholmModeOperator4D_bijective data
  inverseContinuous :=
    (programPD10FredholmInverseCLM4D data).continuous
  inverseCompact :=
    programPD10FredholmInverseCLM4D_compact data

/-- Spectral quadratic action on one complete multiplicity-aware D10
Hilbert block. -/
def programPD10QuadraticAction4D
    (data : ProductThroatSpectralData)
    (state : ProgramPD10ModeHilbert4D data) : ℝ :=
  (1 / 2 : ℝ) * ∑' mode : ProgramPD10Mode4D data,
    productDiracEigenvalueSquared data mode.separatedMode *
      (state mode) ^ 2

/-- On the operator domain, the spectral action is exactly
`(1/2) ⟪x, D²x⟫`. -/
theorem programPD10QuadraticAction4D_eq_inner_operator
    (data : ProductThroatSpectralData)
    (state : programPD10FredholmModeDomainSubmodule4D data) :
    programPD10QuadraticAction4D data state.1 =
      (1 / 2 : ℝ) *
        inner ℝ state.1
          (programPD10FredholmModeOperator4D data state) := by
  change
    (1 / 2 : ℝ) * ∑' mode : ProgramPD10Mode4D data,
      productDiracEigenvalueSquared data mode.separatedMode *
        (state.1 mode) ^ 2 =
    (1 / 2 : ℝ) * ∑' mode : ProgramPD10Mode4D data,
      inner ℝ (state.1 mode)
        (productDiracEigenvalueSquared data mode.separatedMode *
          state.1 mode)
  congr 1
  apply tsum_congr
  intro mode
  simp [pow_two]
  ring

/-- Finite quadratic action on the common complete-D10 chart. -/
def finiteProgramPD10QuadraticAction4D
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) : ℝ :=
  (1 / 2 : ℝ) * ∑ mode ∈ modes,
    productDiracEigenvalueSquared data mode.separatedMode *
      (configuration mode) ^ 2

theorem finiteProgramPD10QuadraticAction4D_contDiff_two
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data)) :
    ContDiff ℝ 2
      (finiteProgramPD10QuadraticAction4D
        data modes) := by
  unfold finiteProgramPD10QuadraticAction4D
  have hSum : ContDiff ℝ 2
      (fun configuration :
          ProgramPMultiplicityD10Configuration4D data =>
        ∑ mode ∈ modes,
          productDiracEigenvalueSquared data mode.separatedMode *
            (configuration mode) ^ 2) := by
    apply ContDiff.sum
    intro mode _
    have hMode : ContDiff ℝ 2
        (fun configuration :
            ProgramPMultiplicityD10Configuration4D data =>
          configuration mode) :=
      (lp.evalCLM ℝ
        (fun _ : ProgramPD10Mode4D data => ℝ) 2 mode).contDiff
    simpa [smul_eq_mul] using
      ContDiff.const_smul
        (productDiracEigenvalueSquared
          data mode.separatedMode)
        (hMode.pow 2)
  simpa [smul_eq_mul] using
    ContDiff.const_smul (1 / 2 : ℝ) hSum

theorem finiteProgramPD10QuadraticAction4D_helmholtz
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    HelmholtzJacobianAt
      (actionGradient
        (finiteProgramPD10QuadraticAction4D
          data modes))
      configuration :=
  action_gradient_helmholtz_at
    (finiteProgramPD10QuadraticAction4D data modes)
    configuration
    (finiteProgramPD10QuadraticAction4D_contDiff_two
      data modes).contDiffAt

/-- Quadratic-form domain on the common Program-P chart. -/
def ProgramPMultiplicityD10QuadraticFormDomain4D
    (data : ProductThroatSpectralData) :
    Set (ProgramPMultiplicityD10Configuration4D data) :=
  programPD10QuadraticFormDomain4D data

theorem configurationProgramPD10FiniteProjection4D_mem_formDomain
    (data : ProductThroatSpectralData)
    (modes : Finset (ProgramPD10Mode4D data))
    (configuration : ProgramPMultiplicityD10Configuration4D data) :
    configurationProgramPD10FiniteProjection4D
      data modes configuration ∈
        ProgramPMultiplicityD10QuadraticFormDomain4D
          data := by
  exact programPD10FiniteProjection4D_mem_quadraticFormDomain
    data modes configuration

/-- Infinite spectral action on the common complete-D10 chart. -/
def programPMultiplicityD10QuadraticAction4D
    (data : ProductThroatSpectralData)
    (configuration : ProgramPMultiplicityD10Configuration4D data) : ℝ :=
  programPD10QuadraticAction4D data configuration

/-- Arbitrary finite multiplicity-aware packets recover the full spectral
quadratic action on its exact form domain. -/
theorem finiteProgramPD10QuadraticAction4D_tendsto
    (data : ProductThroatSpectralData)
    (configuration : ProgramPMultiplicityD10Configuration4D data)
    (hDomain : configuration ∈
      ProgramPMultiplicityD10QuadraticFormDomain4D data) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        finiteProgramPD10QuadraticAction4D
          data modes configuration)
      atTop
      (𝓝 (programPMultiplicityD10QuadraticAction4D
        data configuration)) := by
  change Tendsto
    (fun modes : Finset (ProgramPD10Mode4D data) =>
      (1 / 2 : ℝ) * ∑ mode ∈ modes,
        productDiracEigenvalueSquared data mode.separatedMode *
          (configuration mode) ^ 2)
    atTop
    (𝓝 ((1 / 2 : ℝ) *
      ∑' mode : ProgramPD10Mode4D data,
        productDiracEigenvalueSquared data mode.separatedMode *
          (configuration mode) ^ 2))
  exact tendsto_const_nhds.mul hDomain.hasSum

end

end P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
end JanusFormal
