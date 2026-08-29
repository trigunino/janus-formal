import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

/-!
# D10 smooth core and Hilbert completion

The D10 coefficient Hilbert space is a completion.  A smooth geometric core
should inject into it with dense range and contain every finite mode packet;
it need not be surjective.  This gate proves the finite synthesis and density
consequences from that exact minimal datum.

It also isolates the stronger assertion used by the legacy agreement:
identifying the smooth core with the whole `ℓ²` completion is exactly the
additional surjectivity of the analysis map.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD10SmoothCoreHilbertCompletion4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

variable {Core : Type*} [AddCommGroup Core] [Module ℝ Core]

/-- Canonical unit coordinate vector of one multiplicity-aware D10 mode. -/
def programPD10UnitMode4D
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    ProgramPD10ModeHilbert4D data :=
  lp.single 2 mode 1

/-- Minimal Fourier datum for a core inside the D10 Hilbert completion. -/
structure ProgramPD10CoreSynthesis4D
    (data : ProductThroatSpectralData) (Core : Type*)
    [AddCommGroup Core] [Module ℝ Core] where
  analysis : Core →ₗ[ℝ] ProgramPD10ModeHilbert4D data
  modeVector : ProgramPD10Mode4D data → Core
  analysis_modeVector :
    ∀ mode, analysis (modeVector mode) = programPD10UnitMode4D data mode
  analysis_injective : Function.Injective analysis

namespace ProgramPD10CoreSynthesis4D

variable {data : ProductThroatSpectralData}
variable (synthesis : ProgramPD10CoreSynthesis4D data Core)

/-- Synthesis of an arbitrary finite packet using the core mode vectors. -/
def finiteSynthesis
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) : Core :=
  ∑ mode ∈ modes, (state mode) • synthesis.modeVector mode

/-- Finite core synthesis is exactly the canonical spectral projection. -/
theorem analysis_finiteSynthesis
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    synthesis.analysis (synthesis.finiteSynthesis modes state) =
      programPD10FiniteProjection4D data modes state := by
  classical
  rw [finiteSynthesis, map_sum,
    programPD10FiniteProjection4D_apply]
  apply Finset.sum_congr rfl
  intro mode _
  rw [map_smul, synthesis.analysis_modeVector]
  ext coordinate
  by_cases hCoordinate : coordinate = mode
  · subst coordinate
    simp [programPD10UnitMode4D, lp.single_apply]
  · simp [programPD10UnitMode4D, lp.single_apply,
      hCoordinate]

/-- Every finite spectral packet belongs to the analyzed core. -/
theorem finiteProjection_mem_range
    (modes : Finset (ProgramPD10Mode4D data))
    (state : ProgramPD10ModeHilbert4D data) :
    programPD10FiniteProjection4D data modes state ∈
      Set.range synthesis.analysis :=
  ⟨synthesis.finiteSynthesis modes state,
    synthesis.analysis_finiteSynthesis modes state⟩

/-- Containing all unit modes already forces the core analysis to have dense
range in the Hilbert completion. -/
theorem analysis_denseRange :
    DenseRange synthesis.analysis := by
  intro state
  apply mem_closure_of_tendsto
    (programPD10FiniteProjection4D_tendsto data state)
  exact Filter.Eventually.of_forall fun modes =>
    synthesis.finiteProjection_mem_range modes state

/-- Distinct D10 labels give distinct core vectors. -/
theorem modeVector_injective :
    Function.Injective synthesis.modeVector := by
  intro first second hModes
  have hCoordinates := congrArg synthesis.analysis hModes
  rw [synthesis.analysis_modeVector,
    synthesis.analysis_modeVector] at hCoordinates
  by_contra hNe
  have hAtFirst := congrArg
    (fun state : ProgramPD10ModeHilbert4D data => state first)
    hCoordinates
  simp [programPD10UnitMode4D, lp.single_apply, hNe] at hAtFirst

/-- Finite projection transported to the core through analysis and finite
synthesis; no inverse on the full Hilbert completion is used. -/
def finiteProjection
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) : Core :=
  synthesis.finiteSynthesis modes (synthesis.analysis state)

@[simp]
theorem analysis_finiteProjection
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) :
    synthesis.analysis (synthesis.finiteProjection modes state) =
      programPD10FiniteProjection4D data modes
        (synthesis.analysis state) :=
  synthesis.analysis_finiteSynthesis modes (synthesis.analysis state)

theorem finiteProjection_idempotent
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) :
    synthesis.finiteProjection modes
        (synthesis.finiteProjection modes state) =
      synthesis.finiteProjection modes state := by
  apply synthesis.analysis_injective
  calc
    synthesis.analysis
        (synthesis.finiteProjection modes
          (synthesis.finiteProjection modes state)) =
      programPD10FiniteProjection4D data modes
        (synthesis.analysis
          (synthesis.finiteProjection modes state)) :=
      synthesis.analysis_finiteProjection modes
        (synthesis.finiteProjection modes state)
    _ =
      programPD10FiniteProjection4D data modes
        (programPD10FiniteProjection4D data modes
          (synthesis.analysis state)) := by
      rw [synthesis.analysis_finiteProjection]
    _ =
      programPD10FiniteProjection4D data modes
        (synthesis.analysis state) :=
      programPD10FiniteProjection4D_idempotent
        data modes (synthesis.analysis state)
    _ =
      synthesis.analysis
        (synthesis.finiteProjection modes state) :=
      (synthesis.analysis_finiteProjection modes state).symm

theorem analysis_finiteProjection_coordinate
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core)
    (mode : ProgramPD10Mode4D data) :
    synthesis.analysis (synthesis.finiteProjection modes state) mode =
      if mode ∈ modes then synthesis.analysis state mode else 0 := by
  rw [synthesis.analysis_finiteProjection,
    programPD10FiniteProjection4D_apply_coordinate]

/-- The core norm induced by D10 analysis. -/
def inducedNorm (state : Core) : ℝ :=
  ‖synthesis.analysis state‖

theorem inducedNorm_nonnegative (state : Core) :
    0 ≤ synthesis.inducedNorm state :=
  norm_nonneg _

theorem inducedNorm_eq_zero_iff (state : Core) :
    synthesis.inducedNorm state = 0 ↔ state = 0 := by
  rw [inducedNorm, norm_eq_zero]
  rw [← map_zero synthesis.analysis]
  exact synthesis.analysis_injective.eq_iff

theorem inducedNorm_smul (scalar : ℝ) (state : Core) :
    synthesis.inducedNorm (scalar • state) =
      |scalar| * synthesis.inducedNorm state := by
  rw [inducedNorm, inducedNorm, map_smul, norm_smul,
    Real.norm_eq_abs]

theorem inducedNorm_triangle (first second : Core) :
    synthesis.inducedNorm (first + second) ≤
      synthesis.inducedNorm first + synthesis.inducedNorm second := by
  simpa [inducedNorm] using
    norm_add_le (synthesis.analysis first) (synthesis.analysis second)

/-- Finite mode packets converge to every core vector in the induced Hilbert
norm. -/
theorem finiteProjection_tendsto_inducedNorm
    (state : Core) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        synthesis.inducedNorm
          (synthesis.finiteProjection modes state - state))
      atTop (𝓝 0) := by
  have hProjection :=
    programPD10FiniteProjection4D_tendsto
      data (synthesis.analysis state)
  have hDifference :=
    hProjection.sub_const (synthesis.analysis state)
  simpa [inducedNorm, map_sub,
    synthesis.analysis_finiteProjection] using hDifference.norm

/-- Pullback of the maximal squared-Dirac domain to the core. -/
def fredholmDomain : Set Core :=
  { state |
    synthesis.analysis state ∈
      programPD10FredholmModeDomain4D data }

/-- The core operator has values in the Hilbert completion.  Returning to a
smooth core vector would require a separate elliptic-regularity theorem. -/
def fredholmCoordinateOperator
    (state : { state : Core // state ∈ synthesis.fredholmDomain }) :
    ProgramPD10ModeHilbert4D data :=
  programPD10FredholmModeOperator4D data
    ⟨synthesis.analysis state.1, state.2⟩

theorem finiteProjection_mem_fredholmDomain
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) :
    synthesis.finiteProjection modes state ∈
      synthesis.fredholmDomain := by
  rw [fredholmDomain, Set.mem_setOf_eq,
    synthesis.analysis_finiteProjection]
  exact programPD10FiniteProjection4D_mem_fredholmDomain
    data modes (synthesis.analysis state)

theorem fredholmCoordinateOperator_coercive
    (state : { state : Core // state ∈ synthesis.fredholmDomain }) :
    synthesis.inducedNorm state.1 ≤
      (1 / programPD10SpectralGap4D data) *
        ‖synthesis.fredholmCoordinateOperator state‖ := by
  exact
    programPD10FredholmModeOperator4D_coercive data
      ⟨synthesis.analysis state.1, state.2⟩

/-- Pullback of the exact spectral quadratic-form domain. -/
def quadraticFormDomain : Set Core :=
  { state |
    synthesis.analysis state ∈
      programPD10QuadraticFormDomain4D data }

def quadraticAction (state : Core) : ℝ :=
  programPD10QuadraticAction4D data (synthesis.analysis state)

def finiteQuadraticAction
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) : ℝ :=
  finiteProgramPD10QuadraticAction4D
    data modes (synthesis.analysis state)

theorem finiteProjection_mem_quadraticFormDomain
    (modes : Finset (ProgramPD10Mode4D data))
    (state : Core) :
    synthesis.finiteProjection modes state ∈
      synthesis.quadraticFormDomain := by
  rw [quadraticFormDomain, Set.mem_setOf_eq,
    synthesis.analysis_finiteProjection]
  exact programPD10FiniteProjection4D_mem_quadraticFormDomain
    data modes (synthesis.analysis state)

theorem finiteQuadraticAction_tendsto
    (state : Core)
    (hDomain : state ∈ synthesis.quadraticFormDomain) :
    Tendsto
      (fun modes : Finset (ProgramPD10Mode4D data) =>
        synthesis.finiteQuadraticAction modes state)
      atTop (𝓝 (synthesis.quadraticAction state)) := by
  exact finiteProgramPD10QuadraticAction4D_tendsto
    data (synthesis.analysis state) hDomain

/-- Surjectivity is the precise extra statement needed to replace the dense
core by the whole Hilbert completion. -/
def analysisLinearEquiv
    (hSurjective : Function.Surjective synthesis.analysis) :
    Core ≃ₗ[ℝ] ProgramPD10ModeHilbert4D data :=
  LinearEquiv.ofBijective synthesis.analysis
    ⟨synthesis.analysis_injective, hSurjective⟩

theorem analysis_surjective_iff_exists_linearEquiv :
    Function.Surjective synthesis.analysis ↔
      ∃ equivalence :
          Core ≃ₗ[ℝ] ProgramPD10ModeHilbert4D data,
        equivalence.toLinearMap = synthesis.analysis := by
  constructor
  · intro hSurjective
    exact ⟨synthesis.analysisLinearEquiv hSurjective, rfl⟩
  · rintro ⟨equivalence, hEquivalence⟩
    rw [← hEquivalence]
    exact equivalence.surjective

end ProgramPD10CoreSynthesis4D

/-- The algebraic finite-mode core inside the coefficient Hilbert space. -/
def programPD10FiniteModeCore4D
    (data : ProductThroatSpectralData) :
    Submodule ℝ (ProgramPD10ModeHilbert4D data) :=
  Submodule.span ℝ (Set.range (programPD10UnitMode4D data))

/-- One canonical mode as an element of the finite-mode core. -/
def programPD10FiniteModeCoreVector4D
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    programPD10FiniteModeCore4D data :=
  ⟨programPD10UnitMode4D data mode,
    Submodule.subset_span (Set.mem_range_self mode)⟩

/-- Concrete, assumption-free finite-mode synthesis. -/
def programPD10CoefficientCoreSynthesis4D
    (data : ProductThroatSpectralData) :
    ProgramPD10CoreSynthesis4D data
      (programPD10FiniteModeCore4D data) where
  analysis := (programPD10FiniteModeCore4D data).subtype
  modeVector := programPD10FiniteModeCoreVector4D data
  analysis_modeVector := fun _ => rfl
  analysis_injective := Subtype.val_injective

/-- The concrete finite-mode core is dense in the D10 Hilbert completion. -/
theorem programPD10FiniteModeCore4D_dense :
    ∀ data : ProductThroatSpectralData,
    Dense
      (programPD10FiniteModeCore4D data :
        Set (ProgramPD10ModeHilbert4D data)) := by
  intro data
  have hRange :
      Set.range
          ((programPD10FiniteModeCore4D data).subtype :
            programPD10FiniteModeCore4D data →ₗ[ℝ]
              ProgramPD10ModeHilbert4D data) =
        (programPD10FiniteModeCore4D data :
          Set (ProgramPD10ModeHilbert4D data)) := by
    ext state
    constructor
    · rintro ⟨coreState, rfl⟩
      exact coreState.2
    · intro hState
      exact ⟨⟨state, hState⟩, rfl⟩
  rw [← hRange]
  exact
    (programPD10CoefficientCoreSynthesis4D data).analysis_denseRange

/-- Correct geometric target: smooth complete variations form a dense core
of the D10 completion once actual global mode fields and their analysis have
been constructed. -/
abbrev ProgramPD10GeometricSmoothCoreSynthesis4D
    {period : ℝ} {hPeriod : period ≠ 0}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :=
  ProgramPD10CoreSynthesis4D domain.d7d10SpectralData
    (ProgramPCompleteVariation4D period hPeriod)

end

end P0EFTJanusProgramPD10SmoothCoreHilbertCompletion4D
end JanusFormal
