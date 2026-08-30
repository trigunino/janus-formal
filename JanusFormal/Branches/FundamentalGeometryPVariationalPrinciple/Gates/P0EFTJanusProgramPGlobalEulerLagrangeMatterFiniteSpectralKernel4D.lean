import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralResidual4D

/-!
# Kernel of the finite SpinC spectral residual

The exact finite-mode critical locus is the set of coefficient families
supported on modes where `2D + m² = 0`.  This gives uniqueness off resonance
and explicit nonzero critical points on resonance.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralKernel4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

local instance matterFiniteCoreNormedAddCommGroup (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    period hPeriod massSquared

local instance matterFiniteCoreNormedSpace (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod massSquared

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Spectral mass shell on which the strong coefficient residual vanishes. -/
def globalCandidateAMatterFiniteSpectralMassShell
    (massSquared : Real) : Set ProgramPPrimitiveSpinCMatterMode :=
  {mode | programPPrimitiveSpinCMatterHessianWeight
    period hPeriod massSquared mode = 0}

@[simp]
theorem globalCandidateAMatterFiniteSpectralResidual_apply
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    globalCandidateAMatterFiniteSpectralResidual period hPeriod massSquared
        core mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) *
        ((globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod
          massSquared).symm core) mode := by
  simp [globalCandidateAMatterFiniteSpectralResidual]

/-- The strong residual vanishes exactly when every supported coefficient lies
on the spectral mass shell. -/
theorem globalCandidateAMatterFiniteSpectralResidual_eq_zero_iff_support
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteSpectralResidual period hPeriod massSquared
        core = 0 ↔
      ((↑((globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod
        massSquared).symm core).support :
          Set ProgramPPrimitiveSpinCMatterMode) ⊆
        globalCandidateAMatterFiniteSpectralMassShell period hPeriod
          massSquared) := by
  let coefficients := (globalCandidateAMatterFiniteGraphCoreEquiv period
    hPeriod massSquared).symm core
  constructor
  · intro hResidual mode hMode
    have hCoefficient : coefficients mode ≠ 0 :=
      Finsupp.mem_support_iff.mp hMode
    have hApply := congrArg
      (fun residual : ProgramPPrimitiveSpinCMatterFiniteCoefficients ↦
        residual mode) hResidual
    have hApply' :
        globalCandidateAMatterFiniteSpectralResidual period hPeriod
          massSquared core mode = 0 := by
      simpa using hApply
    rw [globalCandidateAMatterFiniteSpectralResidual_apply] at hApply'
    change ((programPPrimitiveSpinCMatterHessianWeight period hPeriod
      massSquared mode : Real) : Complex) * coefficients mode = 0 at hApply'
    have hWeightComplex :
        ((programPPrimitiveSpinCMatterHessianWeight period hPeriod
          massSquared mode : Real) : Complex) = 0 :=
      (mul_eq_zero.mp hApply').resolve_right hCoefficient
    change programPPrimitiveSpinCMatterHessianWeight period hPeriod
      massSquared mode = 0
    exact Complex.ofReal_eq_zero.mp hWeightComplex
  · intro hSupport
    apply Finsupp.ext
    intro mode
    rw [globalCandidateAMatterFiniteSpectralResidual_apply]
    by_cases hCoefficient : coefficients mode = 0
    · dsimp [coefficients] at hCoefficient
      simp [hCoefficient]
    · have hWeight : programPPrimitiveSpinCMatterHessianWeight period
          hPeriod massSquared mode = 0 :=
        hSupport (Finsupp.mem_support_iff.mpr hCoefficient)
      simp [hWeight]

/-- Descended criticality is support on the exact spectral mass shell. -/
theorem globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_spectralSupport
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    (globalCandidateAMatterFiniteGraphVariationalAtlas period hPeriod data
        measure).IsEulerCritical period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) ↔
      ((↑((globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod
        couplings.matterMassSquared).symm core).support :
          Set ProgramPPrimitiveSpinCMatterMode) ⊆
        globalCandidateAMatterFiniteSpectralMassShell period hPeriod
          couplings.matterMassSquared) := by
  rw [globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_spectralResidual
    period hPeriod data measure core]
  exact globalCandidateAMatterFiniteSpectralResidual_eq_zero_iff_support
    period hPeriod couplings.matterMassSquared core

/-- Off resonance, the explicit spectral residual has trivial kernel. -/
theorem globalCandidateAMatterFiniteSpectralResidual_eq_zero_iff_core_eq_zero
    (massSquared : Real)
    (hNonresonant : ∀ mode, programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared mode ≠ 0)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteSpectralResidual period hPeriod massSquared
        core = 0 ↔ core = 0 := by
  constructor
  · intro hResidual
    have hCoefficients :
        (globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod
          massSquared).symm core = 0 := by
      apply Finsupp.ext
      intro mode
      have hApply := congrArg
        (fun residual : ProgramPPrimitiveSpinCMatterFiniteCoefficients ↦
          residual mode) hResidual
      rw [globalCandidateAMatterFiniteSpectralResidual_apply] at hApply
      exact (mul_eq_zero.mp hApply).resolve_left
        (Complex.ofReal_ne_zero.mpr (hNonresonant mode))
    have hCore := congrArg
      (globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod massSquared)
      hCoefficients
    simpa using hCore
  · intro hCore
    subst core
    simp [globalCandidateAMatterFiniteSpectralResidual]

/-- Consequently, the finite SpinC atlas has a unique critical core off
resonance. -/
theorem globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_core_eq_zero_of_nonresonant
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hNonresonant : ∀ mode, programPPrimitiveSpinCMatterHessianWeight
      period hPeriod couplings.matterMassSquared mode ≠ 0)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    (globalCandidateAMatterFiniteGraphVariationalAtlas period hPeriod data
        measure).IsEulerCritical period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) ↔ core = 0 := by
  rw [globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_spectralResidual
    period hPeriod data measure core]
  exact
    globalCandidateAMatterFiniteSpectralResidual_eq_zero_iff_core_eq_zero
      period hPeriod couplings.matterMassSquared hNonresonant core

/-- A single resonant mode gives an explicit finite graph core. -/
def globalCandidateAMatterFiniteResonantCore
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared :=
  globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod massSquared
    (Finsupp.single mode 1)

theorem globalCandidateAMatterFiniteResonantCore_ne_zero
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    globalCandidateAMatterFiniteResonantCore period hPeriod massSquared mode ≠
      0 := by
  intro hZero
  have hCoefficients := congrArg
    (globalCandidateAMatterFiniteGraphCoreEquiv period hPeriod
      massSquared).symm hZero
  have hMode := congrArg
    (fun coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients ↦
      coefficients mode) hCoefficients
  simp [globalCandidateAMatterFiniteResonantCore] at hMode

theorem globalCandidateAMatterFiniteResonantCore_residual_eq_zero
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode)
    (hResonant : programPPrimitiveSpinCMatterHessianWeight period hPeriod
      massSquared mode = 0) :
    globalCandidateAMatterFiniteSpectralResidual period hPeriod massSquared
      (globalCandidateAMatterFiniteResonantCore period hPeriod massSquared
        mode) = 0 := by
  apply Finsupp.ext
  intro other
  rw [globalCandidateAMatterFiniteSpectralResidual_apply]
  by_cases hOther : other = mode
  · subst other
    simp [hResonant]
  · simp [globalCandidateAMatterFiniteResonantCore, hOther]

/-- A resonant mode produces a nonzero descended critical point. -/
theorem globalCandidateAMatterFiniteGraphAtlas_has_nonzero_critical_of_resonant
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (mode : ProgramPPrimitiveSpinCMatterMode)
    (hResonant : programPPrimitiveSpinCMatterHessianWeight period hPeriod
      couplings.matterMassSquared mode = 0) :
    let core := globalCandidateAMatterFiniteResonantCore period hPeriod
      couplings.matterMassSquared mode
    core ≠ 0 ∧
      (globalCandidateAMatterFiniteGraphVariationalAtlas period hPeriod data
          measure).IsEulerCritical period hPeriod
        (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
          configuration couplings.matterMassSquared core) := by
  dsimp
  refine ⟨globalCandidateAMatterFiniteResonantCore_ne_zero period hPeriod
    couplings.matterMassSquared mode, ?_⟩
  rw [globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_spectralResidual
    period hPeriod data measure]
  exact globalCandidateAMatterFiniteResonantCore_residual_eq_zero period hPeriod
    couplings.matterMassSquared mode hResonant

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralKernel4D
end JanusFormal
