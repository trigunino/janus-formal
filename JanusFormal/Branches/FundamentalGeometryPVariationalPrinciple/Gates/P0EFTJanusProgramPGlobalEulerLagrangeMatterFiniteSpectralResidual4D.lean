import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteContinuousResidual4D

/-!
# Explicit finite SpinC spectral residual

On the finite graph core, the strong residual is the diagonal coefficient
family `(2D + m²)c`.  Its ambient real inner-product pairing represents the
exact Euler covector and separates coefficients without an analytic input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralResidual4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

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

/-- Explicit diagonal strong residual on finite SpinC coefficients. -/
def globalCandidateAMatterFiniteSpectralResidual
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
  programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared
    ((globalCandidateAMatterFiniteGraphCoreEquiv
      period hPeriod massSquared).symm core)

/-- Pair a spectral residual with a finite graph test through the canonical
coefficient embedding into the ambient Hilbert space. -/
def globalCandidateAMatterFiniteSpectralResidualPairing
    (massSquared : Real)
    (residual : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (direction : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) : Real :=
  inner Real
    (programPPrimitiveSpinCMatterFiniteHilbertEmbedding
      ((globalCandidateAMatterFiniteGraphCoreEquiv
        period hPeriod massSquared).symm direction))
    (programPPrimitiveSpinCMatterFiniteHilbertEmbedding residual)

/-- The exact finite graph Euler covector is represented by the explicit
diagonal spectral residual. -/
theorem globalCandidateAMatterFiniteGraphHessian_eq_spectralResidualPairing
    (massSquared : Real)
    (core direction : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared core direction =
      globalCandidateAMatterFiniteSpectralResidualPairing period hPeriod
        massSquared
          (globalCandidateAMatterFiniteSpectralResidual period hPeriod
            massSquared core)
          direction := by
  rw [globalCandidateAMatterFiniteGraphHessian_apply]
  rw [programPPrimitiveSpinCMatterGraphForm_comm,
    programPPrimitiveSpinCMatterGraphForm_apply]
  rw [globalCandidateAMatterFiniteGraphInclusion_apply,
    globalCandidateAMatterFiniteGraphInclusion_apply]
  have hDirection := globalCandidateAMatterFiniteGraphCoreEquiv_symm_graph
    period hPeriod massSquared direction
  have hCore := globalCandidateAMatterFiniteGraphCoreEquiv_symm_graph
    period hPeriod massSquared core
  change inner Real
      (globalCandidateAMatterFiniteGraphCoreValue period hPeriod massSquared
        direction).1.1
      (globalCandidateAMatterFiniteGraphCoreValue period hPeriod massSquared
        core).1.2 = _
  rw [← hDirection, ← hCore]
  rfl

/-- The explicit spectral residual and pairing instantiate the separating
residual interface. -/
def globalCandidateAMatterFiniteSpectralResidualRepresentation
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared core).toLinearMap where
  Residual := ProgramPPrimitiveSpinCMatterFiniteCoefficients
  zeroResidual := 0
  residual := globalCandidateAMatterFiniteSpectralResidual
    period hPeriod massSquared core
  pairing := globalCandidateAMatterFiniteSpectralResidualPairing
    period hPeriod massSquared
  represents := globalCandidateAMatterFiniteGraphHessian_eq_spectralResidualPairing
    period hPeriod massSquared core
  separates := by
    constructor
    · intro hPairing
      let residual := globalCandidateAMatterFiniteSpectralResidual
        period hPeriod massSquared core
      let direction := globalCandidateAMatterFiniteGraphCoreEquiv
        period hPeriod massSquared residual
      have hSelf := hPairing direction
      change inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding
          ((globalCandidateAMatterFiniteGraphCoreEquiv
            period hPeriod massSquared).symm direction))
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding residual) = 0
        at hSelf
      rw [show (globalCandidateAMatterFiniteGraphCoreEquiv
          period hPeriod massSquared).symm direction = residual by
        exact (globalCandidateAMatterFiniteGraphCoreEquiv
          period hPeriod massSquared).symm_apply_apply residual] at hSelf
      have hEmbedding :
          programPPrimitiveSpinCMatterFiniteHilbertEmbedding residual = 0 :=
        inner_self_eq_zero.mp hSelf
      apply Finsupp.ext
      intro mode
      have hMode := congrArg
        (fun value : ProgramPPrimitiveSpinCMatterHilbert ↦ value mode)
        hEmbedding
      simpa [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
        using hMode
    · intro hResidual direction
      rw [hResidual]
      simp [globalCandidateAMatterFiniteSpectralResidualPairing]

/-- The true finite-chart Euler equation is exactly the explicit diagonal
coefficient equation. -/
theorem globalCandidateAMatterFiniteGraphEuler_eq_zero_iff_spectralResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core = 0 ↔
      globalCandidateAMatterFiniteSpectralResidual period hPeriod
        couplings.matterMassSquared core = 0 := by
  rw [globalCandidateAMatterFiniteGraph_euler_eq period hPeriod data measure
    core]
  constructor
  · intro hEuler
    apply (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).separates.mp
    intro direction
    rw [← (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).represents direction]
    rw [hEuler]
    rfl
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro direction
    rw [globalCandidateAMatterFiniteGraphHessian_eq_spectralResidualPairing]
    exact (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).separates.mpr
        hResidual direction

/-- Descended criticality of the concrete finite SpinC atlas is the explicit
mode equation `(2D + m²)c = 0`. -/
theorem globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_spectralResidual
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
      globalCandidateAMatterFiniteSpectralResidual period hPeriod
        couplings.matterMassSquared core = 0 := by
  rw [globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff period hPeriod
    data measure core]
  constructor
  · intro hEuler
    apply (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).separates.mp
    intro direction
    rw [← (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).represents direction]
    rw [hEuler]
    rfl
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro direction
    rw [globalCandidateAMatterFiniteGraphHessian_eq_spectralResidualPairing]
    exact (globalCandidateAMatterFiniteSpectralResidualRepresentation
      period hPeriod couplings.matterMassSquared core).separates.mpr
        hResidual direction

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralResidual4D
end JanusFormal
