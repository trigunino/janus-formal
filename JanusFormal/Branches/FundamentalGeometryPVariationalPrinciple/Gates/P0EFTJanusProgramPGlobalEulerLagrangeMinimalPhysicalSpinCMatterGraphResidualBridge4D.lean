import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

/-!
# SpinC matter-block spectral residual in the minimal physical chart

The exact matter action identity transports the maximal SpinC graph residual
to the matter block of every minimal physical chart.  Finite graph directions
already occur in the typed diagonal core, so chart tests separate that
residual.  This does not identify the result with the complete SpinC Euler
covector: the latter is the derivative of all nine action blocks.  Their exact
difference is retained as a separate cross-block covector below.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

variable (period : Real) (hPeriod : period ≠ 0)

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

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

/-- The actual matter member of the nine-block Candidate-A action in the
minimal chart. -/
def globalCandidateAMinimalPhysicalMatterBlockAction :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model → Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  (globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod (0 : chart.Model)
      chart.zero_mem_domain) measure).matter

/-- The chart matter block is exactly the constant spectator plus the
primitive SpinC graph action. -/
theorem globalCandidateAMinimalPhysicalMatterBlockAction_eq_graph :
    globalCandidateAMinimalPhysicalMatterBlockAction period hPeriod
        configuration data analysis chartData =
      fun state =>
        (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
          configuration data analysis chartData).matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
            hPeriod configuration data analysis chartData).matterProjection
              state) := by
  exact
    (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).matterAction_eq

/-- Frechet Euler covector of the matter block alone. -/
noncomputable def globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalMatterBlockAction period hPeriod
      configuration data analysis chartData) point

/-- The matter-block Euler covector is the pullback of the exact graph form
at every chart point. -/
theorem globalCandidateAMinimalPhysicalMatterBlockEulerCovector_eq_graph
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared
        ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
          hPeriod configuration data analysis chartData).matterProjection
            point)).comp
        (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
          configuration data analysis chartData).matterProjection := by
  unfold globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt
  rw [globalCandidateAMinimalPhysicalMatterBlockAction_eq_graph period hPeriod
    configuration data analysis chartData]
  let bridge := globalCandidateAMinimalPhysicalQuadraticChartBridge period
    hPeriod configuration data analysis chartData
  have hGraph :=
    programPPrimitiveSpinCMatterGraphAction_hasFDerivAt period hPeriod
      couplings.matterMassSquared (bridge.matterProjection point)
  exact
    ((hGraph.comp point bridge.matterProjection.hasFDerivAt).const_add
      bridge.matterConstant).fderiv

/-- Pair an ambient maximal spectral residual with a chart direction through
the canonical matter projection. -/
def globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing
    (residual : ProgramPPrimitiveSpinCMatterHilbert)
    (direction : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) : Real :=
  programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing period
    hPeriod couplings.matterMassSquared residual
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection direction)

/-- The maximal spectral residual represents the exact matter-block Euler
covector after pullback to the minimal chart. -/
theorem globalCandidateAMinimalPhysicalMatterBlockEuler_eq_spectralResidualPairing
    (point direction :
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point direction =
      globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing period
        hPeriod configuration data analysis chartData
          (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period
            hPeriod couplings.matterMassSquared
              ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
                hPeriod configuration data analysis
                  chartData).matterProjection point)) direction := by
  rw [globalCandidateAMinimalPhysicalMatterBlockEulerCovector_eq_graph period
    hPeriod configuration data analysis chartData point]
  exact programPPrimitiveSpinCMatterGraphForm_eq_maximalResidualPairing period
    hPeriod couplings.matterMassSquared
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection point)
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection direction)

/-- Typed diagonal-core chart directions separate every ambient SpinC
spectral residual. -/
theorem globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing_separates
    (residual : ProgramPPrimitiveSpinCMatterHilbert) :
    (∀ direction :
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).Model,
      globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing period
        hPeriod configuration data analysis chartData residual direction = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    ext mode
    let coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
      Finsupp.single mode (residual mode)
    let core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis :=
      (0, (0, (coefficients, 0)))
    let bridge := globalCandidateAMinimalPhysicalQuadraticChartBridge period
      hPeriod configuration data analysis chartData
    let direction := bridge.chartBridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core)
    have hMode := hPairing direction
    have hProjection :
        bridge.matterProjection direction =
          programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared coefficients := by
      simpa [direction] using bridge.matterProjection_core core
    change programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
      period hPeriod couplings.matterMassSquared residual
        (bridge.matterProjection direction) = 0 at hMode
    rw [hProjection] at hMode
    change inner Real
      (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)
      residual = 0 at hMode
    have hSingle :
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients =
          (lp.single 2 mode (residual mode) :
            ProgramPPrimitiveSpinCMatterHilbert) := by
      ext other
      rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
      change (Finsupp.single mode (residual mode)) other =
        (lp.single 2 mode (residual mode) :
          ProgramPPrimitiveSpinCMatterHilbert) other
      by_cases hOther : other = mode
      · subst other
        simp
      · rw [Finsupp.single_eq_of_ne hOther]
        simp [hOther]
    rw [hSingle, real_inner_eq_re_inner, lp.inner_single_left] at hMode
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re] at hMode
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hMode)
  · intro hResidual direction
    rw [hResidual]
    simp [globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing,
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing]

/-- Concrete separating representation of the matter block on the minimal
chart.  Its residual is the actual maximal spectral `2D + m²` output. -/
def globalCandidateAMinimalPhysicalMatterBlockSpectralResidualRepresentation
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point).toLinearMap where
  Residual := ProgramPPrimitiveSpinCMatterHilbert
  zeroResidual := 0
  residual := programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period
    hPeriod couplings.matterMassSquared
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection point)
  pairing :=
    globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing period
      hPeriod configuration data analysis chartData
  represents :=
    globalCandidateAMinimalPhysicalMatterBlockEuler_eq_spectralResidualPairing
      period hPeriod configuration data analysis chartData point
  separates :=
    globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing_separates
      period hPeriod configuration data analysis chartData _

/-- Matter-block stationarity is exactly vanishing of the pulled maximal
spectral residual. -/
theorem globalCandidateAMinimalPhysicalMatterBlockEuler_eq_zero_iff_spectralResidual
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ↔
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
            hPeriod configuration data analysis chartData).matterProjection
              point) = 0 := by
  let representation :=
    globalCandidateAMinimalPhysicalMatterBlockSpectralResidualRepresentation
      period hPeriod configuration data analysis chartData point
  constructor
  · intro hEuler
    apply (separatingPDEResidualRepresentation_covector_eq_zero_iff
      representation).mp
    exact congrArg ContinuousLinearMap.toLinearMap hEuler
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro direction
    have hCovector :=
      (separatingPDEResidualRepresentation_covector_eq_zero_iff
        representation).mpr hResidual
    exact LinearMap.congr_fun hCovector direction

/-- Restriction of the matter-block covector to pure primitive SpinC
directions. -/
def globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
      .positiveQuarter) →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalMatterBlockEulerCovectorAt period hPeriod
      configuration data analysis chartData point).toLinearMap.comp
    (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
      configuration data analysis chartData)

/-- Exact contribution of the other eight action blocks to the complete
SpinC component.  No vanishing of this covector is assumed. -/
def globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
      .positiveQuarter) →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
      hPeriod configuration data analysis chartData point

/-- The complete SpinC Euler covector is the spectral matter-block
contribution plus the explicit cross-block remainder. -/
theorem globalCandidateAMinimalPhysicalSpinCEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
          hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt
  abel

/-- Identification of the complete SpinC equation with the matter block is
equivalent, rather than definitionally equal, to vanishing of the cross-block
covector. -/
theorem globalCandidateAMinimalPhysicalSpinCEuler_eq_matterBlock_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
          hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D
end JanusFormal
