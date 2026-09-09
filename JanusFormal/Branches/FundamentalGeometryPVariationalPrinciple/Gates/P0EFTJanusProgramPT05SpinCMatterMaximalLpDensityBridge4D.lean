import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Function.L2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterMaximalSpectralDensity4D

/-!
# T05 maximal SpinC measurable-density reduction

The geometric SpinC Hilbert space is an abstract completion of smooth bundle
sections.  The current API contains no almost-everywhere representative of a
completed section.  In particular, local smooth trivializations do not yet
give a measurable global map into a fixed finite-dimensional fiber.

This module isolates that missing step as one linear-isometric `L²`
realization, required to agree almost everywhere with the explicit fiber
coordinates on the finite smooth core.  From that datum alone, the `L²`
Hölder theorem gives an honest `L¹` spacetime density for every maximal graph
state, and its integral is exactly the closed-graph action.  No existence of
the missing realization is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance spinCMatterMaximalLpMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterMaximalLpBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterMaximalLpFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance spinCMatterMaximalLpHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- A fixed Euclidean coordinate fiber containing both physical sectors,
both doubled SpinC summands, and both complex half-spinor coordinates. -/
abbrev ProgramPT05SpinCMatterPointwiseFiber :=
  EuclideanSpace Complex (Sector × (Fin 2 × Fin 2))

/-- Fixed Euclidean coordinates of a pair of doubled matter fibers. -/
def programPT05SpinCMatterPointwiseCoordinates
    (field : Sector → D9DoubledMatterFiber) :
    ProgramPT05SpinCMatterPointwiseFiber :=
  WithLp.toLp 2 fun index =>
    if index.2.1 = (0 : Fin 2) then
      matterFiberHalfSpinorLinearEquiv (field index.1).1 index.2.2
    else
      matterFiberHalfSpinorLinearEquiv (field index.1).2 index.2.2

/-- The Euclidean coordinate inner product is the sum of the two intrinsic
doubled-fiber Hermitian pairings. -/
theorem programPT05SpinCMatterPointwiseCoordinates_inner
    (first second : Sector → D9DoubledMatterFiber) :
    inner Complex
        (programPT05SpinCMatterPointwiseCoordinates first)
        (programPT05SpinCMatterPointwiseCoordinates second) =
      ∑ sector : Sector,
        d9DoubledMatterSpinorHermitianPairing
          (first sector) (second sector) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  unfold d9DoubledMatterSpinorHermitianPairing
  apply Finset.sum_congr rfl
  intro sector _
  rw [Fintype.sum_prod_type]
  simp [programPT05SpinCMatterPointwiseCoordinates,
    d9MatterSpinorHermitianPairing_eq_two_coordinates,
    RCLike.inner_apply, Fin.sum_univ_succ] ;
    ring

/-- Explicit finite-core coordinate representative on the throat. -/
def programPT05SpinCMatterFiniteCorePointwiseCoordinates
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    ProgramPT05SpinCMatterPointwiseFiber :=
  programPT05SpinCMatterPointwiseCoordinates fun sector =>
    show D9DoubledMatterFiber from
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        coefficients sector base

/-- The exact missing analytic datum.  Its isometry fixes the completed `L²`
norm, while `finiteCore_ae` fixes the measurable representative rather than
allowing an unrelated abstract Hilbert embedding. -/
structure ProgramPT05SpinCMatterLpExtension where
  toLp :
    ProgramPPrimitiveSpinCMatterHilbert →ₗᵢ[Complex]
      Lp ProgramPT05SpinCMatterPointwiseFiber 2
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  finiteCore_ae :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      ⇑(toLp (programPPrimitiveSpinCMatterFiniteHilbertEmbedding
        coefficients)) =ᵐ[intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients

/-- The extension realizes the explicit finite smooth core: its pointwise
`L²` pairing agrees almost everywhere with the fixed-coordinate pairing. -/
theorem programPT05SpinCMatterFiniteCoreLpPairing_ae
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (fun base =>
      inner Complex
        (realization.toLp
          (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first) base)
        (realization.toLp
          (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) base))
      =ᵐ[intrinsicCanonicalThroatVolumeMeasure period hPeriod]
    fun base =>
      inner Complex
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base) := by
  filter_upwards [realization.finiteCore_ae first,
    realization.finiteCore_ae second] with base hFirst hSecond
  rw [hFirst, hSecond]

/-- Pointwise real action density obtained from the two `L²` graph
components. -/
def programPT05SpinCMatterMaximalLpLocalDensity
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) : EffectiveThroat period hPeriod → Real :=
  fun base =>
    (1 / 2 : Real) *
      (inner Complex
        (realization.toLp state.1.1 base)
        (realization.toLp state.1.2 base)).re

/-- Hölder's theorem makes the maximal spacetime density integrable. -/
theorem programPT05SpinCMatterMaximalLpLocalDensity_integrable
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    Integrable
      (programPT05SpinCMatterMaximalLpLocalDensity period hPeriod
        realization massSquared state)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hPair : Integrable
      (fun base => inner Complex
        (realization.toLp state.1.1 base)
        (realization.toLp state.1.2 base))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    L2.integrable_inner (𝕜 := Complex)
      (realization.toLp state.1.1) (realization.toLp state.1.2)
  unfold programPT05SpinCMatterMaximalLpLocalDensity
  exact hPair.re.const_mul (1 / 2 : Real)

/-- The maximal density as an actual equivalence class in spacetime `L¹`. -/
def programPT05SpinCMatterMaximalLpLocalDensityL1
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (programPT05SpinCMatterMaximalLpLocalDensity_integrable period hPeriod
    realization massSquared state).toL1
      (programPT05SpinCMatterMaximalLpLocalDensity period hPeriod realization
        massSquared state)

/-- The `L¹` class has the advertised pointwise representative almost
everywhere. -/
theorem programPT05SpinCMatterMaximalLpLocalDensityL1_coeFn
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    ⇑(programPT05SpinCMatterMaximalLpLocalDensityL1 period hPeriod
        realization massSquared state) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      programPT05SpinCMatterMaximalLpLocalDensity period hPeriod realization
        massSquared state :=
  Integrable.coeFn_toL1
    (programPT05SpinCMatterMaximalLpLocalDensity_integrable period hPeriod
      realization massSquared state)

/-- Integrating the maximal a.e. spacetime density gives the exact graph
action. -/
theorem programPT05SpinCMatterMaximalLpLocalDensity_integral_eq_graphAction
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (∫ base,
      programPT05SpinCMatterMaximalLpLocalDensity period hPeriod realization
        massSquared state base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
  let first := realization.toLp state.1.1
  let second := realization.toLp state.1.2
  have hPair : Integrable (fun base => inner Complex (first base) (second base))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    L2.integrable_inner (𝕜 := Complex) first second
  calc
    (∫ base,
        programPT05SpinCMatterMaximalLpLocalDensity period hPeriod realization
          massSquared state base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        (1 / 2 : Real) *
          ∫ base, (inner Complex (first base) (second base)).re
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      change (∫ base, (1 / 2 : Real) *
        (inner Complex (first base) (second base)).re
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = _
      rw [integral_const_mul]
    _ = (1 / 2 : Real) *
        (∫ base, inner Complex (first base) (second base)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)).re := by
      exact congrArg (fun value : Real => (1 / 2 : Real) * value)
        (integral_re hPair)
    _ = (1 / 2 : Real) * (inner Complex first second).re := by
      rw [L2.inner_def]
    _ = (1 / 2 : Real) *
        (inner Complex state.1.1 state.1.2).re := by
      change (1 / 2 : Real) *
        (inner Complex (realization.toLp state.1.1)
          (realization.toLp state.1.2)).re = _
      rw [realization.toLp.inner_map_map]
    _ = programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
      rw [programPPrimitiveSpinCMatterGraphAction,
        programPPrimitiveSpinCMatterGraphForm_apply,
        real_inner_eq_re_inner]
      rfl

/-- The selected `L¹` representative itself integrates to the graph action. -/
theorem programPT05SpinCMatterMaximalLpLocalDensityL1_integral_eq_graphAction
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (∫ base,
      programPT05SpinCMatterMaximalLpLocalDensityL1 period hPeriod realization
        massSquared state base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
  rw [integral_congr_ae
    (programPT05SpinCMatterMaximalLpLocalDensityL1_coeFn period hPeriod
      realization massSquared state)]
  exact programPT05SpinCMatterMaximalLpLocalDensity_integral_eq_graphAction
    period hPeriod realization massSquared state

/-- Gate 828 receives a genuine maximal `L¹` density as soon as the isolated
extension obligation is supplied. -/
theorem programPT05BulkSpinCFrontier_exists_maximalLpLocalDensity
    (realization : ProgramPT05SpinCMatterLpExtension period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) :
    ∃ density :
        Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod),
      (∫ base, density base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        programPT05BulkSpinCFrontierAction period hPeriod couplings
          frontier := by
  refine ⟨programPT05SpinCMatterMaximalLpLocalDensityL1 period hPeriod
    realization couplings.matterMassSquared frontier.graphState, ?_⟩
  exact programPT05SpinCMatterMaximalLpLocalDensityL1_integral_eq_graphAction
    period hPeriod realization couplings.matterMassSquared frontier.graphState

end
end P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D
end JanusFormal
