import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

/-!
# Smooth primitive SpinC realization in the maximal matter graph

A smooth primitive SpinC field belongs to the maximal graph of `2D + m²` once
its Fourier--monopole coefficients and their Hessian-weighted coefficients are
both square summable.  This file records exactly that spectral-decay datum and
constructs the graph vector, its linearity, finite-core compatibility, action
agreement, and injectivity.

The remaining SpinC theorem is therefore the analytic statement that the
existing geometric Fourier transform of every smooth section satisfies the
weighted `ℓ²` condition.  No graph vector is selected independently of those
coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set
open scoped ENNReal lp LinearPMap InnerProductSpace
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MatterSmooth :=
  ProgramPPrimitiveSpinCMatterSmoothField period hPeriod

private abbrev MatterHilbert :=
  ProgramPPrimitiveSpinCMatterHilbert

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real MatterHilbert :=
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

/-- Spectral data of every smooth two-sector primitive SpinC field.  The
weighted map is required to be the exact multiplier `2D + m²`, not an
independent image. -/
structure ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
    (massSquared : Real) where
  coefficients : MatterSmooth period hPeriod →ₗ[Complex] MatterHilbert
  weightedCoefficients :
    MatterSmooth period hPeriod →ₗ[Complex] MatterHilbert
  weighted_relation : ∀ field mode,
    weightedCoefficients field mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) * coefficients field mode
  finite_coefficients :
    ∀ finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      coefficients
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            finite) =
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding finite
  finite_weightedCoefficients :
    ∀ finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      weightedCoefficients
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            finite) =
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding
          (programPPrimitiveSpinCMatterFiniteHessian period hPeriod
            massSquared finite)
  smoothAction_eq_pairing : ∀ field,
    programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared field =
      (1 / 2 : Real) *
        inner Real (coefficients field) (weightedCoefficients field)
  coefficients_injective : Function.Injective coefficients

/-- The exact maximal graph vector associated with one smooth primitive field. -/
def programPPrimitiveSpinCMatterSmoothSpectralGraph
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared)
    (field : MatterSmooth period hPeriod) :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared := by
  let weight :=
    programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
  let state : MatterHilbert := spectral.coefficients field
  let image : MatterHilbert := spectral.weightedCoefficients field
  have hRelation : ∀ mode,
      image mode = ((weight mode : Real) : Complex) * state mode :=
    spectral.weighted_relation field
  let domainState :
      (complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode weight).domain :=
    ⟨state, ⟨image, hRelation⟩⟩
  refine ⟨(state, image), ?_⟩
  apply (LinearPMap.mem_graph_iff
    (complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode weight)).2
  refine ⟨domainState, rfl, ?_⟩
  ext mode
  rw [complexDiagonalOperator_apply]
  exact (hRelation mode).symm

@[simp]
theorem programPPrimitiveSpinCMatterSmoothSpectralGraph_fst
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared)
    (field : MatterSmooth period hPeriod) :
    (programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod massSquared
      spectral field).1.1 = spectral.coefficients field :=
  rfl

@[simp]
theorem programPPrimitiveSpinCMatterSmoothSpectralGraph_snd
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared)
    (field : MatterSmooth period hPeriod) :
    (programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod massSquared
      spectral field).1.2 = spectral.weightedCoefficients field :=
  rfl

/-- Complex-linear smooth-to-graph realization. -/
def programPPrimitiveSpinCMatterSmoothSpectralGraphLinearMap
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared) :
    MatterSmooth period hPeriod →ₗ[Complex]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared where
  toFun := programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod
    massSquared spectral
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext
    · exact spectral.coefficients.map_add first second
    · exact spectral.weightedCoefficients.map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    apply Prod.ext
    · exact spectral.coefficients.map_smul scalar field
    · exact spectral.weightedCoefficients.map_smul scalar field

/-- Real-linear restriction used by the variational chart. -/
def programPPrimitiveSpinCMatterSmoothSpectralGraphRealLinearMap
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared) :
    MatterSmooth period hPeriod →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared where
  toFun := programPPrimitiveSpinCMatterSmoothSpectralGraphLinearMap period
    hPeriod massSquared spectral
  map_add' first second :=
    (programPPrimitiveSpinCMatterSmoothSpectralGraphLinearMap period hPeriod
      massSquared spectral).map_add first second
  map_smul' scalar field := by
    have hScalar :
        scalar • field = (scalar : Complex) • field := by
      funext sector
      change scalar • field sector = (scalar : Complex) • field sector
      rw [d9PrimitiveSpinCGeometricL2_complex_smul,
        d9PrimitiveSpinCComplexScalarSection_ofReal]
    rw [hScalar, map_smul]
    exact (RCLike.real_smul_eq_coe_smul
      (K := Complex) scalar
      (programPPrimitiveSpinCMatterSmoothSpectralGraphLinearMap period hPeriod
        massSquared spectral field)).symm

/-- The spectral construction agrees exactly with the pre-existing finite
graph insertion. -/
theorem programPPrimitiveSpinCMatterSmoothSpectralGraph_finite
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared)
    (finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod massSquared
        spectral
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          finite) =
      programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
        finite := by
  apply Subtype.ext
  apply Prod.ext
  · exact spectral.finite_coefficients finite
  · exact spectral.finite_weightedCoefficients finite

/-- The graph action is the independently defined smooth primitive action. -/
theorem programPPrimitiveSpinCMatterSmoothSpectralGraph_action
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared)
    (field : MatterSmooth period hPeriod) :
    programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        (programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod
          massSquared spectral field) =
      programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared
        field := by
  rw [programPPrimitiveSpinCMatterGraphAction,
    programPPrimitiveSpinCMatterGraphForm_apply,
    programPPrimitiveSpinCMatterSmoothSpectralGraph_fst,
    programPPrimitiveSpinCMatterSmoothSpectralGraph_snd]
  exact (spectral.smoothAction_eq_pairing field).symm

/-- Injectivity follows already from the unweighted Fourier coefficient map. -/
theorem programPPrimitiveSpinCMatterSmoothSpectralGraph_injective
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared) :
    Function.Injective
      (programPPrimitiveSpinCMatterSmoothSpectralGraphRealLinearMap period
        hPeriod massSquared spectral) := by
  intro first second hEqual
  apply spectral.coefficients_injective
  have hFirst := congrArg (fun state => state.1.1) hEqual
  change
    (programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod massSquared
      spectral first).1.1 =
    (programPPrimitiveSpinCMatterSmoothSpectralGraph period hPeriod massSquared
      spectral second).1.1 at hFirst
  rw [programPPrimitiveSpinCMatterSmoothSpectralGraph_fst,
    programPPrimitiveSpinCMatterSmoothSpectralGraph_fst] at hFirst
  exact hFirst

/-- The spectral-decay datum constructs the smooth graph realization expected
by the minimal physical chart. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_spectral
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod
      massSquared where
  toGraph := programPPrimitiveSpinCMatterSmoothSpectralGraphRealLinearMap period
    hPeriod massSquared spectral
  finite_compatibility := by
    intro finite
    exact programPPrimitiveSpinCMatterSmoothSpectralGraph_finite period hPeriod
      massSquared spectral finite
  action_agreement := by
    intro field
    exact programPPrimitiveSpinCMatterSmoothSpectralGraph_action period hPeriod
      massSquared spectral field
  injective := programPPrimitiveSpinCMatterSmoothSpectralGraph_injective period
    hPeriod massSquared spectral

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
end JanusFormal
