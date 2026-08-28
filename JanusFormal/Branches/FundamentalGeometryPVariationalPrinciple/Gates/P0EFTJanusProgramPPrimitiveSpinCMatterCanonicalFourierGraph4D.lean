import Mathlib.Analysis.Normed.Lp.PiLp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D

/-!
# Canonical two-sector Fourier coefficients for smooth primitive SpinC matter

The unweighted coefficients of a smooth primitive SpinC field are not analytic
input.  For each physical sector they are uniquely determined by the inverse
of the already proved geometric signed-mode unitary.  A finite `PiLp` curry
isometry assembles the two coefficient towers in the exact product labels
`Sector × PrimitiveSpinCGeometricSignedMode` used by the physical matter
Hessian.

The remaining spectral datum therefore contains only the weighted coefficient
vector and the statements that it is the exact `2D + m²` multiplier, agrees on
the finite Fourier core, and computes the independently integrated smooth
action.  Injectivity and the unweighted coefficient map are derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SignedMode := PrimitiveSpinCGeometricSignedMode
private abbrev OneSectorSmooth :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev MatterSmooth :=
  ProgramPPrimitiveSpinCMatterSmoothField period hPeriod
private abbrev MatterCoefficients :=
  ProgramPPrimitiveSpinCMatterHilbert

local instance signedModeDecidableEq : DecidableEq SignedMode := Classical.decEq _

local instance matterCoefficientsRealInnerProductSpace :
    InnerProductSpace Real MatterCoefficients :=
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

/-- Product labels as the sigma type required by `piLpCurry`. -/
def sectorSignedModeSigmaEquiv :
    (Σ _ : Sector, SignedMode) ≃ Sector × SignedMode where
  toFun mode := (mode.1, mode.2)
  invFun mode := ⟨mode.1, mode.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fourier coefficients of one smooth physical sector, fixed by the inverse
geometric unitary. -/
def primitiveSpinCOneSectorCanonicalFourierCoefficients :
    OneSectorSmooth period hPeriod →L[Complex]
      ComplexDiagonalHilbert SignedMode :=
  (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
    |>.toLinearIsometry.toContinuousLinearMap.comp
      (d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter)

/-- Isometric reindexing from sigma labels to the exact product labels used by
`ProgramPPrimitiveSpinCMatterMode`. -/
def primitiveSpinCMatterSectorModeReindex :
    ComplexDiagonalHilbert (Σ _ : Sector, SignedMode) ≃ₗᵢ[Complex]
      MatterCoefficients :=
  complexDiagonalHilbertCongr (Σ _ : Sector, SignedMode)
    sectorSignedModeSigmaEquiv

/-- Assemble the two one-sector coefficient towers before uncurrying. -/
def primitiveSpinCMatterCanonicalSectorCoefficients :
    MatterSmooth period hPeriod →ₗ[Complex] MatterCoefficients where
  toFun field := ⟨fun mode =>
      primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (field mode.1) mode.2, by
    change Memℓp (fun mode : Sector × SignedMode =>
      primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (field mode.1) mode.2) 2
    rw [memℓp_gen_iff (by norm_num)]
    apply (summable_prod_of_nonneg (fun _ => by positivity)).2
    constructor
    · intro sector
      exact (memℓp_gen_iff (by norm_num)).1
        (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
          (field sector)).2
    · exact summable_of_hasFiniteSupport (Set.toFinite _)⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact congrArg (fun coefficients => coefficients mode.2) (map_add
      (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod)
      (first mode.1) (second mode.1))
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    exact congrArg (fun coefficients => coefficients mode.2) (map_smul
      (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod)
      scalar (field mode.1))

/-- Canonical two-sector signed Fourier coefficient map. -/
def programPPrimitiveSpinCMatterCanonicalFourierCoefficients :
    MatterSmooth period hPeriod →ₗ[Complex] MatterCoefficients :=
  primitiveSpinCMatterCanonicalSectorCoefficients period hPeriod

@[simp]
theorem programPPrimitiveSpinCMatterCanonicalFourierCoefficients_apply
    (field : MatterSmooth period hPeriod)
    (sector : Sector) (mode : SignedMode) :
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
        field (sector, mode) =
      primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (field sector) mode := by
  rfl

/-- The canonical coefficient map is injective because geometric completion,
the signed-mode unitary and the finite-sector uncurrying are all injective. -/
theorem programPPrimitiveSpinCMatterCanonicalFourierCoefficients_injective :
    Function.Injective
      (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod) := by
  intro first second hEqual
  funext sector
  apply UniformSpace.Completion.coe_injective
  apply (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm.injective
  ext mode
  have hMode := congrArg
    (fun coefficients : MatterCoefficients => coefficients (sector, mode)) hEqual
  simpa [primitiveSpinCOneSectorCanonicalFourierCoefficients,
    d9PrimitiveSpinCGeometricL2Embedding,
    ContinuousLinearMap.comp_apply] using hMode

/-- Only the weighted Fourier vector remains analytic input.  Its pointwise
relation fixes it uniquely whenever the multiplier image is square summable. -/
structure ProgramPPrimitiveSpinCMatterCanonicalWeightedFourierData4D
    (massSquared : Real) where
  weightedCoefficients :
    MatterSmooth period hPeriod →ₗ[Complex] MatterCoefficients
  weighted_relation : ∀ field mode,
    weightedCoefficients field mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) *
        programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
          field mode
  canonical_finite_coefficients :
    ∀ finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
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
        inner Real
          (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period
            hPeriod field)
          (weightedCoefficients field)

/-- Convert the canonical weighted datum into the earlier general spectral
graph interface. -/
def programPPrimitiveSpinCMatterSmoothSpectralGraphData_of_canonical
    (massSquared : Real)
    (canonical : ProgramPPrimitiveSpinCMatterCanonicalWeightedFourierData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period hPeriod
      massSquared where
  coefficients := programPPrimitiveSpinCMatterCanonicalFourierCoefficients
    period hPeriod
  weightedCoefficients := canonical.weightedCoefficients
  weighted_relation := canonical.weighted_relation
  finite_coefficients := canonical.canonical_finite_coefficients
  finite_weightedCoefficients := canonical.finite_weightedCoefficients
  smoothAction_eq_pairing := canonical.smoothAction_eq_pairing
  coefficients_injective :=
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients_injective period
      hPeriod

/-- The canonical weighted Fourier datum constructs the exact maximal graph
realization of every smooth primitive matter field. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_canonicalFourier
    (massSquared : Real)
    (canonical : ProgramPPrimitiveSpinCMatterCanonicalWeightedFourierData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod
      massSquared :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_spectral period hPeriod
    massSquared
      (programPPrimitiveSpinCMatterSmoothSpectralGraphData_of_canonical period
        hPeriod massSquared canonical)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
end JanusFormal
