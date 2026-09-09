import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D

/-!
# T05 finite-core support for the maximal SpinC `L²` realization

Gate 842 isolates a full isometric realization of the completed coefficient
Hilbert space in measurable spacetime `L²`.  The finite signed-mode embedding
already has dense range.  Therefore it is enough to construct a linear `L²`
representative on that algebraic core, prove its exact norm, and identify its
representative almost everywhere.

This module performs the extension from those finite-core data.  It does not
assert that the still-missing finite-core measurable realization exists.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance spinCMatterFiniteCoreLpMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterFiniteCoreLpBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterFiniteCoreLpFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The remaining support needed only on the algebraic finite signed-mode
core.  `norm_eq` is measured against its canonical dense embedding in the
completed coefficient Hilbert space. -/
structure ProgramPT05SpinCMatterFiniteCoreLpSupport where
  coreToLp :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      Lp ProgramPT05SpinCMatterPointwiseFiber 2
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  norm_eq :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      ‖coreToLp coefficients‖ =
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖
  coeFn_ae :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      ⇑(coreToLp coefficients) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
          programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
            coefficients

/-- The canonical finite coefficient embedding has dense range as a map. -/
theorem programPT05SpinCMatterFiniteHilbertEmbedding_denseRange :
    DenseRange
      (programPPrimitiveSpinCMatterFiniteHilbertEmbedding :
        ProgramPPrimitiveSpinCMatterFiniteCoefficients →
          ProgramPPrimitiveSpinCMatterHilbert) := by
  change Dense
    (Set.range
      (programPPrimitiveSpinCMatterFiniteHilbertEmbedding :
        ProgramPPrimitiveSpinCMatterFiniteCoefficients →
          ProgramPPrimitiveSpinCMatterHilbert))
  rw [← LinearMap.coe_range]
  exact programPPrimitiveSpinCMatterFiniteHilbertEmbedding_range_dense

/-- Exact norm preservation on the core supplies the bound required by
`LinearMap.extendOfNorm`. -/
theorem ProgramPT05SpinCMatterFiniteCoreLpSupport.norm_bound
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod) :
    ∃ constant : Real,
      ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
        ‖support.coreToLp coefficients‖ ≤
          constant *
            ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ := by
  refine ⟨1, ?_⟩
  intro coefficients
  rw [support.norm_eq]
  simp

/-- Continuous extension of the finite-core realization to the whole
coefficient Hilbert space. -/
def programPT05SpinCMatterFiniteCoreLpContinuousExtension
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod) :
    ProgramPPrimitiveSpinCMatterHilbert →L[Complex]
      Lp ProgramPT05SpinCMatterPointwiseFiber 2
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  LinearMap.extendOfNorm
    (𝕜 := Complex) (𝕜₂ := Complex) (σ₁₂ := RingHom.id Complex)
    (E := ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (Eₗ := ProgramPPrimitiveSpinCMatterHilbert)
    (F := Lp ProgramPT05SpinCMatterPointwiseFiber 2
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    support.coreToLp programPPrimitiveSpinCMatterFiniteHilbertEmbedding

/-- The continuous extension agrees exactly with the supplied finite-core
map. -/
@[simp]
theorem programPT05SpinCMatterFiniteCoreLpContinuousExtension_apply
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreLpContinuousExtension period hPeriod
        support
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients) =
      support.coreToLp coefficients := by
  unfold programPT05SpinCMatterFiniteCoreLpContinuousExtension
  exact LinearMap.extendOfNorm_eq
    (programPT05SpinCMatterFiniteHilbertEmbedding_denseRange)
    support.norm_bound coefficients

/-- Norm preservation extends from the dense core to every completed
coefficient state. -/
theorem programPT05SpinCMatterFiniteCoreLpContinuousExtension_norm
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod)
    (state : ProgramPPrimitiveSpinCMatterHilbert) :
    ‖programPT05SpinCMatterFiniteCoreLpContinuousExtension period hPeriod
        support state‖ = ‖state‖ := by
  refine DenseRange.induction_on
    (programPT05SpinCMatterFiniteHilbertEmbedding_denseRange) state
    (isClosed_eq
      (continuous_norm.comp
        (programPT05SpinCMatterFiniteCoreLpContinuousExtension period hPeriod
          support).continuous)
      continuous_norm) ?_
  intro coefficients
  rw [programPT05SpinCMatterFiniteCoreLpContinuousExtension_apply,
    support.norm_eq]

/-- The dense extension bundled as a complex-linear isometry. -/
def programPT05SpinCMatterFiniteCoreLpLinearIsometry
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod) :
    ProgramPPrimitiveSpinCMatterHilbert →ₗᵢ[Complex]
      Lp ProgramPT05SpinCMatterPointwiseFiber 2
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toLinearMap :=
    (programPT05SpinCMatterFiniteCoreLpContinuousExtension period hPeriod
      support).toLinearMap
  norm_map' :=
    programPT05SpinCMatterFiniteCoreLpContinuousExtension_norm period hPeriod
      support

/-- The bundled isometry retains the prescribed finite-core values. -/
@[simp]
theorem programPT05SpinCMatterFiniteCoreLpLinearIsometry_apply
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreLpLinearIsometry period hPeriod support
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients) =
      support.coreToLp coefficients :=
  programPT05SpinCMatterFiniteCoreLpContinuousExtension_apply period hPeriod
    support coefficients

/-- Finite-core support promotes canonically to Gate 842's full extension
datum. -/
def ProgramPT05SpinCMatterFiniteCoreLpSupport.toLpExtension
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod) :
    ProgramPT05SpinCMatterLpExtension period hPeriod where
  toLp :=
    programPT05SpinCMatterFiniteCoreLpLinearIsometry period hPeriod support
  finiteCore_ae := by
    intro coefficients
    rw [programPT05SpinCMatterFiniteCoreLpLinearIsometry_apply]
    exact support.coeFn_ae coefficients

/-- Consequently, finite-core support suffices for the conditional maximal
`L¹` density statement at the Gate-828 frontier. -/
theorem programPT05BulkSpinCFrontier_exists_maximalLpLocalDensity_of_finiteCore
    (support : ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) :
    ∃ density :
        Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod),
      (∫ base, density base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        programPT05BulkSpinCFrontierAction period hPeriod couplings
          frontier :=
  programPT05BulkSpinCFrontier_exists_maximalLpLocalDensity period hPeriod
    support.toLpExtension couplings frontier

end
end P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D
end JanusFormal
