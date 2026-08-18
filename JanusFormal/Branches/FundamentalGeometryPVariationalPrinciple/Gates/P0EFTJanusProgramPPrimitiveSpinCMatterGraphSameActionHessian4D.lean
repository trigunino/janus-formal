import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Primitive SpinC matter graph action and same-action Hessian

The two physical matter sectors carry the signed primitive SpinC coefficient
operator `2D + m²`.  On its closed graph this operator is continuous into the
ambient real Hilbert space.  Its symmetric pairing therefore defines a genuine
real quadratic action whose second Frechet derivative is exactly the original
operator pairing.

This gate is coefficient-side and assumption-free.  It does not identify an
arbitrary global variational chart with the primitive SpinC graph domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The primitive SpinC signed mode, repeated once per physical sector. -/
abbrev ProgramPPrimitiveSpinCMatterMode :=
  Sector × PrimitiveSpinCGeometricSignedMode

local instance programPPrimitiveSpinCMatterModeDecidableEq :
    DecidableEq ProgramPPrimitiveSpinCMatterMode :=
  Classical.decEq _

private def finiteCoefficientEmbedding
    (Mode : Type*) [DecidableEq Mode] :
    (Mode →₀ Complex) →ₗ[Complex] ComplexDiagonalHilbert Mode :=
  Finsupp.linearCombination Complex (complexDiagonalBasis Mode)

@[simp]
private theorem finiteCoefficientEmbedding_single
    (Mode : Type*) [DecidableEq Mode]
    (mode : Mode) (coefficient : Complex) :
    finiteCoefficientEmbedding Mode (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [finiteCoefficientEmbedding, Finsupp.linearCombination_single,
    complexDiagonalBasis_eq_single]
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [lp.single_apply]
  · simp [lp.single_apply, hOther]

@[simp]
private theorem finiteCoefficientEmbedding_apply
    (Mode : Type*) [DecidableEq Mode]
    (coefficients : Mode →₀ Complex) (mode : Mode) :
    finiteCoefficientEmbedding Mode coefficients mode =
      coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [finiteCoefficientEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        finiteCoefficientEmbedding Mode
              (Finsupp.single other coefficient) mode +
            finiteCoefficientEmbedding Mode rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [finiteCoefficientEmbedding_single, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

private def finiteDiagonalHessian
    (Mode : Type*) [DecidableEq Mode]
    (weight : Mode → Real) :
    (Mode →₀ Complex) →ₗ[Complex] (Mode →₀ Complex) :=
  Finsupp.lsum Complex fun mode =>
    (Finsupp.lsingle mode).comp
      (((weight mode : Real) : Complex) •
        (LinearMap.id : Complex →ₗ[Complex] Complex))

@[simp]
private theorem finiteDiagonalHessian_single
    (Mode : Type*) [DecidableEq Mode]
    (weight : Mode → Real)
    (mode : Mode) (coefficient : Complex) :
    finiteDiagonalHessian Mode weight (Finsupp.single mode coefficient) =
      ((weight mode : Real) : Complex) •
        Finsupp.single mode coefficient := by
  simp [finiteDiagonalHessian]

@[simp]
private theorem finiteDiagonalHessian_apply
    (Mode : Type*) [DecidableEq Mode]
    (weight : Mode → Real)
    (coefficients : Mode →₀ Complex) (mode : Mode) :
    finiteDiagonalHessian Mode weight coefficients mode =
      ((weight mode : Real) : Complex) * coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add, Finsupp.add_apply, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp
        ring
      · simp [hMode]

private theorem finiteCoefficientEmbedding_inner_finiteDiagonalHessian_re
    (Mode : Type*) [DecidableEq Mode]
    (weight : Mode → Real)
    (coefficients : Mode →₀ Complex) :
    (inner Complex
      (finiteCoefficientEmbedding Mode coefficients)
      (finiteCoefficientEmbedding Mode
        (finiteDiagonalHessian Mode weight coefficients))).re =
      coefficients.sum fun mode coefficient =>
        weight mode * Complex.normSq coefficient := by
  rw [lp.inner_eq_tsum]
  simp_rw [finiteCoefficientEmbedding_apply,
    finiteDiagonalHessian_apply]
  rw [tsum_eq_sum (s := coefficients.support) (by
    intro mode hMode
    rw [Finsupp.notMem_support_iff.mp hMode]
    simp)]
  change RCLike.reCLM
      (∑ mode ∈ coefficients.support,
        inner Complex (coefficients mode)
          (((weight mode : Real) : Complex) * coefficients mode)) =
    coefficients.sum fun mode coefficient =>
      weight mode * Complex.normSq coefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro mode _
  simp [Complex.normSq_apply]
  ring

/-- Exact matter Hessian coefficient `2D + m²` in both physical sectors. -/
def programPPrimitiveSpinCMatterHessianWeight
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode) : Real :=
  primitiveSpinCGeometricSignedKineticHessianWeight
      period hPeriod mode.2 +
    massSquared

/-- Arbitrary finite two-sector signed coefficients. -/
abbrev ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
  ProgramPPrimitiveSpinCMatterMode →₀ Complex

/-- Finite diagonal realization of the exact two-sector Hessian. -/
def programPPrimitiveSpinCMatterFiniteHessian
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
  finiteDiagonalHessian ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)

@[simp]
theorem programPPrimitiveSpinCMatterFiniteHessian_apply
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared
        coefficients mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) * coefficients mode :=
  finiteDiagonalHessian_apply _ _ _ _

/-- Canonical inclusion of finite coefficients into the ambient two-sector
coefficient Hilbert space. -/
def programPPrimitiveSpinCMatterFiniteHilbertEmbedding :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      ComplexDiagonalHilbert ProgramPPrimitiveSpinCMatterMode :=
  finiteCoefficientEmbedding ProgramPPrimitiveSpinCMatterMode

@[simp]
theorem programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients mode =
      coefficients mode :=
  finiteCoefficientEmbedding_apply
    ProgramPPrimitiveSpinCMatterMode coefficients mode

/-- The finite two-sector coefficient core is dense in the ambient matter
Hilbert space.  No graph-norm density is claimed here. -/
theorem programPPrimitiveSpinCMatterFiniteHilbertEmbedding_range_dense :
    Dense
      ((LinearMap.range
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding :
          Submodule Complex
            (ComplexDiagonalHilbert
              ProgramPPrimitiveSpinCMatterMode)) :
        Set (ComplexDiagonalHilbert
          ProgramPPrimitiveSpinCMatterMode)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex
        (ComplexDiagonalHilbert ProgramPPrimitiveSpinCMatterMode)) =
        (Submodule.span Complex
          (Set.range
            (complexDiagonalBasis
              ProgramPPrimitiveSpinCMatterMode))).topologicalClosure :=
      (HilbertBasis.dense_span
        (complexDiagonalBasis
          ProgramPPrimitiveSpinCMatterMode)).symm
    _ ≤ (LinearMap.range
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding
          ).topologicalClosure :=
      Submodule.topologicalClosure_mono
        (Submodule.span_le.mpr (by
          rintro _ ⟨mode, rfl⟩
          refine ⟨Finsupp.single mode 1, ?_⟩
          change
            finiteCoefficientEmbedding
                ProgramPPrimitiveSpinCMatterMode
                (Finsupp.single mode 1) =
              complexDiagonalBasis
                ProgramPPrimitiveSpinCMatterMode mode
          rw [finiteCoefficientEmbedding_single,
            complexDiagonalBasis_eq_single]))

/-- Two independent primitive SpinC smooth matter sectors. -/
abbrev ProgramPPrimitiveSpinCMatterSmoothField :=
  Sector →
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter

/-- The genuine primitive smooth matter action.  Its differential expression
is the same `2D + m²` used by the graph Hessian below. -/
def programPPrimitiveSpinCMatterSmoothAction
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    Real :=
  (1 / 2 : Real) *
    ∑ sector : Sector,
      (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (state sector)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared (state sector))).re

/-- A single signed coefficient synthesized into one physical smooth
matter sector. -/
def programPPrimitiveSpinCMatterSmoothSingleSynthesis
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    ProgramPPrimitiveSpinCMatterSmoothField period hPeriod :=
  fun other =>
    if other = sector then
      primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod (Finsupp.single mode coefficient)
    else
      0

/-- Smooth synthesis of arbitrary finite coefficients, curried by physical
sector. -/
def programPPrimitiveSpinCMatterSmoothFiniteSynthesis
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ProgramPPrimitiveSpinCMatterSmoothField period hPeriod :=
  fun sector =>
    primitiveSpinCGeometricSignedDiracFiniteSynthesis
      period hPeriod (coefficients.curry sector)

@[simp]
theorem programPPrimitiveSpinCMatterSmoothFiniteSynthesis_apply
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (sector : Sector) :
    programPPrimitiveSpinCMatterSmoothFiniteSynthesis
        period hPeriod coefficients sector =
      primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod (coefficients.curry sector) :=
  rfl

/-- Finite signed coefficients synthesized linearly into the genuine smooth
two-sector SpinC tangent. -/
def programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      ProgramPPrimitiveSpinCMatterSmoothField period hPeriod where
  toFun := programPPrimitiveSpinCMatterSmoothFiniteSynthesis
    period hPeriod
  map_add' first second := by
    funext sector
    have hCurry :
        (first + second).curry sector =
          first.curry sector + second.curry sector := by
      ext mode
      rfl
    change
      primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod ((first + second).curry sector) =
        primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod (first.curry sector) +
          primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod (second.curry sector)
    rw [hCurry, map_add]
  map_smul' scalar coefficients := by
    funext sector
    have hCurry :
        (scalar • coefficients).curry sector =
          scalar • coefficients.curry sector := by
      ext mode
      rfl
    change
      primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod ((scalar • coefficients).curry sector) =
        scalar • primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod (coefficients.curry sector)
    rw [hCurry, map_smul]

/-- Real-linear restriction of the finite smooth matter synthesis. -/
def programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ProgramPPrimitiveSpinCMatterSmoothField period hPeriod where
  toFun := programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
    period hPeriod
  map_add' first second := by
    exact map_add
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
        period hPeriod) first second
  map_smul' real coefficients := by
    have hCoefficients :
        real • coefficients = (real : Complex) • coefficients := by
      ext mode
      rfl
    rw [hCoefficients, map_smul]
    funext sector
    change
      d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter (real : Complex)
          ((programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
            period hPeriod) coefficients sector) =
        real •
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
            period hPeriod) coefficients sector
    exact d9PrimitiveSpinCComplexScalarSection_ofReal
      period hPeriod .positiveQuarter real _

private theorem primitiveSpinCGeometricSignedFiniteSynthesis_embedding
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients) =
      primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
        (finiteCoefficientEmbedding
          PrimitiveSpinCGeometricSignedMode coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add, map_add, inductionHypothesis,
        finiteCoefficientEmbedding_single,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
        primitiveSpinCGeometricSignedDiracModeUnitary_single,
        map_smul]
      rfl

private theorem primitiveSpinCGeometricSignedSmoothFinitePairing
    (massSquared : Real)
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    (d9PrimitiveSpinCGeometricL2Pairing
      period hPeriod .positiveQuarter
      (primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod coefficients)
      (primitiveSpinCGeometricSignedActionHessianSmoothCore
        period hPeriod massSquared
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients))).re =
      coefficients.sum fun mode coefficient =>
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) *
          Complex.normSq coefficient := by
  rw [primitiveSpinCGeometricSignedDiracFiniteSynthesis_intertwines_hessian]
  change
    (inner Complex
      (primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod coefficients)
      (primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod
        (primitiveSpinCGeometricSignedFiniteActionHessian
          period hPeriod massSquared coefficients))).re = _
  rw [← UniformSpace.Completion.inner_coe]
  change
    (inner Complex
      (d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients))
      (d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared coefficients)))).re = _
  rw [primitiveSpinCGeometricSignedFiniteSynthesis_embedding,
    primitiveSpinCGeometricSignedFiniteSynthesis_embedding,
    LinearIsometryEquiv.inner_map_map]
  change
    (inner Complex
      (finiteCoefficientEmbedding
        PrimitiveSpinCGeometricSignedMode coefficients)
      (finiteCoefficientEmbedding PrimitiveSpinCGeometricSignedMode
        (finiteDiagonalHessian PrimitiveSpinCGeometricSignedMode
          (fun mode =>
            primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared)
          coefficients))).re = _
  exact finiteCoefficientEmbedding_inner_finiteDiagonalHessian_re
    PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared)
    coefficients

@[simp]
theorem programPPrimitiveSpinCMatterL2Pairing_eq_inner
    (first second :
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter first second =
      inner Complex first second :=
  rfl

/-- Exact smooth-action value on one synthesized signed mode in one physical
sector. -/
theorem programPPrimitiveSpinCMatterSmoothAction_single
    (massSquared : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    programPPrimitiveSpinCMatterSmoothAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterSmoothSingleSynthesis
          period hPeriod sector mode coefficient) =
      (1 / 2 : Real) *
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) *
        Complex.normSq coefficient := by
  classical
  let vector :=
    primitiveSpinCGeometricSignedDiracModeSmoothVector
      period hPeriod mode
  have hVectorNorm : ‖vector‖ = 1 := by
    have hCompleted :=
      (primitiveSpinCGeometricSignedDiracModeVector_orthonormal
        period hPeriod).1 mode
    simpa [vector,
      primitiveSpinCGeometricSignedDiracModeVector,
      primitiveSpinCGeometricSignedDiracModeSmoothVector,
      primitiveSpinCGeometricSignedModeVector,
      UniformSpace.Completion.norm_coe] using hCompleted
  have hVectorInner : inner Complex vector vector = 1 :=
    inner_self_eq_one_of_norm_eq_one hVectorNorm
  unfold programPPrimitiveSpinCMatterSmoothAction
  rw [Finset.sum_eq_single sector]
  · simp only [programPPrimitiveSpinCMatterSmoothSingleSynthesis,
      if_pos]
    rw [primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
      map_smul,
      primitiveSpinCGeometricSignedActionHessianSmoothCore_mode]
    change
      (1 / 2 : Real) *
          (inner Complex
            (coefficient • vector)
            (coefficient •
              (((primitiveSpinCGeometricSignedKineticHessianWeight
                period hPeriod mode + massSquared : Real) : Complex) •
                vector))).re =
        (1 / 2 : Real) *
          (primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared) *
          Complex.normSq coefficient
    simp only [inner_smul_left, inner_smul_right]
    rw [hVectorInner]
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  · intro other _ hOther
    simp [programPPrimitiveSpinCMatterSmoothSingleSynthesis, hOther]
  · simp

/-- Exact independently integrated smooth-action value on the whole finite
two-sector signed spectral core. -/
theorem programPPrimitiveSpinCMatterSmoothAction_finite
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterSmoothAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
          period hPeriod coefficients) =
      (1 / 2 : Real) *
        coefficients.sum fun mode coefficient =>
          programPPrimitiveSpinCMatterHessianWeight
            period hPeriod massSquared mode *
            Complex.normSq coefficient := by
  unfold programPPrimitiveSpinCMatterSmoothAction
  congr 1
  calc
    _ = ∑ sector : Sector,
        (coefficients.curry sector).sum fun mode coefficient =>
          (primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared) *
            Complex.normSq coefficient := by
      apply Finset.sum_congr rfl
      intro sector _
      rw [programPPrimitiveSpinCMatterSmoothFiniteSynthesis_apply,
        primitiveSpinCGeometricSignedSmoothFinitePairing]
    _ = coefficients.sum fun mode coefficient =>
        programPPrimitiveSpinCMatterHessianWeight
          period hPeriod massSquared mode *
          Complex.normSq coefficient := by
      simp only [programPPrimitiveSpinCMatterHessianWeight]
      rw [← Finsupp.sum_curry_index coefficients
        (fun _ mode coefficient =>
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) *
          Complex.normSq coefficient)]
      apply (Finsupp.sum_fintype
        coefficients.curry
        (fun _ sectorCoefficients =>
          sectorCoefficients.sum fun mode coefficient =>
            (primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared) *
              Complex.normSq coefficient)
        (by intro; simp)).symm

/-- Ambient signed coefficient Hilbert space of both matter sectors. -/
abbrev ProgramPPrimitiveSpinCMatterHilbert :=
  ComplexDiagonalHilbert ProgramPPrimitiveSpinCMatterMode

local instance programPPrimitiveSpinCMatterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- Closed graph of the exact signed matter Hessian. -/
abbrev ProgramPPrimitiveSpinCMatterGraphDomain
    (massSquared : Real) :=
  ComplexDiagonalGraphDomain ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)

/-- Canonical graph representative of one coefficient in one signed mode
and physical sector. -/
def programPPrimitiveSpinCMatterGraphSingle
    (massSquared : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared := by
  let weight :=
    programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared
  let key : ProgramPPrimitiveSpinCMatterMode := (sector, mode)
  let state : ProgramPPrimitiveSpinCMatterHilbert :=
    lp.single 2 key coefficient
  let image : ProgramPPrimitiveSpinCMatterHilbert :=
    lp.single 2 key ((weight key : Real) * coefficient)
  have hRelation :
      ∀ other, image other = (weight other : Complex) * state other := by
    intro other
    by_cases hOther : other = key
    · subst other
      simp [state, image, lp.single_apply]
    · simp [state, image, lp.single_apply, hOther]
  let domainState :
      (complexDiagonalOperator
        ProgramPPrimitiveSpinCMatterMode weight).domain :=
    ⟨state, ⟨image, hRelation⟩⟩
  refine ⟨(state, image), ?_⟩
  apply (LinearPMap.mem_graph_iff
    (complexDiagonalOperator
      ProgramPPrimitiveSpinCMatterMode weight)).2
  refine ⟨domainState, rfl, ?_⟩
  ext other
  rw [complexDiagonalOperator_apply]
  exact (hRelation other).symm

/-- Canonical graph representative of an arbitrary finite two-sector
coefficient family. -/
def programPPrimitiveSpinCMatterGraphFinite
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared := by
  let weight :=
    programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared
  let state : ProgramPPrimitiveSpinCMatterHilbert :=
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients
  let image : ProgramPPrimitiveSpinCMatterHilbert :=
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding
      (programPPrimitiveSpinCMatterFiniteHessian
        period hPeriod massSquared coefficients)
  have hRelation :
      ∀ mode, image mode = (weight mode : Complex) * state mode := by
    intro mode
    dsimp [image, state,
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding,
      programPPrimitiveSpinCMatterFiniteHessian]
    rw [finiteCoefficientEmbedding_apply,
      finiteCoefficientEmbedding_apply,
      finiteDiagonalHessian_apply]
  let domainState :
      (complexDiagonalOperator
        ProgramPPrimitiveSpinCMatterMode weight).domain :=
    ⟨state, ⟨image, hRelation⟩⟩
  refine ⟨(state, image), ?_⟩
  apply (LinearPMap.mem_graph_iff
    (complexDiagonalOperator
      ProgramPPrimitiveSpinCMatterMode weight)).2
  refine ⟨domainState, rfl, ?_⟩
  ext mode
  rw [complexDiagonalOperator_apply]
  exact (hRelation mode).symm

@[simp]
theorem programPPrimitiveSpinCMatterGraphFinite_fst
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (programPPrimitiveSpinCMatterGraphFinite
      period hPeriod massSquared coefficients).1.1 =
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients :=
  rfl

@[simp]
theorem programPPrimitiveSpinCMatterGraphFinite_snd
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (programPPrimitiveSpinCMatterGraphFinite
      period hPeriod massSquared coefficients).1.2 =
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding
      (programPPrimitiveSpinCMatterFiniteHessian
          period hPeriod massSquared coefficients) :=
  rfl

/-- Linear finite-core inclusion into the exact matter graph. -/
def programPPrimitiveSpinCMatterGraphFiniteLinearMap
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared where
  toFun := programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp
  map_smul' scalar coefficients := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp

/-- Real-linear restriction of the finite-core inclusion into the graph. -/
def programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared where
  toFun :=
    programPPrimitiveSpinCMatterGraphFiniteLinearMap
      period hPeriod massSquared
  map_add' first second :=
    (programPPrimitiveSpinCMatterGraphFiniteLinearMap
      period hPeriod massSquared).map_add first second
  map_smul' scalar coefficients := by
    have hCoefficients :
        scalar • coefficients = (scalar : Complex) • coefficients := by
      ext mode
      rfl
    rw [hCoefficients, map_smul]
    exact (RCLike.real_smul_eq_coe_smul
      (K := Complex) scalar
        (programPPrimitiveSpinCMatterGraphFiniteLinearMap
          period hPeriod massSquared coefficients)).symm

theorem programPPrimitiveSpinCMatterGraphFiniteLinearMap_injective
    (massSquared : Real) :
    Function.Injective
      (programPPrimitiveSpinCMatterGraphFiniteLinearMap
        period hPeriod massSquared) := by
  intro first second hEqual
  have hFirst := congrArg (fun state => state.1.1) hEqual
  ext mode
  have hMode := congrArg
    (fun state : ProgramPPrimitiveSpinCMatterHilbert => state mode) hFirst
  simpa [programPPrimitiveSpinCMatterGraphFiniteLinearMap] using hMode

/-- Finite signed matter modes are dense for the actual graph norm, not only
for the ambient coefficient Hilbert norm. -/
theorem programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange
    (massSquared : Real) :
    DenseRange
      (programPPrimitiveSpinCMatterGraphFiniteLinearMap
        period hPeriod massSquared) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro state
  let closedRange :=
    (LinearMap.range
      (programPPrimitiveSpinCMatterGraphFiniteLinearMap
        period hPeriod massSquared)).topologicalClosure
  change state ∈ closedRange
  let term := fun mode : ProgramPPrimitiveSpinCMatterMode =>
    programPPrimitiveSpinCMatterGraphFiniteLinearMap
      period hPeriod massSquared
      (Finsupp.single mode (state.1.1 mode))
  have hTermFst :
      (fun mode => (term mode).1.1) =
        (fun mode => lp.single 2 mode (state.1.1 mode)) := by
    funext mode
    ext other
    dsimp [term, programPPrimitiveSpinCMatterGraphFiniteLinearMap]
    rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
    change (Finsupp.single mode (state.1.1 mode)) other =
      (lp.single 2 mode (state.1.1 mode) :
        ProgramPPrimitiveSpinCMatterHilbert) other
    by_cases hOther : other = mode
    · subst other
      simp
    · rw [Finsupp.single_eq_of_ne hOther]
      simp [hOther]
  have hFst : HasSum (fun mode => (term mode).1.1) state.1.1 := by
    rw [hTermFst]
    exact lp.hasSum_single ENNReal.ofNat_ne_top state.1.1
  have hTermSnd :
      (fun mode => (term mode).1.2) =
        (fun mode => lp.single 2 mode (state.1.2 mode)) := by
    funext mode
    ext other
    rw [complexDiagonalGraphDomain_relation
      ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared) (term mode) other]
    rw [show (term mode).1.1 = lp.single 2 mode (state.1.1 mode) from
      congrFun hTermFst mode]
    by_cases hOther : other = mode
    · subst other
      rw [complexDiagonalGraphDomain_relation
        ProgramPPrimitiveSpinCMatterMode
        (programPPrimitiveSpinCMatterHessianWeight
          period hPeriod massSquared) state mode]
      simp
    · simp [lp.single_apply, hOther]
  have hSnd : HasSum (fun mode => (term mode).1.2) state.1.2 := by
    rw [hTermSnd]
    exact lp.hasSum_single ENNReal.ofNat_ne_top state.1.2
  have hGraph : HasSum term state := by
    rw [HasSum, tendsto_subtype_rng]
    simpa [HasSum, term] using hFst.prodMk hSnd
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hGraph
  filter_upwards with modes
  apply Submodule.le_topologicalClosure
  refine ⟨∑ mode ∈ modes, Finsupp.single mode (state.1.1 mode), ?_⟩
  simp [term]

/-- Inclusion of the graph domain into the ambient Hilbert space, over the
real scalars of the variational action. -/
def programPPrimitiveSpinCMatterGraphFstRealCLM
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (complexDiagonalGraphFstCLM ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)).restrictScalars Real

/-- The signed matter Hessian, continuous from its graph norm to the ambient
Hilbert space and viewed over `Real`. -/
def programPPrimitiveSpinCMatterGraphOperatorRealCLM
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (complexDiagonalGraphOperatorCLM ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)).restrictScalars Real

/-- Real operator pairing on the exact signed matter graph. -/
def programPPrimitiveSpinCMatterGraphForm
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared →L[Real] Real :=
  (innerSL Real).bilinearComp
    (programPPrimitiveSpinCMatterGraphFstRealCLM
      period hPeriod massSquared)
    (programPPrimitiveSpinCMatterGraphOperatorRealCLM
      period hPeriod massSquared)

@[simp]
theorem programPPrimitiveSpinCMatterGraphForm_apply
    (massSquared : Real)
    (first second :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared first second =
      inner Real first.1.1 second.1.2 :=
  rfl

/-- The exact signed matter operator pairing is symmetric on its graph. -/
theorem programPPrimitiveSpinCMatterGraphForm_comm
    (massSquared : Real)
    (first second :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared first second =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared second first := by
  let weight :=
    programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared
  let operator :=
    complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode weight
  let firstDomain : operator.domain :=
    ⟨first.1.1, ⟨first.1.2, by
      intro mode
      exact complexDiagonalGraphDomain_relation
        ProgramPPrimitiveSpinCMatterMode weight first mode⟩⟩
  let secondDomain : operator.domain :=
    ⟨second.1.1, ⟨second.1.2, by
      intro mode
      exact complexDiagonalGraphDomain_relation
        ProgramPPrimitiveSpinCMatterMode weight second mode⟩⟩
  have hFirstOperator : operator firstDomain = first.1.2 := by
    ext mode
    rw [complexDiagonalOperator_apply]
    exact (complexDiagonalGraphDomain_relation
      ProgramPPrimitiveSpinCMatterMode weight first mode).symm
  have hSecondOperator : operator secondDomain = second.1.2 := by
    ext mode
    rw [complexDiagonalOperator_apply]
    exact (complexDiagonalGraphDomain_relation
      ProgramPPrimitiveSpinCMatterMode weight second mode).symm
  have hAdjoint :=
    complexDiagonalOperator_isFormalAdjoint_self
      ProgramPPrimitiveSpinCMatterMode weight firstDomain secondDomain
  rw [programPPrimitiveSpinCMatterGraphForm_apply,
    programPPrimitiveSpinCMatterGraphForm_apply]
  have hReal :
      inner Real (firstDomain : ProgramPPrimitiveSpinCMatterHilbert)
          (operator secondDomain) =
        inner Real (secondDomain : ProgramPPrimitiveSpinCMatterHilbert)
          (operator firstDomain) := by
    calc
    inner Real (firstDomain : ProgramPPrimitiveSpinCMatterHilbert)
        (operator secondDomain) =
      inner Real (operator firstDomain)
        (secondDomain : ProgramPPrimitiveSpinCMatterHilbert) := by
          simpa only [real_inner_eq_re_inner] using
            congrArg RCLike.re hAdjoint.symm
    _ = inner Real (secondDomain : ProgramPPrimitiveSpinCMatterHilbert)
        (operator firstDomain) :=
      real_inner_comm _ _
  simpa only [hFirstOperator, hSecondOperator] using hReal

/-- The genuine real quadratic action on the signed matter graph. -/
def programPPrimitiveSpinCMatterGraphAction
    (massSquared : Real)
    (state :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) : Real :=
  (1 / 2 : Real) *
    programPPrimitiveSpinCMatterGraphForm
      period hPeriod massSquared state state

/-- The coefficient graph action has the same exact one-mode value as the
primitive smooth action. -/
theorem programPPrimitiveSpinCMatterGraphAction_single
    (massSquared : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode coefficient) =
      (1 / 2 : Real) *
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) *
        Complex.normSq coefficient := by
  rw [programPPrimitiveSpinCMatterGraphAction,
    programPPrimitiveSpinCMatterGraphForm_apply]
  change
    (1 / 2 : Real) *
        inner Real
          (lp.single 2 (sector, mode) coefficient :
            ProgramPPrimitiveSpinCMatterHilbert)
          (lp.single 2 (sector, mode)
            (((primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared : Real) : Complex) *
              coefficient) :
            ProgramPPrimitiveSpinCMatterHilbert) =
      (1 / 2 : Real) *
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) *
        Complex.normSq coefficient
  rw [real_inner_eq_re_inner, lp.inner_single_left]
  simp [lp.single_apply, Complex.normSq_apply]
  ring

/-- Concrete finite-core agreement between the independently integrated
primitive smooth action and the closed graph action. -/
theorem programPPrimitiveSpinCMatterSmoothAction_single_eq_graphAction
    (massSquared : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    programPPrimitiveSpinCMatterSmoothAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterSmoothSingleSynthesis
          period hPeriod sector mode coefficient) =
      programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode coefficient) := by
  rw [programPPrimitiveSpinCMatterSmoothAction_single,
    programPPrimitiveSpinCMatterGraphAction_single]

/-- Exact graph-action value on the whole finite two-sector signed spectral
core. -/
theorem programPPrimitiveSpinCMatterGraphAction_finite
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod massSquared coefficients) =
      (1 / 2 : Real) *
        coefficients.sum fun mode coefficient =>
          programPPrimitiveSpinCMatterHessianWeight
            period hPeriod massSquared mode *
            Complex.normSq coefficient := by
  rw [programPPrimitiveSpinCMatterGraphAction,
    programPPrimitiveSpinCMatterGraphForm_apply,
    programPPrimitiveSpinCMatterGraphFinite_fst,
    programPPrimitiveSpinCMatterGraphFinite_snd,
    real_inner_eq_re_inner]
  change
    (1 / 2 : Real) *
        (inner Complex
          (finiteCoefficientEmbedding
            ProgramPPrimitiveSpinCMatterMode coefficients)
          (finiteCoefficientEmbedding ProgramPPrimitiveSpinCMatterMode
            (finiteDiagonalHessian ProgramPPrimitiveSpinCMatterMode
              (programPPrimitiveSpinCMatterHessianWeight
                period hPeriod massSquared)
              coefficients))).re =
      _
  rw [finiteCoefficientEmbedding_inner_finiteDiagonalHessian_re]

/-- Whole-finite-core agreement between the independently integrated
primitive smooth action and the closed graph action. -/
theorem programPPrimitiveSpinCMatterSmoothAction_finite_eq_graphAction
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterSmoothAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
          period hPeriod coefficients) =
      programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod massSquared coefficients) := by
  rw [programPPrimitiveSpinCMatterSmoothAction_finite,
    programPPrimitiveSpinCMatterGraphAction_finite]

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric :
      ∀ first second, bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

/-- The first Frechet derivative of the actual graph action. -/
theorem programPPrimitiveSpinCMatterGraphAction_hasFDerivAt
    (massSquared : Real)
    (state :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    HasFDerivAt
      (programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared)
      (programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared state) state := by
  exact symmetricQuadratic_hasFDerivAt
    (programPPrimitiveSpinCMatterGraphForm
      period hPeriod massSquared)
    (programPPrimitiveSpinCMatterGraphForm_comm
      period hPeriod massSquared)
    state

theorem programPPrimitiveSpinCMatterGraphAction_fderiv
    (massSquared : Real)
    (state :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    fderiv Real
        (programPPrimitiveSpinCMatterGraphAction
          period hPeriod massSquared) state =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared state :=
  (programPPrimitiveSpinCMatterGraphAction_hasFDerivAt
    period hPeriod massSquared state).fderiv

/-- The second Frechet derivative is the constant exact operator form. -/
theorem programPPrimitiveSpinCMatterGraphAction_second_fderiv
    (massSquared : Real)
    (base :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    fderiv Real
        (fun state => fderiv Real
          (programPPrimitiveSpinCMatterGraphAction
            period hPeriod massSquared) state) base =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared := by
  rw [show
      (fun state => fderiv Real
        (programPPrimitiveSpinCMatterGraphAction
          period hPeriod massSquared) state) =
      (fun state =>
        programPPrimitiveSpinCMatterGraphForm
          period hPeriod massSquared state) from by
    funext state
    exact programPPrimitiveSpinCMatterGraphAction_fderiv
      period hPeriod massSquared state]
  let hessian :
      ProgramPPrimitiveSpinCMatterGraphDomain
          period hPeriod massSquared →L[Real]
        ProgramPPrimitiveSpinCMatterGraphDomain
          period hPeriod massSquared →L[Real] Real :=
    programPPrimitiveSpinCMatterGraphForm
      period hPeriod massSquared
  change fderiv Real
      (hessian :
        ProgramPPrimitiveSpinCMatterGraphDomain
            period hPeriod massSquared →
          ProgramPPrimitiveSpinCMatterGraphDomain
            period hPeriod massSquared →L[Real] Real)
      base = hessian
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E :=
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared)
    (F :=
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared →L[Real] Real)
    hessian

/-- Same-action identity: the original signed operator pairing is the mixed
second Frechet derivative of the displayed quadratic action. -/
theorem programPPrimitiveSpinCMatterGraph_pairing_eq_sameActionHessian
    (massSquared : Real)
    (base first second :
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared) :
    inner Real first.1.1 second.1.2 =
      fderiv Real
          (fun state => fderiv Real
            (programPPrimitiveSpinCMatterGraphAction
              period hPeriod massSquared) state)
          base first second := by
  rw [programPPrimitiveSpinCMatterGraphAction_second_fderiv,
    programPPrimitiveSpinCMatterGraphForm_apply]

theorem programPPrimitiveSpinCMatterGraphAction_contDiff
    (massSquared : Real) :
    ContDiff Real ⊤
      (programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared) := by
  unfold programPPrimitiveSpinCMatterGraphAction
  exact contDiff_const.mul
    ((programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared).contDiff
      |>.clm_apply contDiff_id)

theorem programPPrimitiveSpinCMatterGraphAction_contDiff_two
    (massSquared : Real) :
    ContDiff Real 2
      (programPPrimitiveSpinCMatterGraphAction
        period hPeriod massSquared) :=
  (programPPrimitiveSpinCMatterGraphAction_contDiff
    period hPeriod massSquared).of_le (by simp)

/-- Finite-zero-gap datum for the two physical copies of `2D + m²`. -/
def programPPrimitiveSpinCMatterHessianFiniteZeroGap
    (massSquared : Real) :
    ComplexDiagonalFiniteZeroGap ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared) := by
  exact
    complexDiagonalFiniteZeroGap_finiteProduct
      PrimitiveSpinCGeometricSignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared)
      (primitiveSpinCGeometricSignedActionHessianFiniteZeroGap
        period hPeriod massSquared)

/-- The graph realization of the exact two-sector matter Hessian is
Fredholm, allowing the genuine finite mass-resonant kernel. -/
theorem programPPrimitiveSpinCMatterGraphOperator_fredholm
    (massSquared : Real) :
    IsClosed
        (LinearMap.range
          (complexDiagonalGraphOperatorCLM
            ProgramPPrimitiveSpinCMatterMode
            (programPPrimitiveSpinCMatterHessianWeight
              period hPeriod massSquared)).toLinearMap :
          Set ProgramPPrimitiveSpinCMatterHilbert) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (complexDiagonalGraphOperatorCLM
            ProgramPPrimitiveSpinCMatterMode
            (programPPrimitiveSpinCMatterHessianWeight
              period hPeriod massSquared)).toLinearMap) ∧
      FiniteDimensional Complex
        (ComplexDiagonalGraphCokernel
          ProgramPPrimitiveSpinCMatterMode
          (programPPrimitiveSpinCMatterHessianWeight
            period hPeriod massSquared)) :=
  complexDiagonalGraphOperator_fredholm
    ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)
    (programPPrimitiveSpinCMatterHessianFiniteZeroGap
      period hPeriod massSquared)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
end JanusFormal
