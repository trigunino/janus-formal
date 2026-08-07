import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D

/-!
# Finite SpinC Green identity and graph-core closure

The exact signed Fourier modes already provide a canonical finite smooth core.
On that core the geometric operator `2D + m²` is diagonal with real weights,
so its Green identity is unconditional.  This file proves that finite identity
and isolates the sole extension theorem needed for arbitrary smooth primitive
SpinC sections: simultaneous convergence of a finite spectral exhaustion in
ambient `L²` and after application of the smooth Hessian.

Such graph-core density implies the full smooth Dirac Green identity, hence the
maximal-domain membership, operator agreement and same-action realization of
the preceding gate.  No independently chosen Fourier coefficient map, boundary
condition, action or D10 direction is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter Set Topology
open scoped BigOperators ENNReal lp LinearPMap InnerProductSpace
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SignedMode := PrimitiveSpinCGeometricSignedMode
private abbrev OneSectorSmooth :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev FiniteCoefficients :=
  PrimitiveSpinCGeometricSignedFiniteCoefficients
private abbrev OneSectorL2 :=
  D9PrimitiveSpinCGeometricL2Completion period hPeriod .positiveQuarter

/-- Canonical finite-coordinate inclusion in the exact signed coefficient
Hilbert space. -/
private def finiteCoefficientEmbedding :
    FiniteCoefficients →ₗ[Complex]
      ComplexDiagonalHilbert SignedMode :=
  Finsupp.linearCombination Complex (complexDiagonalBasis SignedMode)

@[simp]
private theorem finiteCoefficientEmbedding_single
    (mode : SignedMode) (coefficient : Complex) :
    finiteCoefficientEmbedding
        (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [finiteCoefficientEmbedding, Finsupp.linearCombination_single,
    complexDiagonalBasis_eq_single]

@[simp]
private theorem finiteCoefficientEmbedding_apply
    (coefficients : FiniteCoefficients) (mode : SignedMode) :
    finiteCoefficientEmbedding coefficients mode = coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [finiteCoefficientEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        finiteCoefficientEmbedding
              (Finsupp.single other coefficient) mode +
            finiteCoefficientEmbedding rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [finiteCoefficientEmbedding_single, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

@[simp]
private theorem finiteActionHessian_apply
    (massSquared : Real)
    (coefficients : FiniteCoefficients) (mode : SignedMode) :
    primitiveSpinCGeometricSignedFiniteActionHessian
        period hPeriod massSquared coefficients mode =
      ((primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared : Real) : Complex) *
        coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add, Finsupp.add_apply, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        rw [primitiveSpinCGeometricSignedFiniteActionHessian_single]
        simp
        ring
      · rw [primitiveSpinCGeometricSignedFiniteActionHessian_single]
        simp [hMode]

/-- The genuine finite smooth synthesis is exactly the geometric signed-mode
unitary applied to the canonical finite coefficient inclusion. -/
private theorem finiteSynthesis_embedding
    (coefficients : FiniteCoefficients) :
    d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients) =
      primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
        (finiteCoefficientEmbedding coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [finiteCoefficientEmbedding]
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add, map_add, inductionHypothesis,
        finiteCoefficientEmbedding_single,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
        primitiveSpinCGeometricSignedDiracModeUnitary_single,
        map_smul]
      rfl

/-- Every finite coefficient packet belongs to the maximal signed domain. -/
private def finiteCoefficientDomain
    (massSquared : Real) (coefficients : FiniteCoefficients) :
    (primitiveSpinCGeometricSignedActionHessianOperator
      period hPeriod massSquared).domain :=
  ⟨finiteCoefficientEmbedding coefficients,
    ⟨finiteCoefficientEmbedding
        (primitiveSpinCGeometricSignedFiniteActionHessian
          period hPeriod massSquared coefficients), by
      intro mode
      rw [finiteCoefficientEmbedding_apply,
        finiteCoefficientEmbedding_apply,
        finiteActionHessian_apply]⟩⟩

/-- The maximal diagonal operator restricts to the advertised finite
multiplier. -/
private theorem operator_finiteCoefficientDomain
    (massSquared : Real) (coefficients : FiniteCoefficients) :
    primitiveSpinCGeometricSignedActionHessianOperator
        period hPeriod massSquared
        (finiteCoefficientDomain period hPeriod massSquared coefficients) =
      finiteCoefficientEmbedding
        (primitiveSpinCGeometricSignedFiniteActionHessian
          period hPeriod massSquared coefficients) := by
  ext mode
  rw [complexDiagonalOperator_apply,
    finiteCoefficientEmbedding_apply,
    finiteCoefficientEmbedding_apply,
    finiteActionHessian_apply]

/-- Formal adjointness of the real diagonal multiplier on the whole finite
coefficient core. -/
private theorem finiteCoefficient_formalAdjoint
    (massSquared : Real)
    (first second : FiniteCoefficients) :
    inner Complex
        (finiteCoefficientEmbedding first)
        (finiteCoefficientEmbedding
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared second)) =
      inner Complex
        (finiteCoefficientEmbedding
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared first))
        (finiteCoefficientEmbedding second) := by
  let operator :=
    primitiveSpinCGeometricSignedActionHessianOperator
      period hPeriod massSquared
  let firstDomain :=
    finiteCoefficientDomain period hPeriod massSquared first
  let secondDomain :=
    finiteCoefficientDomain period hPeriod massSquared second
  have hAdjoint :=
    complexDiagonalOperator_isFormalAdjoint_self
      SignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared)
      firstDomain secondDomain
  calc
    inner Complex
        (finiteCoefficientEmbedding first)
        (finiteCoefficientEmbedding
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared second)) =
      inner Complex (firstDomain : ComplexDiagonalHilbert SignedMode)
        (operator secondDomain) := by
          rw [operator_finiteCoefficientDomain]
    _ = inner Complex (operator firstDomain)
        (secondDomain : ComplexDiagonalHilbert SignedMode) := hAdjoint.symm
    _ = inner Complex
        (finiteCoefficientEmbedding
          (primitiveSpinCGeometricSignedFiniteActionHessian
            period hPeriod massSquared first))
        (finiteCoefficientEmbedding second) := by
          rw [operator_finiteCoefficientDomain]

/-- Unconditional Green identity on the complete finite smooth signed core. -/
theorem primitiveSpinCGeometricSignedFiniteDiracGreen
    (massSquared : Real)
    (first second : FiniteCoefficients) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod first)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod second)) =
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod first))
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod second) := by
  rw [primitiveSpinCGeometricSignedDiracFiniteSynthesis_intertwines_hessian,
    primitiveSpinCGeometricSignedDiracFiniteSynthesis_intertwines_hessian]
  change
    inner Complex
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod first))
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis period hPeriod
            (primitiveSpinCGeometricSignedFiniteActionHessian
              period hPeriod massSquared second))) =
      inner Complex
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis period hPeriod
            (primitiveSpinCGeometricSignedFiniteActionHessian
              period hPeriod massSquared first)))
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod second))
  rw [finiteSynthesis_embedding, finiteSynthesis_embedding,
    finiteSynthesis_embedding, finiteSynthesis_embedding,
    LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.inner_map_map]
  exact finiteCoefficient_formalAdjoint period hPeriod massSquared first second

/-- The two physical sectors inherit the exact finite Green identity without
mixing their coefficient towers. -/
theorem programPPrimitiveSpinCMatterFiniteDiracGreen
    (massSquared : Real)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∑ sector : Sector,
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
          period hPeriod first sector)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
            period hPeriod second sector))) =
      ∑ sector : Sector,
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricSignedActionHessianSmoothCore
            period hPeriod massSquared
            (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
              period hPeriod first sector))
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
            period hPeriod second sector) := by
  apply Finset.sum_congr rfl
  intro sector _
  simpa only [programPPrimitiveSpinCMatterSmoothFiniteSynthesis_apply] using
    primitiveSpinCGeometricSignedFiniteDiracGreen period hPeriod massSquared
      (first.curry sector) (second.curry sector)

/-- Exact remaining spectral closure statement.  Every smooth primitive
section must admit a finite signed-mode exhaustion converging both in ambient
`L²` and after applying the smooth Hessian.  This is graph-core density, not a
new action or coefficient choice. -/
structure ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D
    (massSquared : Real) : Prop where
  approximate : ∀ field : OneSectorSmooth period hPeriod,
    ∃ sequence : ℕ → FiniteCoefficients,
      Tendsto
          (fun index =>
            d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                period hPeriod (sequence index)))
          atTop
          (𝓝 (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter field)) ∧
        Tendsto
          (fun index =>
            d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedActionHessianSmoothCore
                period hPeriod massSquared
                (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                  period hPeriod (sequence index))))
          atTop
          (𝓝 (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared field)))

/-- Graph-core density upgrades the finite Green identity to every pair of
smooth primitive sections. -/
def programPPrimitiveSpinCSmoothDiracGreenData_of_graphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCSmoothDiracGreenData4D
      period hPeriod massSquared where
  green := by
    intro first second
    obtain ⟨firstSequence, hFirst, hFirstImage⟩ :=
      density.approximate first
    obtain ⟨secondSequence, hSecond, hSecondImage⟩ :=
      density.approximate second
    let firstL2 : ℕ → OneSectorL2 period hPeriod := fun index =>
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod (firstSequence index))
    let firstImageL2 : ℕ → OneSectorL2 period hPeriod := fun index =>
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod (firstSequence index)))
    let secondL2 : ℕ → OneSectorL2 period hPeriod := fun index =>
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod (secondSequence index))
    let secondImageL2 : ℕ → OneSectorL2 period hPeriod := fun index =>
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared
          (primitiveSpinCGeometricSignedDiracFiniteSynthesis
            period hPeriod (secondSequence index)))
    have hLeft :
        Tendsto
          (fun index => inner Complex (firstL2 index) (secondImageL2 index))
          atTop
          (𝓝 (inner Complex
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter first)
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedActionHessianSmoothCore
                period hPeriod massSquared second)))) := by
      exact
        (((innerSL Complex).continuous.tendsto).comp hFirst).clm_apply
          hSecondImage
    have hRight :
        Tendsto
          (fun index => inner Complex (firstImageL2 index) (secondL2 index))
          atTop
          (𝓝 (inner Complex
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedActionHessianSmoothCore
                period hPeriod massSquared first))
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter second))) := by
      exact
        (((innerSL Complex).continuous.tendsto).comp hFirstImage).clm_apply
          hSecond
    have hFinite : ∀ index,
        inner Complex (firstL2 index) (secondImageL2 index) =
          inner Complex (firstImageL2 index) (secondL2 index) := by
      intro index
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricSignedDiracFiniteSynthesis
              period hPeriod (firstSequence index))
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared
              (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                period hPeriod (secondSequence index))) =
          d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared
              (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                period hPeriod (firstSequence index)))
            (primitiveSpinCGeometricSignedDiracFiniteSynthesis
              period hPeriod (secondSequence index))
      exact primitiveSpinCGeometricSignedFiniteDiracGreen period hPeriod
        massSquared (firstSequence index) (secondSequence index)
    have hRightAsLeft :
        Tendsto
          (fun index => inner Complex (firstL2 index) (secondImageL2 index))
          atTop
          (𝓝 (inner Complex
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedActionHessianSmoothCore
                period hPeriod massSquared first))
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter second))) :=
      hRight.congr' (Filter.Eventually.of_forall fun index =>
        (hFinite index).symm)
    have hLimit := tendsto_nhds_unique hLeft hRightAsLeft
    change
      inner Complex
          (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter first)
          (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared second)) =
        inner Complex
          (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared first))
          (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter second)
    exact hLimit

/-- Graph-core density therefore provides the exact formal-symmetry datum used
by the maximal-domain gate. -/
def programPPrimitiveSpinCSmoothDiracFormalSymmetryData_of_graphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D
      period hPeriod massSquared :=
  programPPrimitiveSpinCSmoothDiracFormalSymmetryData_of_green period hPeriod
    massSquared
      (programPPrimitiveSpinCSmoothDiracGreenData_of_graphCoreDensity
        period hPeriod massSquared density)

/-- Graph-core density constructs maximal-domain membership and exact operator
agreement for every smooth primitive section. -/
def programPPrimitiveSpinCSmoothMaximalDomainData_of_graphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCSmoothMaximalDomainData4D
      period hPeriod massSquared :=
  programPPrimitiveSpinCSmoothMaximalDomainData_of_diracSymmetry period hPeriod
    massSquared
      (programPPrimitiveSpinCSmoothDiracFormalSymmetryData_of_graphCoreDensity
        period hPeriod massSquared density)

/-- Preferred smooth-to-maximal-graph construction from one graph-core density
theorem. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_graphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D
      period hPeriod massSquared) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_diracGreen period hPeriod
    massSquared
      (programPPrimitiveSpinCSmoothDiracGreenData_of_graphCoreDensity
        period hPeriod massSquared density)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D
end JanusFormal
