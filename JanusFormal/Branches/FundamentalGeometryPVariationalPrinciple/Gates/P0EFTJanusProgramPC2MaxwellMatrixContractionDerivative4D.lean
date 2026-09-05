import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D

/-! # Exact derivative of the C² Maxwell matrix contraction -/

namespace JanusFormal
namespace P0EFTJanusProgramPC2MaxwellMatrixContractionDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Product-rule velocity of the quadratic inverse-metric contraction. -/
def c2MaxwellMatrixContractionVelocity
    (inverse velocity first second : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (inverse μ ρ) (velocity ν σ) +
          canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (velocity μ ρ) (inverse ν σ))
        (first μ ν))
      (second ρ σ)

/-- Canonical Fréchet derivative of the quadratic contraction. -/
def c2MaxwellMatrixContractionDerivativeAt
    (inverse first second : C2Matrix period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Scalar period hPeriod :=
  fderiv Real
    (fun candidate => c2MaxwellMatrixContraction
      period hPeriod candidate first second) inverse

theorem c2MaxwellMatrixContraction_hasFDerivAt
    (inverse first second : C2Matrix period hPeriod) :
    HasFDerivAt
      (fun candidate => c2MaxwellMatrixContraction
        period hPeriod candidate first second)
      (c2MaxwellMatrixContractionDerivativeAt
        period hPeriod inverse first second) inverse :=
  ((c2MaxwellMatrixContraction_contDiff period hPeriod first second)
    |>.differentiable (by simp) inverse).hasFDerivAt

private theorem c2MatrixAffineEntry_hasDerivAt
    (inverse velocity : C2Matrix period hPeriod) (row column : Fin 4) :
    HasDerivAt
      (fun scalar : Real => (inverse + scalar • velocity) row column)
      (velocity row column) 0 := by
  have hAffine :=
    (hasDerivAt_id (0 : Real)).smul_const (velocity row column)
      |>.const_add (inverse row column)
      |>.congr_deriv (one_smul Real (velocity row column))
  apply hAffine.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

private theorem c2MaxwellMatrixContractionTerm_line_hasDerivAt
    (inverse velocity first second : C2Matrix period hPeriod)
    (μ ν ρ σ : Fin 4) :
    let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    HasDerivAt
      (fun scalar : Real =>
        product
          (product
            (product ((inverse + scalar • velocity) μ ρ)
              ((inverse + scalar • velocity) ν σ))
            (first μ ν))
          (second ρ σ))
      (product
        (product
          (product (inverse μ ρ) (velocity ν σ) +
            product (velocity μ ρ) (inverse ν σ))
          (first μ ν))
        (second ρ σ)) 0 := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  have hFirst := c2MatrixAffineEntry_hasDerivAt
    period hPeriod inverse velocity μ ρ
  have hSecond := c2MatrixAffineEntry_hasDerivAt
    period hPeriod inverse velocity ν σ
  have hPair :=
    ((product.hasFDerivAt.comp 0 hFirst.hasFDerivAt).clm_apply
      hSecond.hasFDerivAt).hasDerivAt
  have hFirstConstant : HasDerivAt
      (fun _ : Real => first μ ν) 0 0 := hasDerivAt_const 0 _
  have hWithFirst :=
    ((product.hasFDerivAt.comp 0 hPair.hasFDerivAt).clm_apply
      hFirstConstant.hasFDerivAt).hasDerivAt
  have hSecondConstant : HasDerivAt
      (fun _ : Real => second ρ σ) 0 0 := hasDerivAt_const 0 _
  have hWithSecond :=
    ((product.hasFDerivAt.comp 0 hWithFirst.hasFDerivAt).clm_apply
      hSecondConstant.hasFDerivAt).hasDerivAt
  apply hWithSecond.congr_deriv
  simp only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, zero_smul, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, map_zero,
    add_zero, zero_add]
  rfl

private theorem c2MaxwellMatrixContraction_line_hasDerivAt
    (inverse velocity first second : C2Matrix period hPeriod) :
    HasDerivAt
      (fun scalar : Real => c2MaxwellMatrixContraction period hPeriod
        (inverse + scalar • velocity) first second)
      (c2MaxwellMatrixContractionVelocity
        period hPeriod inverse velocity first second) 0 := by
  unfold c2MaxwellMatrixContraction c2MaxwellMatrixContractionVelocity
  have hSigma (μ ν ρ : Fin 4) : HasDerivAt
      (fun scalar : Real => ∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                ((inverse + scalar • velocity) μ ρ)
                ((inverse + scalar • velocity) ν σ))
            (first μ ν))
          (second ρ σ))
      (∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (inverse μ ρ) (velocity ν σ) +
              canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (velocity μ ρ) (inverse ν σ))
            (first μ ν))
          (second ρ σ)) 0 := by
    apply (HasDerivAt.sum (u := Finset.univ) (fun σ _ =>
      c2MaxwellMatrixContractionTerm_line_hasDerivAt
        period hPeriod inverse velocity first second μ ν ρ σ)
      |>.congr_of_eventuallyEq)
    exact Filter.Eventually.of_forall fun scalar => by
      simp only [Finset.sum_apply]
  have hRho (μ ν : Fin 4) : HasDerivAt
      (fun scalar : Real => ∑ ρ : Fin 4, ∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                ((inverse + scalar • velocity) μ ρ)
                ((inverse + scalar • velocity) ν σ))
            (first μ ν))
          (second ρ σ))
      (∑ ρ : Fin 4, ∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (inverse μ ρ) (velocity ν σ) +
              canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (velocity μ ρ) (inverse ν σ))
            (first μ ν))
          (second ρ σ)) 0 := by
    apply (HasDerivAt.sum (u := Finset.univ) (fun ρ _ => hSigma μ ν ρ)
      |>.congr_of_eventuallyEq)
    exact Filter.Eventually.of_forall fun scalar => by
      simp only [Finset.sum_apply]
  have hNu (μ : Fin 4) : HasDerivAt
      (fun scalar : Real => ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                ((inverse + scalar • velocity) μ ρ)
                ((inverse + scalar • velocity) ν σ))
            (first μ ν))
          (second ρ σ))
      (∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (inverse μ ρ) (velocity ν σ) +
              canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (velocity μ ρ) (inverse ν σ))
            (first μ ν))
          (second ρ σ)) 0 := by
    apply (HasDerivAt.sum (u := Finset.univ) (fun ν _ => hRho μ ν)
      |>.congr_of_eventuallyEq)
    exact Filter.Eventually.of_forall fun scalar => by
      simp only [Finset.sum_apply]
  apply (HasDerivAt.sum (u := Finset.univ) (fun μ _ => hNu μ)
    |>.congr_of_eventuallyEq)
  exact Filter.Eventually.of_forall fun scalar => by
    simp only [Finset.sum_apply]

private theorem c2MatrixAffineLine_hasDerivAt
    (base direction : C2Matrix period hPeriod) :
    HasDerivAt (fun scalar : Real => base + scalar • direction)
      direction 0 := by
  have hAffine :=
    (hasDerivAt_const (0 : Real) base).add
      ((hasDerivAt_id (0 : Real)).smul_const direction)
  refine (hAffine.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [zero_add, one_smul]
  · exact Filter.Eventually.of_forall fun _ => rfl

@[simp]
theorem c2MaxwellMatrixContractionDerivativeAt_apply
    (inverse velocity first second : C2Matrix period hPeriod) :
    c2MaxwellMatrixContractionDerivativeAt
        period hPeriod inverse first second velocity =
      c2MaxwellMatrixContractionVelocity
        period hPeriod inverse velocity first second := by
  have hCanonical := c2MaxwellMatrixContraction_hasFDerivAt
    period hPeriod inverse first second
  have hAffine := c2MatrixAffineLine_hasDerivAt
    period hPeriod inverse velocity
  have hAtLineZero : HasFDerivAt
      (fun candidate => c2MaxwellMatrixContraction
        period hPeriod candidate first second)
      (c2MaxwellMatrixContractionDerivativeAt
        period hPeriod inverse first second)
      ((fun scalar : Real => inverse + scalar • velocity) 0) := by
    simpa using hCanonical
  have hComposed :=
    (hAtLineZero.comp 0 hAffine.hasFDerivAt).hasDerivAt
  have hLine := c2MaxwellMatrixContraction_line_hasDerivAt
    period hPeriod inverse velocity first second
  have hUnique := hComposed.unique hLine
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one] using hUnique

/-- Gate marker for the exact C² inverse-metric Maxwell product rule. -/
theorem c2_maxwell_matrix_contraction_derivative_gate
    (inverse first second : C2Matrix period hPeriod) :
    HasFDerivAt
        (fun candidate => c2MaxwellMatrixContraction
          period hPeriod candidate first second)
        (c2MaxwellMatrixContractionDerivativeAt
          period hPeriod inverse first second) inverse ∧
      ∀ velocity,
        c2MaxwellMatrixContractionDerivativeAt
            period hPeriod inverse first second velocity =
          c2MaxwellMatrixContractionVelocity
            period hPeriod inverse velocity first second :=
  ⟨c2MaxwellMatrixContraction_hasFDerivAt
      period hPeriod inverse first second,
    fun velocity => c2MaxwellMatrixContractionDerivativeAt_apply
      period hPeriod inverse velocity first second⟩

end
end P0EFTJanusProgramPC2MaxwellMatrixContractionDerivative4D
end JanusFormal
