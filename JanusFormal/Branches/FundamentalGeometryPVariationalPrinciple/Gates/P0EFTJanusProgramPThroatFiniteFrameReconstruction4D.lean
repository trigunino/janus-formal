import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Trace

/-!
# Canonical reconstruction from a redundant throat frame

The existing finite smooth throat family spans every tangent fiber but need
not be a basis.  The intrinsic nondegenerate throat metric turns it into an
invertible frame operator.  Its inverse supplies canonical redundant
coefficients and exact pointwise reconstruction, without a global-frame
assumption or an additional metric.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

/-! ## Generic algebra of a redundant finite frame -/

section RedundantFiniteFrameAlgebra

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [FiniteDimensional Real E]
variable {dimension : Nat}

/-- Matrix of an endomorphism in a redundant synthesis/analysis pair. -/
def redundantFiniteFrameEncoding
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (endomorphism : E →ₗ[Real] E) :
    Matrix (Fin dimension) (Fin dimension) Real :=
  LinearMap.toMatrix (Pi.basisFun Real (Fin dimension))
    (Pi.basisFun Real (Fin dimension))
    (analysis.comp (endomorphism.comp synthesis))

/-- Extend the encoded endomorphism by the identity on the redundant
complement. -/
def redundantFiniteFrameLift
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (endomorphism : E →ₗ[Real] E) :
    Matrix (Fin dimension) (Fin dimension) Real :=
  1 - redundantFiniteFrameEncoding analysis synthesis LinearMap.id +
    redundantFiniteFrameEncoding analysis synthesis endomorphism

/-- Acting with an encoded endomorphism on redundant coefficients is exactly
analysis after intrinsic synthesis and application. -/
theorem redundantFiniteFrameEncoding_mulVec
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (endomorphism : E →ₗ[Real] E)
    (coefficients : Fin dimension → Real) :
    (redundantFiniteFrameEncoding analysis synthesis endomorphism).mulVec
        coefficients =
      analysis (endomorphism (synthesis coefficients)) := by
  simpa [redundantFiniteFrameEncoding] using
    (LinearMap.toMatrix_mulVec_repr
      (Pi.basisFun Real (Fin dimension))
      (Pi.basisFun Real (Fin dimension))
      (analysis.comp (endomorphism.comp synthesis)) coefficients)

/-- The identity extension is faithful after synthesis, including on
coefficient vectors outside the analysis range. -/
theorem redundantFiniteFrameSynthesis_lift_mulVec
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (endomorphism : E →ₗ[Real] E)
    (coefficients : Fin dimension → Real) :
    synthesis
        ((redundantFiniteFrameLift analysis synthesis endomorphism).mulVec
          coefficients) =
      endomorphism (synthesis coefficients) := by
  change synthesis
    ((1 - redundantFiniteFrameEncoding analysis synthesis LinearMap.id +
      redundantFiniteFrameEncoding analysis synthesis endomorphism).mulVec
        coefficients) = _
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    redundantFiniteFrameEncoding_mulVec,
    redundantFiniteFrameEncoding_mulVec]
  simp only [map_add, map_sub, LinearMap.id_apply]
  have hFirst :
      synthesis (analysis (synthesis coefficients)) = synthesis coefficients := by
    simpa using LinearMap.congr_fun hReconstruct (synthesis coefficients)
  have hSecond :
      synthesis (analysis (endomorphism (synthesis coefficients))) =
        endomorphism (synthesis coefficients) := by
    simpa using LinearMap.congr_fun hReconstruct
      (endomorphism (synthesis coefficients))
  rw [hFirst, hSecond]
  abel

/-- Exact reconstruction makes redundant matrices preserve composition. -/
theorem redundantFiniteFrameEncoding_comp
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (first second : E →ₗ[Real] E) :
    redundantFiniteFrameEncoding analysis synthesis (first.comp second) =
      redundantFiniteFrameEncoding analysis synthesis first *
        redundantFiniteFrameEncoding analysis synthesis second := by
  let coordinateBasis := Pi.basisFun Real (Fin dimension)
  let fiberBasis := Module.finBasis Real E
  let analysisMatrix := LinearMap.toMatrix fiberBasis coordinateBasis analysis
  let synthesisMatrix := LinearMap.toMatrix coordinateBasis fiberBasis synthesis
  have hEncoding (current : E →ₗ[Real] E) :
      redundantFiniteFrameEncoding analysis synthesis current =
        analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis current *
          synthesisMatrix := by
    dsimp [redundantFiniteFrameEncoding, analysisMatrix, synthesisMatrix]
    rw [← LinearMap.toMatrix_eq_toMatrix']
    rw [LinearMap.toMatrix_comp coordinateBasis fiberBasis coordinateBasis
        analysis (current.comp synthesis),
      LinearMap.toMatrix_comp coordinateBasis fiberBasis fiberBasis
        current synthesis]
    exact (Matrix.mul_assoc (LinearMap.toMatrix fiberBasis coordinateBasis analysis)
      (LinearMap.toMatrix fiberBasis fiberBasis current)
      (LinearMap.toMatrix coordinateBasis fiberBasis synthesis)).symm
  have hMatrix : synthesisMatrix * analysisMatrix = 1 := by
    change LinearMap.toMatrix coordinateBasis fiberBasis synthesis *
        LinearMap.toMatrix fiberBasis coordinateBasis analysis = 1
    rw [← LinearMap.toMatrix_comp fiberBasis coordinateBasis fiberBasis
      synthesis analysis, hReconstruct]
    simp
  rw [hEncoding, hEncoding, hEncoding,
    LinearMap.toMatrix_comp fiberBasis fiberBasis fiberBasis first second]
  calc
    analysisMatrix *
          (LinearMap.toMatrix fiberBasis fiberBasis first *
            LinearMap.toMatrix fiberBasis fiberBasis second) *
        synthesisMatrix =
      analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis first *
        ((synthesisMatrix * analysisMatrix) *
          LinearMap.toMatrix fiberBasis fiberBasis second *
            synthesisMatrix) := by
      rw [hMatrix]
      simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis first *
        (synthesisMatrix *
          (analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis second *
            synthesisMatrix)) := by
      simp only [Matrix.mul_assoc]
    _ = analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis first *
          synthesisMatrix *
        (analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis second *
          synthesisMatrix) := by
      exact (Matrix.mul_assoc
        (analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis first)
        synthesisMatrix
        (analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis second *
          synthesisMatrix)).symm

/-- The redundant lift has the intrinsic determinant. -/
theorem redundantFiniteFrameLift_det
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (endomorphism : E →ₗ[Real] E) :
    Matrix.det
        (redundantFiniteFrameLift analysis synthesis endomorphism) =
      LinearMap.det endomorphism := by
  let coordinateBasis := Pi.basisFun Real (Fin dimension)
  let fiberBasis := Module.finBasis Real E
  let analysisMatrix := LinearMap.toMatrix fiberBasis coordinateBasis analysis
  let endomorphismMatrix :=
    LinearMap.toMatrix fiberBasis fiberBasis endomorphism
  let synthesisMatrix := LinearMap.toMatrix coordinateBasis fiberBasis synthesis
  have hEncoding (current : E →ₗ[Real] E) :
      redundantFiniteFrameEncoding analysis synthesis current =
        analysisMatrix * LinearMap.toMatrix fiberBasis fiberBasis current *
          synthesisMatrix := by
    dsimp [redundantFiniteFrameEncoding, analysisMatrix, synthesisMatrix]
    rw [← LinearMap.toMatrix_eq_toMatrix']
    rw [LinearMap.toMatrix_comp coordinateBasis fiberBasis coordinateBasis
        analysis (current.comp synthesis),
      LinearMap.toMatrix_comp coordinateBasis fiberBasis fiberBasis
        current synthesis]
    exact (Matrix.mul_assoc (LinearMap.toMatrix fiberBasis coordinateBasis analysis)
      (LinearMap.toMatrix fiberBasis fiberBasis current)
      (LinearMap.toMatrix coordinateBasis fiberBasis synthesis)).symm
  have hMatrix : synthesisMatrix * analysisMatrix = 1 := by
    change LinearMap.toMatrix coordinateBasis fiberBasis synthesis *
        LinearMap.toMatrix fiberBasis coordinateBasis analysis = 1
    rw [← LinearMap.toMatrix_comp fiberBasis coordinateBasis fiberBasis
      synthesis analysis, hReconstruct]
    simp
  have hLift :
      redundantFiniteFrameLift analysis synthesis endomorphism =
        1 + analysisMatrix *
          ((endomorphismMatrix - 1) * synthesisMatrix) := by
    rw [redundantFiniteFrameLift, hEncoding LinearMap.id,
      hEncoding endomorphism]
    change 1 - analysisMatrix *
          (LinearMap.toMatrix fiberBasis fiberBasis LinearMap.id) *
          synthesisMatrix +
        analysisMatrix * endomorphismMatrix * synthesisMatrix = _
    simp only [LinearMap.toMatrix_id]
    rw [Matrix.sub_mul, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hLift, Matrix.det_one_add_mul_comm]
  have hInside :
      1 + (endomorphismMatrix - 1) * synthesisMatrix * analysisMatrix =
        endomorphismMatrix := by
    rw [Matrix.mul_assoc, hMatrix]
    simp
  rw [hInside, LinearMap.det_toMatrix]

/-- The redundant encoding also has the intrinsic trace. -/
theorem redundantFiniteFrameEncoding_trace
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (endomorphism : E →ₗ[Real] E) :
    Matrix.trace
        (redundantFiniteFrameEncoding analysis synthesis endomorphism) =
      LinearMap.trace Real E endomorphism := by
  let coordinateBasis := Pi.basisFun Real (Fin dimension)
  let fiberBasis := Module.finBasis Real E
  let analysisMatrix := LinearMap.toMatrix fiberBasis coordinateBasis analysis
  let endomorphismMatrix :=
    LinearMap.toMatrix fiberBasis fiberBasis endomorphism
  let synthesisMatrix := LinearMap.toMatrix coordinateBasis fiberBasis synthesis
  have hEncoding :
      redundantFiniteFrameEncoding analysis synthesis endomorphism =
        analysisMatrix * endomorphismMatrix * synthesisMatrix := by
    dsimp [redundantFiniteFrameEncoding, analysisMatrix, endomorphismMatrix,
      synthesisMatrix]
    rw [← LinearMap.toMatrix_eq_toMatrix']
    rw [LinearMap.toMatrix_comp coordinateBasis fiberBasis coordinateBasis
        analysis (endomorphism.comp synthesis),
      LinearMap.toMatrix_comp coordinateBasis fiberBasis fiberBasis
        endomorphism synthesis]
    exact (Matrix.mul_assoc (LinearMap.toMatrix fiberBasis coordinateBasis analysis)
      (LinearMap.toMatrix fiberBasis fiberBasis endomorphism)
      (LinearMap.toMatrix coordinateBasis fiberBasis synthesis)).symm
  have hMatrix : synthesisMatrix * analysisMatrix = 1 := by
    change LinearMap.toMatrix coordinateBasis fiberBasis synthesis *
        LinearMap.toMatrix fiberBasis coordinateBasis analysis = 1
    rw [← LinearMap.toMatrix_comp fiberBasis coordinateBasis fiberBasis
      synthesis analysis, hReconstruct]
    simp
  rw [hEncoding,
    Matrix.trace_mul_comm (analysisMatrix * endomorphismMatrix)
      synthesisMatrix,
    ← Matrix.mul_assoc, hMatrix, Matrix.one_mul]
  exact (LinearMap.trace_eq_matrix_trace Real fiberBasis endomorphism).symm

/-- The identity extension remains multiplicative. -/
theorem redundantFiniteFrameLift_comp
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (first second : E →ₗ[Real] E) :
    redundantFiniteFrameLift analysis synthesis first *
        redundantFiniteFrameLift analysis synthesis second =
      redundantFiniteFrameLift analysis synthesis (first.comp second) := by
  let projector :=
    redundantFiniteFrameEncoding analysis synthesis LinearMap.id
  let firstMatrix := redundantFiniteFrameEncoding analysis synthesis first
  let secondMatrix := redundantFiniteFrameEncoding analysis synthesis second
  let compositeMatrix :=
    redundantFiniteFrameEncoding analysis synthesis (first.comp second)
  have hProjector : projector * projector = projector := by
    simpa [projector] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        LinearMap.id LinearMap.id).symm
  have hProjectorSecond : projector * secondMatrix = secondMatrix := by
    simpa [projector, secondMatrix] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        LinearMap.id second).symm
  have hFirstProjector : firstMatrix * projector = firstMatrix := by
    simpa [projector, firstMatrix] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        first LinearMap.id).symm
  have hComposite : firstMatrix * secondMatrix = compositeMatrix := by
    simpa [firstMatrix, secondMatrix, compositeMatrix] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        first second).symm
  change (1 - projector + firstMatrix) * (1 - projector + secondMatrix) =
    1 - projector + compositeMatrix
  calc
    (1 - projector + firstMatrix) * (1 - projector + secondMatrix) =
        1 - projector - projector + projector * projector + secondMatrix -
          projector * secondMatrix + firstMatrix - firstMatrix * projector +
            firstMatrix * secondMatrix := by
      noncomm_ring
    _ = 1 - projector + compositeMatrix := by
      rw [hProjector, hProjectorSecond, hFirstProjector, hComposite]
      abel

end RedundantFiniteFrameAlgebra

open scoped Manifold ContDiff BigOperators Topology
open Bundle ContinuousLinearMap Filter Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev TangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev SmoothTangentSection :=
  ContMDiffSection throatCoverModelWithCorners ThroatCoverCoordinates ∞
    (TangentFiber period hPeriod)

private abbrev SmoothCovectorSection :=
  ContMDiffSection throatCoverModelWithCorners
    (ThroatCoverCoordinates →L[Real] Real) ∞
    (fun point : EffectiveThroat period hPeriod =>
      TangentFiber period hPeriod point →L[Real] Real)

private abbrev SmoothEndomorphismSection :=
  ContMDiffSection throatCoverModelWithCorners
    (ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
    (fun point : EffectiveThroat period hPeriod =>
      TangentFiber period hPeriod point →L[Real]
        TangentFiber period hPeriod point)

private abbrev ModelTangent := ThroatCoverCoordinates
private abbrev ModelCovector := ModelTangent →L[Real] Real
private abbrev ModelEndomorphism := ModelTangent →L[Real] ModelTangent

local instance tangentFiberFiniteDimensional
    (point : EffectiveThroat period hPeriod) :
    FiniteDimensional Real (TangentFiber period hPeriod point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

local instance tangentFiberT2
    (point : EffectiveThroat period hPeriod) :
    T2Space (TangentFiber period hPeriod point) := by
  change T2Space ThroatCoverCoordinates
  infer_instance

/-- One member of the existing finite spanning family as a smooth section. -/
def smoothThroatFrameVectorSection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (index : Fin frame.count) :
    SmoothTangentSection period hPeriod where
  toFun := fun point => frame.vectorAt point index
  contMDiff_toFun := frame.contMDiff_vector index

@[simp]
theorem smoothThroatFrameVectorSection_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatFrameVectorSection period hPeriod frame index point =
      frame.vectorAt point index :=
  rfl

private def throatCovectorCoordinates
    (covector : SmoothCovectorSection period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) : ModelCovector :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod)
    Real (fun _ : EffectiveThroat period hPeriod => Real)
    anchor current anchor current (covector current)

private theorem throatCovectorCoordinates_contMDiffAt
    (covector : SmoothCovectorSection period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, ModelCovector) ∞
      (throatCovectorCoordinates period hPeriod covector anchor) anchor := by
  have hSmooth := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem throatCovectorCoordinates_apply
    (covector : SmoothCovectorSection period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet)
    (vector : ModelTangent) :
    throatCovectorCoordinates period hPeriod covector anchor current vector =
      covector current
        ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).symm current vector) := by
  unfold throatCovectorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp

/-- A smooth covector-vector rank-one endomorphism on the throat. -/
def smoothThroatCovectorVectorRankOne
    (covector : SmoothCovectorSection period hPeriod)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothEndomorphismSection period hPeriod where
  toFun := fun point => (covector point).smulRight (vector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hCovector := throatCovectorCoordinates_contMDiffAt
      period hPeriod covector anchor
    have hVector := vector.contMDiff anchor
    rw [contMDiffAt_section] at hVector
    have hRankOne :
        ContMDiffAt throatCoverModelWithCorners
          𝓘(Real, ModelEndomorphism) ∞
          (fun current =>
            (throatCovectorCoordinates period hPeriod covector anchor current)
              |>.smulRight
                ((trivializationAt ModelTangent
                  (TangentFiber period hPeriod) anchor)
                  ⟨current, vector current⟩).2) anchor :=
      (contDiff_fst.smulRight contDiff_snd).comp_contMDiffAt
        (hCovector.prodMk_space hVector)
    apply hRankOne.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor)
    filter_upwards [hCurrent] with current hCurrent'
    apply ContinuousLinearMap.ext
    intro input
    rw [ContinuousLinearMap.inCoordinates_eq hCurrent' hCurrent']
    simp only [ContinuousLinearMap.smulRight_apply]
    rw [throatCovectorCoordinates_apply period hPeriod covector anchor current
      hCurrent' input]
    simp [ContinuousLinearMap.comp_apply]

@[simp]
theorem smoothThroatCovectorVectorRankOne_apply
    (covector : SmoothCovectorSection period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (input : TangentFiber period hPeriod point) :
    smoothThroatCovectorVectorRankOne period hPeriod covector vector point input =
      covector point input • vector point :=
  rfl

/-- Smooth section of intrinsic redundant-frame operators. -/
def intrinsicThroatFiniteFrameOperatorSection
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    SmoothEndomorphismSection period hPeriod :=
  ∑ index : Fin frame.count,
    smoothThroatCovectorVectorRankOne period hPeriod
      (P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D.throatMetricFrameCovector
        period hPeriod frame
          (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 index)
      (smoothThroatFrameVectorSection period hPeriod frame index)

/-- Intrinsic finite-frame operator
`u ↦ ∑ i, g(vᵢ,u) vᵢ` on one throat tangent fiber. -/
def intrinsicThroatFiniteFrameOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  intrinsicThroatFiniteFrameOperatorSection period hPeriod frame point

@[simp]
theorem intrinsicThroatFiniteFrameOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameOperator period hPeriod frame point vector =
      ∑ index : Fin frame.count,
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
            point (frame.vectorAt point index) vector •
          frame.vectorAt point index := by
  classical
  have hSum (indices : Finset (Fin frame.count)) :
      ((∑ index ∈ indices,
          smoothThroatCovectorVectorRankOne period hPeriod
            (P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D.throatMetricFrameCovector
              period hPeriod frame
                (intrinsicSmoothNondegenerateThroatMetric
                  period hPeriod).1 index)
            (smoothThroatFrameVectorSection
              period hPeriod frame index)) point) vector =
        ∑ index ∈ indices,
          (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
              point (frame.vectorAt point index) vector •
            frame.vectorAt point index := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hIndex hInduction =>
        simp [Finset.sum_insert, hIndex, hInduction,
          smoothThroatCovectorVectorRankOne_apply]
  simpa [intrinsicThroatFiniteFrameOperator,
    intrinsicThroatFiniteFrameOperatorSection] using hSum Finset.univ

/-- Spanning and nondegeneracy make the intrinsic frame operator injective. -/
theorem intrinsicThroatFiniteFrameOperator_injective
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    Function.Injective
      (intrinsicThroatFiniteFrameOperator period hPeriod frame point) := by
  let metric :=
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1
  let operator :=
    intrinsicThroatFiniteFrameOperator period hPeriod frame point
  have hKernel (vector : TangentFiber period hPeriod point)
      (hVector : operator vector = 0) : vector = 0 := by
    have hEnergy :
        (∑ index : Fin frame.count,
          (metric.tensor point (frame.vectorAt point index) vector) ^ 2) = 0 := by
      calc
        (∑ index : Fin frame.count,
            (metric.tensor point (frame.vectorAt point index) vector) ^ 2) =
            metric.tensor point vector
              (∑ index : Fin frame.count,
                metric.tensor point (frame.vectorAt point index) vector •
                  frame.vectorAt point index) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro index _
              rw [map_smul]
              change
                (metric.tensor point
                    (frame.vectorAt point index) vector) ^ 2 =
                  metric.tensor point (frame.vectorAt point index) vector *
                    metric.tensor point vector (frame.vectorAt point index)
              rw [metric.symmetric point vector (frame.vectorAt point index)]
              ring
        _ = metric.tensor point vector (operator vector) := by
              rw [intrinsicThroatFiniteFrameOperator_apply]
        _ = 0 := by rw [hVector]; simp
    have hReading (index : Fin frame.count) :
        metric.tensor point (frame.vectorAt point index) vector = 0 := by
      have hSquare :
          (metric.tensor point (frame.vectorAt point index) vector) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => sq_nonneg _)).mp hEnergy index (Finset.mem_univ index)
      exact sq_eq_zero_iff.mp hSquare
    have hFlatLinear :
        (metric.tensor point vector).toLinearMap = 0 := by
      apply LinearMap.ext_on_range (frame.spansAt point)
      intro index
      change metric.tensor point vector (frame.vectorAt point index) = 0
      rw [metric.symmetric point vector (frame.vectorAt point index)]
      exact hReading index
    have hFlat : metric.tensor point vector = 0 := by
      apply ContinuousLinearMap.ext
      intro input
      exact LinearMap.congr_fun hFlatLinear input
    apply (intrinsicSmoothNondegenerateThroatMetric period hPeriod).2 point
    simpa using hFlat
  intro first second hEqual
  apply sub_eq_zero.mp
  apply hKernel (first - second)
  rw [map_sub, hEqual, sub_self]

/-- In finite dimension the injective intrinsic frame operator is bijective. -/
theorem intrinsicThroatFiniteFrameOperator_bijective
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    Function.Bijective
      (intrinsicThroatFiniteFrameOperator period hPeriod frame point) := by
  have hInjective := intrinsicThroatFiniteFrameOperator_injective
    period hPeriod frame point
  exact ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩

/-- Continuous linear equivalence defined by the redundant frame operator. -/
def intrinsicThroatFiniteFrameOperatorEquiv
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod point :=
  (LinearEquiv.ofBijective
    (intrinsicThroatFiniteFrameOperator
      period hPeriod frame point).toLinearMap
    (intrinsicThroatFiniteFrameOperator_bijective
      period hPeriod frame point)).toContinuousLinearEquiv

@[simp]
theorem intrinsicThroatFiniteFrameOperatorEquiv_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameOperatorEquiv period hPeriod frame point vector =
      intrinsicThroatFiniteFrameOperator period hPeriod frame point vector :=
  rfl

theorem intrinsicThroatFiniteFrameOperator_isInvertible
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (intrinsicThroatFiniteFrameOperator
      period hPeriod frame point).IsInvertible := by
  exact ⟨intrinsicThroatFiniteFrameOperatorEquiv
    period hPeriod frame point, rfl⟩

private def throatEndomorphismCoordinates
    (endomorphism : SmoothEndomorphismSection period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) :
    ModelEndomorphism :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod)
    ModelTangent (TangentFiber period hPeriod)
    anchor current anchor current (endomorphism current)

private theorem throatEndomorphismCoordinates_contMDiffAt
    (endomorphism : SmoothEndomorphismSection period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ModelEndomorphism) ∞
      (throatEndomorphismCoordinates period hPeriod endomorphism anchor)
      anchor := by
  have hSmooth := endomorphism.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem intrinsicThroatFiniteFrameOperatorCoordinates_isInvertible
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    (throatEndomorphismCoordinates period hPeriod
      (intrinsicThroatFiniteFrameOperatorSection period hPeriod frame)
      anchor anchor).IsInvertible := by
  have hFiber : anchor ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor
  unfold throatEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hFiber hFiber]
  change
    ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real anchor hFiber).toContinuousLinearMap.comp
      ((intrinsicThroatFiniteFrameOperatorEquiv
        period hPeriod frame anchor).toContinuousLinearMap.comp
        ((trivializationAt ModelTangent
              (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real anchor hFiber).symm.toContinuousLinearMap) |>.IsInvertible
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private theorem inverseIntrinsicThroatFiniteFrameCoordinates_apply_eq
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet) :
    (throatEndomorphismCoordinates period hPeriod
      (intrinsicThroatFiniteFrameOperatorSection period hPeriod frame)
      anchor current).inverse
        ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor)
          ⟨current, vector current⟩).2 =
      ((trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor)
        ⟨current,
          (intrinsicThroatFiniteFrameOperator
            period hPeriod frame current).inverse (vector current)⟩).2 := by
  unfold throatEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hCurrent]
  change
    (((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hCurrent).toContinuousLinearMap.comp
      ((intrinsicThroatFiniteFrameOperatorEquiv
        period hPeriod frame current).toContinuousLinearMap.comp
        ((trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real current hCurrent).symm.toContinuousLinearMap)).inverse
      (((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hCurrent) (vector current)) = _
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_symm]
  rw [show
    (intrinsicThroatFiniteFrameOperator
      period hPeriod frame current).inverse =
        (intrinsicThroatFiniteFrameOperatorEquiv
          period hPeriod frame current).symm.toContinuousLinearMap by
    change
      ((intrinsicThroatFiniteFrameOperatorEquiv
        period hPeriod frame current).toContinuousLinearMap).inverse = _
    exact ContinuousLinearMap.inverse_equiv _]
  rfl

/-- Smooth solution of the intrinsic finite-frame reconstruction equation. -/
def intrinsicThroatFiniteFrameSolve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothTangentSection period hPeriod where
  toFun := fun point =>
    (intrinsicThroatFiniteFrameOperator
      period hPeriod frame point).inverse (vector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_section]
    have hOperator := throatEndomorphismCoordinates_contMDiffAt
      period hPeriod
      (intrinsicThroatFiniteFrameOperatorSection period hPeriod frame) anchor
    have hInverse :=
      (intrinsicThroatFiniteFrameOperatorCoordinates_isInvertible
        period hPeriod frame anchor
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hOperator
    have hVector := vector.contMDiff anchor
    rw [contMDiffAt_section] at hVector
    have hFormula := hInverse.clm_apply hVector
    apply hFormula.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor)
    filter_upwards [hCurrent] with current hCurrent'
    exact (inverseIntrinsicThroatFiniteFrameCoordinates_apply_eq
      period hPeriod frame vector anchor current hCurrent').symm

@[simp]
theorem intrinsicThroatFiniteFrameSolve_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatFiniteFrameSolve period hPeriod frame vector point =
      (intrinsicThroatFiniteFrameOperator
        period hPeriod frame point).inverse (vector point) :=
  rfl

theorem intrinsicThroatFiniteFrameOperator_solve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatFiniteFrameOperator period hPeriod frame point
        (intrinsicThroatFiniteFrameSolve
          period hPeriod frame vector point) =
      vector point := by
  exact (intrinsicThroatFiniteFrameOperator_isInvertible
    period hPeriod frame point).self_apply_inverse (vector point)

/-- Canonical coefficient covector associated with one redundant generator. -/
def intrinsicThroatFiniteFrameCoefficientAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    TangentFiber period hPeriod point →L[Real] Real :=
  ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
      (frame.vectorAt point index)).comp
    (intrinsicThroatFiniteFrameOperator
      period hPeriod frame point).inverse

@[simp]
theorem intrinsicThroatFiniteFrameCoefficientAt_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count)
    (vector : TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameCoefficientAt
        period hPeriod frame point index vector =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
        (frame.vectorAt point index)
        ((intrinsicThroatFiniteFrameOperator
          period hPeriod frame point).inverse vector) :=
  rfl

/-- A canonical coefficient evaluated after the frame operator recovers the
corresponding intrinsic metric component. -/
theorem intrinsicThroatFiniteFrameCoefficientAt_operator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count)
    (vector : TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameCoefficientAt period hPeriod frame point index
        (intrinsicThroatFiniteFrameOperator period hPeriod frame point
          vector) =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        point (frame.vectorAt point index) vector := by
  rw [intrinsicThroatFiniteFrameCoefficientAt_apply,
    (intrinsicThroatFiniteFrameOperator_isInvertible
      period hPeriod frame point).inverse_apply_self]

/-- Smooth canonical coefficient of a smooth tangent section. -/
def intrinsicThroatFiniteFrameCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (index : Fin frame.count) :
    SmoothThroatField period hPeriod Real where
  toFun := fun point =>
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
      (frame.vectorAt point index)
      (intrinsicThroatFiniteFrameSolve
        period hPeriod frame vector point)
  contMDiff_toFun := by
    have hApplied :=
      (intrinsicSmoothNondegenerateThroatMetric
        period hPeriod).1.tensor.contMDiff.clm_bundle_apply₂
          (frame.contMDiff_vector index)
          (intrinsicThroatFiniteFrameSolve
            period hPeriod frame vector).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem intrinsicThroatFiniteFrameCoefficient_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatFiniteFrameCoefficient
        period hPeriod frame vector index point =
      intrinsicThroatFiniteFrameCoefficientAt
        period hPeriod frame point index (vector point) :=
  rfl

/-- Every tangent vector is reconstructed exactly from the canonical
redundant coefficients. -/
theorem intrinsicThroatFiniteFrameCoefficientAt_reconstructs
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    vector =
      ∑ index : Fin frame.count,
        intrinsicThroatFiniteFrameCoefficientAt
            period hPeriod frame point index vector •
          frame.vectorAt point index := by
  calc
    vector =
        intrinsicThroatFiniteFrameOperator period hPeriod frame point
          ((intrinsicThroatFiniteFrameOperator
            period hPeriod frame point).inverse vector) :=
      ((intrinsicThroatFiniteFrameOperator_isInvertible
        period hPeriod frame point).self_apply_inverse vector).symm
    _ = ∑ index : Fin frame.count,
          (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
              point (frame.vectorAt point index)
              ((intrinsicThroatFiniteFrameOperator
                period hPeriod frame point).inverse vector) •
            frame.vectorAt point index :=
      intrinsicThroatFiniteFrameOperator_apply period hPeriod frame point _
    _ = ∑ index : Fin frame.count,
          intrinsicThroatFiniteFrameCoefficientAt
              period hPeriod frame point index vector •
            frame.vectorAt point index := by rfl

/-- Global smooth reconstruction of a smooth tangent section. -/
theorem intrinsicThroatFiniteFrame_reconstructs
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    vector point =
      ∑ index : Fin frame.count,
        intrinsicThroatFiniteFrameCoefficient
            period hPeriod frame vector index point •
          frame.vectorAt point index := by
  rw [← intrinsicThroatFiniteFrameOperator_solve
    period hPeriod frame vector point]
  rw [intrinsicThroatFiniteFrameOperator_apply]
  rfl

/-! ## Faithful finite matrix algebra -/

/-- Synthesis by the already installed redundant throat generators. -/
def intrinsicThroatFiniteFrameSynthesisAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (Fin frame.count → Real) →ₗ[Real] TangentFiber period hPeriod point where
  toFun coefficients :=
    ∑ index : Fin frame.count,
      coefficients index • frame.vectorAt point index
  map_add' first second := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
      RingHom.id_apply]

@[simp]
theorem intrinsicThroatFiniteFrameSynthesisAt_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (coefficients : Fin frame.count → Real) :
    intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point
        coefficients =
      ∑ index : Fin frame.count,
        coefficients index • frame.vectorAt point index :=
  rfl

/-- Canonical analysis map supplied by the intrinsic throat metric. -/
def intrinsicThroatFiniteFrameAnalysisAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    TangentFiber period hPeriod point →ₗ[Real] (Fin frame.count → Real) where
  toFun vector index :=
    intrinsicThroatFiniteFrameCoefficientAt
      period hPeriod frame point index vector
  map_add' first second := by
    funext index
    exact (intrinsicThroatFiniteFrameCoefficientAt
      period hPeriod frame point index).map_add first second
  map_smul' scalar vector := by
    funext index
    exact (intrinsicThroatFiniteFrameCoefficientAt
      period hPeriod frame point index).map_smul scalar vector

/-- Analysis followed by synthesis reconstructs every tangent vector. -/
theorem intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point).comp
        (intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point) =
      LinearMap.id := by
  apply LinearMap.ext
  intro vector
  exact (intrinsicThroatFiniteFrameCoefficientAt_reconstructs
    period hPeriod frame point vector).symm

abbrev IntrinsicThroatFiniteFrameMatrix
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  Matrix (Fin frame.count) (Fin frame.count) Real

/-- Faithful redundant matrix of a throat endomorphism. -/
def intrinsicThroatFiniteFrameEndomorphismMatrixAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    IntrinsicThroatFiniteFrameMatrix period hPeriod frame :=
  redundantFiniteFrameEncoding
    (intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point)
    (intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point)
    endomorphism

@[simp]
theorem intrinsicThroatFiniteFrameEndomorphismMatrixAt_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point)
    (row column : Fin frame.count) :
    intrinsicThroatFiniteFrameEndomorphismMatrixAt
        period hPeriod frame point endomorphism row column =
      intrinsicThroatFiniteFrameCoefficientAt period hPeriod frame point row
        (endomorphism (frame.vectorAt point column)) := by
  classical
  simp [intrinsicThroatFiniteFrameEndomorphismMatrixAt,
    redundantFiniteFrameEncoding, intrinsicThroatFiniteFrameSynthesisAt,
    intrinsicThroatFiniteFrameAnalysisAt]

/-- The encoded inverse reference operator sends the readings of a genuine
covector to the canonical analysis coefficients of its raised vector. -/
theorem
    intrinsicThroatFiniteFrameEndomorphismMatrixAt_inverseOperator_mulVec
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    (intrinsicThroatFiniteFrameEndomorphismMatrixAt
        period hPeriod frame point
        ((intrinsicThroatFiniteFrameOperator period hPeriod frame point)
          |>.inverse.toLinearMap)).mulVec
        (fun index => covector (frame.vectorAt point index)) =
      intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point
        (intrinsicThroatInverseMusical period hPeriod point covector) := by
  unfold intrinsicThroatFiniteFrameEndomorphismMatrixAt
  rw [redundantFiniteFrameEncoding_mulVec]
  have hSynthesis :
      intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point
          (fun index => covector (frame.vectorAt point index)) =
        intrinsicThroatFiniteFrameOperator period hPeriod frame point
          (intrinsicThroatInverseMusical period hPeriod point covector) := by
    rw [intrinsicThroatFiniteFrameOperator_apply]
    change (∑ index : Fin frame.count,
      covector (frame.vectorAt point index) • frame.vectorAt point index) = _
    apply Finset.sum_congr rfl
    intro index _
    rw [intrinsicThroatMetric_apply_inverseMusical]
  rw [hSynthesis]
  apply congrArg
    (intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point)
  exact (intrinsicThroatFiniteFrameOperator_isInvertible
    period hPeriod frame point).inverse_apply_self _

/-- Encoding the frame operator followed by an endomorphism reads exactly the
intrinsic metric matrix of that endomorphism. -/
theorem intrinsicThroatFiniteFrameEndomorphismMatrixAt_operator_comp_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point)
    (row column : Fin frame.count) :
    intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        ((intrinsicThroatFiniteFrameOperator period hPeriod frame point
          |>.toLinearMap).comp endomorphism) row column =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
        (frame.vectorAt point row) (endomorphism (frame.vectorAt point column)) := by
  rw [intrinsicThroatFiniteFrameEndomorphismMatrixAt_apply,
    LinearMap.comp_apply]
  exact intrinsicThroatFiniteFrameCoefficientAt_operator
    period hPeriod frame point row _

/-- The faithful matrix of a bilinear form relative to the intrinsic metric
is obtained by composing its musical map with the intrinsic inverse musical. -/
theorem intrinsicThroatFiniteFrameEndomorphismMatrixAt_relativeMusical_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (bilinear : TangentFiber period hPeriod point →L[Real]
      (TangentFiber period hPeriod point →L[Real] Real))
    (row column : Fin frame.count) :
    intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        ((intrinsicThroatFiniteFrameOperator period hPeriod frame point
            |>.toLinearMap).comp
          (((intrinsicThroatInverseMusical period hPeriod point
              |>.toContinuousLinearMap).comp bilinear).toLinearMap))
        row column =
      bilinear (frame.vectorAt point column) (frame.vectorAt point row) := by
  rw [intrinsicThroatFiniteFrameEndomorphismMatrixAt_operator_comp_apply]
  exact intrinsicThroatMetric_apply_inverseMusical
    period hPeriod point _ _

/-- Projector recording the redundancy of the finite generating family. -/
def intrinsicThroatFiniteFrameProjectorMatrixAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    IntrinsicThroatFiniteFrameMatrix period hPeriod frame :=
  intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
    LinearMap.id

/-- Identity extension of an intrinsic endomorphism to the full coefficient
space. -/
def intrinsicThroatFiniteFrameLiftAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    IntrinsicThroatFiniteFrameMatrix period hPeriod frame :=
  redundantFiniteFrameLift
    (intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point)
    (intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point)
    endomorphism

/-- The faithful intrinsic lift has the advertised action after synthesis. -/
theorem intrinsicThroatFiniteFrameSynthesisAt_liftAt_mulVec
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point)
    (coefficients : Fin frame.count → Real) :
    intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point
        ((intrinsicThroatFiniteFrameLiftAt period hPeriod frame point
          endomorphism).mulVec coefficients) =
      endomorphism
        (intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point
          coefficients) := by
  exact redundantFiniteFrameSynthesis_lift_mulVec
    (intrinsicThroatFiniteFrameAnalysisAt period hPeriod frame point)
    (intrinsicThroatFiniteFrameSynthesisAt period hPeriod frame point)
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      period hPeriod frame point)
    endomorphism coefficients

theorem intrinsicThroatFiniteFrameEndomorphismMatrixAt_comp
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        (first.comp second) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
          period hPeriod frame point first *
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          period hPeriod frame point second :=
  redundantFiniteFrameEncoding_comp _ _
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      period hPeriod frame point) first second

/-- The encoded inverse frame operator cancels the encoded frame operator
before any intrinsic endomorphism. -/
theorem intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        (intrinsicThroatFiniteFrameOperator period hPeriod frame point
          |>.inverse.toLinearMap) *
      intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        ((intrinsicThroatFiniteFrameOperator period hPeriod frame point
          |>.toLinearMap).comp endomorphism) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt period hPeriod frame point
        endomorphism := by
  rw [← intrinsicThroatFiniteFrameEndomorphismMatrixAt_comp]
  congr 1
  apply LinearMap.ext
  intro vector
  exact (intrinsicThroatFiniteFrameOperator_isInvertible
    period hPeriod frame point).inverse_apply_self (endomorphism vector)

theorem intrinsicThroatFiniteFrameLiftAt_det
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    Matrix.det (intrinsicThroatFiniteFrameLiftAt
        period hPeriod frame point endomorphism) =
      LinearMap.det endomorphism :=
  redundantFiniteFrameLift_det _ _
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      period hPeriod frame point) endomorphism

theorem intrinsicThroatFiniteFrameEndomorphismMatrixAt_trace
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    Matrix.trace (intrinsicThroatFiniteFrameEndomorphismMatrixAt
        period hPeriod frame point endomorphism) =
      LinearMap.trace Real (TangentFiber period hPeriod point) endomorphism :=
  redundantFiniteFrameEncoding_trace _ _
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      period hPeriod frame point) endomorphism

theorem intrinsicThroatFiniteFrameLiftAt_comp
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : TangentFiber period hPeriod point →ₗ[Real]
      TangentFiber period hPeriod point) :
    intrinsicThroatFiniteFrameLiftAt period hPeriod frame point first *
        intrinsicThroatFiniteFrameLiftAt period hPeriod frame point second =
      intrinsicThroatFiniteFrameLiftAt period hPeriod frame point
        (first.comp second) :=
  redundantFiniteFrameLift_comp _ _
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      period hPeriod frame point) first second

/-- The completed GHY algebra can read determinant and trace from the global
redundant frame without postulating a global basis. -/
theorem intrinsic_throat_finite_frame_matrix_algebra_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (∀ endomorphism : TangentFiber period hPeriod point →ₗ[Real]
        TangentFiber period hPeriod point,
      Matrix.det (intrinsicThroatFiniteFrameLiftAt
          period hPeriod frame point endomorphism) =
        LinearMap.det endomorphism ∧
      Matrix.trace (intrinsicThroatFiniteFrameEndomorphismMatrixAt
          period hPeriod frame point endomorphism) =
        LinearMap.trace Real (TangentFiber period hPeriod point)
          endomorphism) ∧
    (∀ first second : TangentFiber period hPeriod point →ₗ[Real]
        TangentFiber period hPeriod point,
      intrinsicThroatFiniteFrameLiftAt period hPeriod frame point first *
          intrinsicThroatFiniteFrameLiftAt period hPeriod frame point second =
        intrinsicThroatFiniteFrameLiftAt period hPeriod frame point
          (first.comp second)) := by
  exact ⟨fun endomorphism =>
      ⟨intrinsicThroatFiniteFrameLiftAt_det
          period hPeriod frame point endomorphism,
        intrinsicThroatFiniteFrameEndomorphismMatrixAt_trace
          period hPeriod frame point endomorphism⟩,
    intrinsicThroatFiniteFrameLiftAt_comp period hPeriod frame point⟩

/-- Algebraic reconstruction gate consumed by the completed boundary jets. -/
theorem intrinsic_throat_finite_frame_reconstruction_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    Function.Bijective
        (intrinsicThroatFiniteFrameOperator period hPeriod frame point) ∧
      ∀ vector : TangentFiber period hPeriod point,
        vector =
          ∑ index : Fin frame.count,
            intrinsicThroatFiniteFrameCoefficientAt
                period hPeriod frame point index vector •
              frame.vectorAt point index :=
  ⟨intrinsicThroatFiniteFrameOperator_bijective period hPeriod frame point,
    intrinsicThroatFiniteFrameCoefficientAt_reconstructs
      period hPeriod frame point⟩

end
end P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
end JanusFormal
