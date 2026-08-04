import Mathlib.Analysis.Matrix.Normed
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

/-!
# Global finite-frame coefficients for the intrinsic Candidate-A root

The effective D8 quotient need not admit a global tangent basis.  The already
constructed finite smooth spanning family nevertheless has a canonical smooth
dual reconstruction once one background Lorentz metric is fixed.  The frame
operator

`F(u) = ∑ i, g(vᵢ,u) vᵢ`

is injective because `g(u,F(u))` is the sum of the squares `g(vᵢ,u)²`;
finite dimensionality makes it invertible.  Its smooth inverse gives global
smooth redundant coefficients, exact reconstruction, and hence an honest
finite-matrix encoding of the intrinsic Candidate-A root.  No global frame or
new geometric assumption is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Bundle ContinuousLinearMap Filter Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D

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

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev SmoothTangentSection :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (TangentFiber period hPeriod)

private abbrev SmoothCovectorSection :=
  ContMDiffSection coverModelWithCorners
    (CoverCoordinates →L[Real] Real) ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentFiber period hPeriod point →L[Real] Real)

private abbrev SmoothEndomorphismSection :=
  ContMDiffSection coverModelWithCorners
    (CoverCoordinates →L[Real] CoverCoordinates) ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentFiber period hPeriod point →L[Real]
        TangentFiber period hPeriod point)

private abbrev ModelTangent := CoverCoordinates
private abbrev ModelCovector := ModelTangent →L[Real] Real
private abbrev ModelEndomorphism := ModelTangent →L[Real] ModelTangent

local instance tangentFiberFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- One member of a smooth finite spanning family, packaged as a genuine
smooth tangent section. -/
def smoothFrameVectorSection
    (frame : SmoothD8Frame period hPeriod)
    (index : Fin frame.count) :
    SmoothTangentSection period hPeriod where
  toFun := fun point => frame.vectorAt point index
  contMDiff_toFun := frame.contMDiff_vector index

@[simp]
theorem smoothFrameVectorSection_apply
    (frame : SmoothD8Frame period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    smoothFrameVectorSection period hPeriod frame index point =
      frame.vectorAt point index :=
  rfl

private def covectorCoordinates
    (covector : SmoothCovectorSection period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) : ModelCovector :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod)
    Real (fun _ : EffectiveQuotient period hPeriod => Real)
    anchor current anchor current (covector current)

private theorem covectorCoordinates_contMDiffAt
    (covector : SmoothCovectorSection period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, ModelCovector) ∞
      (covectorCoordinates period hPeriod covector anchor) anchor := by
  have hSmooth := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem covectorCoordinates_apply
    (covector : SmoothCovectorSection period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet)
    (vector : ModelTangent) :
    covectorCoordinates period hPeriod covector anchor current vector =
      covector current
        ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).symm current vector) := by
  unfold covectorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp

/-- A smooth covector-vector outer product as a smooth endomorphism section. -/
def smoothCovectorVectorRankOne
    (covector : SmoothCovectorSection period hPeriod)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothEndomorphismSection period hPeriod where
  toFun := fun point => (covector point).smulRight (vector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hCovector := covectorCoordinates_contMDiffAt
      period hPeriod covector anchor
    have hVector := vector.contMDiff anchor
    rw [contMDiffAt_section] at hVector
    have hRankOne :
        ContMDiffAt coverModelWithCorners
          𝓘(Real, ModelEndomorphism) ∞
          (fun current =>
            (covectorCoordinates period hPeriod covector anchor current).smulRight
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
    rw [covectorCoordinates_apply period hPeriod covector anchor current
      hCurrent' input]
    simp [ContinuousLinearMap.comp_apply]

@[simp]
theorem smoothCovectorVectorRankOne_apply
    (covector : SmoothCovectorSection period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (input : TangentFiber period hPeriod point) :
    smoothCovectorVectorRankOne period hPeriod covector vector point input =
      covector point input • vector point :=
  rfl

/-- The intrinsic finite-frame operator `u ↦ ∑ i, g(vᵢ,u) vᵢ`. -/
def generalMetricFiniteFrameOperator
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothEndomorphismSection period hPeriod :=
  ∑ index : Fin frame.count,
    smoothCovectorVectorRankOne period hPeriod
      (generalMetricFrameCovector period hPeriod frame metric.tensor index)
      (smoothFrameVectorSection period hPeriod frame index)

@[simp]
theorem generalMetricFiniteFrameOperator_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameOperator period hPeriod frame metric point vector =
      ∑ index : Fin frame.count,
        metric.tensor.tensor point (frame.vectorAt point index) vector •
          frame.vectorAt point index := by
  classical
  have hSum (indices : Finset (Fin frame.count)) :
      ((∑ index ∈ indices,
          smoothCovectorVectorRankOne period hPeriod
            (generalMetricFrameCovector
              period hPeriod frame metric.tensor index)
            (smoothFrameVectorSection period hPeriod frame index)) point) vector =
        ∑ index ∈ indices,
          metric.tensor.tensor point (frame.vectorAt point index) vector •
            frame.vectorAt point index := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hIndex hInduction =>
        simp [Finset.sum_insert, hIndex, hInduction,
          smoothCovectorVectorRankOne_apply]
        change
          metric.tensor.tensor point (frame.vectorAt point index) vector •
              frame.vectorAt point index =
            metric.tensor.tensor point (frame.vectorAt point index) vector •
              frame.vectorAt point index
        rfl
  simpa [generalMetricFiniteFrameOperator] using hSum Finset.univ

/-- The finite-frame operator has trivial kernel.  This is the key point that
replaces any global-frame assumption. -/
theorem generalMetricFiniteFrameOperator_injective
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (generalMetricFiniteFrameOperator period hPeriod frame metric point) := by
  let operator :=
    generalMetricFiniteFrameOperator period hPeriod frame metric point
  have hKernel (vector : TangentFiber period hPeriod point)
      (hVector : operator vector = 0) : vector = 0 := by
    have hEnergy :
        (∑ index : Fin frame.count,
          (metric.tensor.tensor point (frame.vectorAt point index) vector) ^ 2) =
            0 := by
      calc
        (∑ index : Fin frame.count,
            (metric.tensor.tensor point (frame.vectorAt point index) vector) ^ 2) =
            metric.tensor.tensor point vector
              (∑ index : Fin frame.count,
                metric.tensor.tensor point (frame.vectorAt point index) vector •
                  frame.vectorAt point index) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro index _
              rw [map_smul]
              change
                (metric.tensor.tensor point
                    (frame.vectorAt point index) vector) ^ 2 =
                  metric.tensor.tensor point
                      (frame.vectorAt point index) vector *
                    metric.tensor.tensor point vector
                      (frame.vectorAt point index)
              rw [metric.tensor.symmetric point vector
                (frame.vectorAt point index)]
              ring
        _ = metric.tensor.tensor point vector (operator vector) := by
              rw [generalMetricFiniteFrameOperator_apply]
        _ = 0 := by rw [hVector]; simp
    have hReading (index : Fin frame.count) :
        metric.tensor.tensor point (frame.vectorAt point index) vector = 0 := by
      have hSquare :
          (metric.tensor.tensor point
            (frame.vectorAt point index) vector) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => sq_nonneg _)).mp hEnergy index (Finset.mem_univ index)
      exact sq_eq_zero_iff.mp hSquare
    have hFlatLinear :
        (metric.musical point vector).toLinearMap = 0 := by
      apply LinearMap.ext_on_range (frame.spansAt point)
      intro index
      change metric.musical point vector
        (frame.vectorAt point index) = 0
      have hMusical :
          metric.musical point vector (frame.vectorAt point index) =
            metric.tensor.tensor point vector
              (frame.vectorAt point index) := by
        have hFirst := DFunLike.congr_fun
          (metric.musical_eq_tensor point) vector
        exact DFunLike.congr_fun hFirst (frame.vectorAt point index)
      rw [hMusical, metric.tensor.symmetric point vector
        (frame.vectorAt point index)]
      exact hReading index
    have hFlat : metric.musical point vector = 0 := by
      apply ContinuousLinearMap.ext
      intro input
      exact LinearMap.congr_fun hFlatLinear input
    exact (metric.musical point).injective (by simpa using hFlat)
  intro first second hEqual
  apply sub_eq_zero.mp
  apply hKernel (first - second)
  rw [map_sub, hEqual, sub_self]

/-- In finite dimension the injective frame operator is bijective. -/
theorem generalMetricFiniteFrameOperator_bijective
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Function.Bijective
      (generalMetricFiniteFrameOperator period hPeriod frame metric point) := by
  let operator :=
    generalMetricFiniteFrameOperator period hPeriod frame metric point
  have hInjective : Function.Injective operator :=
    generalMetricFiniteFrameOperator_injective
      period hPeriod frame metric point
  refine ⟨hInjective, ?_⟩
  exact (LinearMap.injective_iff_surjective.mp hInjective)

/-- Pointwise continuous linear equivalence supplied by the canonical finite
spanning-family operator. -/
def generalMetricFiniteFrameOperatorEquiv
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod point :=
  (LinearEquiv.ofBijective
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric point).toLinearMap
    (generalMetricFiniteFrameOperator_bijective
      period hPeriod frame metric point)).toContinuousLinearEquiv

@[simp]
theorem generalMetricFiniteFrameOperatorEquiv_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameOperatorEquiv
        period hPeriod frame metric point vector =
      generalMetricFiniteFrameOperator
        period hPeriod frame metric point vector :=
  rfl

theorem generalMetricFiniteFrameOperator_isInvertible
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric point).IsInvertible := by
  exact ⟨generalMetricFiniteFrameOperatorEquiv
    period hPeriod frame metric point, rfl⟩

private def endomorphismCoordinates
    (endomorphism : SmoothEndomorphismSection period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelEndomorphism :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod)
    ModelTangent (TangentFiber period hPeriod)
    anchor current anchor current (endomorphism current)

private theorem endomorphismCoordinates_contMDiffAt
    (endomorphism : SmoothEndomorphismSection period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners
      𝓘(Real, ModelEndomorphism) ∞
      (endomorphismCoordinates period hPeriod endomorphism anchor) anchor := by
  have hSmooth := endomorphism.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem finiteFrameOperatorCoordinates_isInvertible
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    (endomorphismCoordinates period hPeriod
      (generalMetricFiniteFrameOperator period hPeriod frame metric)
      anchor anchor).IsInvertible := by
  have hFiber : anchor ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor
  unfold endomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hFiber hFiber]
  change
    ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real anchor hFiber).toContinuousLinearMap.comp
      ((generalMetricFiniteFrameOperatorEquiv
        period hPeriod frame metric anchor).toContinuousLinearMap.comp
        ((trivializationAt ModelTangent
              (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real anchor hFiber).symm.toContinuousLinearMap) |>.IsInvertible
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private theorem inverseFiniteFrameCoordinates_apply_eq
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet) :
    (endomorphismCoordinates period hPeriod
      (generalMetricFiniteFrameOperator period hPeriod frame metric)
      anchor current).inverse
        ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor)
          ⟨current, vector current⟩).2 =
      ((trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor)
        ⟨current,
          (generalMetricFiniteFrameOperator
            period hPeriod frame metric current).inverse (vector current)⟩).2 := by
  unfold endomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hCurrent]
  change
    (((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hCurrent).toContinuousLinearMap.comp
      ((generalMetricFiniteFrameOperatorEquiv
        period hPeriod frame metric current).toContinuousLinearMap.comp
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
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric current).inverse =
        (generalMetricFiniteFrameOperatorEquiv
          period hPeriod frame metric current).symm.toContinuousLinearMap by
    change
      ((generalMetricFiniteFrameOperatorEquiv
        period hPeriod frame metric current).toContinuousLinearMap).inverse = _
    exact ContinuousLinearMap.inverse_equiv _]
  rfl

/-- Smooth inverse of the canonical finite-frame operator.  This packages the
inverse already used by `generalMetricFiniteFrameSolve` as a reusable bundle
endomorphism; it adds no frame choice. -/
def generalMetricFiniteFrameInverseOperator
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothEndomorphismSection period hPeriod where
  toFun := fun point =>
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric point).inverse
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hOperator := endomorphismCoordinates_contMDiffAt
      period hPeriod
      (generalMetricFiniteFrameOperator period hPeriod frame metric) anchor
    have hInverse :=
      (finiteFrameOperatorCoordinates_isInvertible
        period hPeriod frame metric anchor
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hOperator
    apply hInverse.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor)
    filter_upwards [hCurrent] with current hCurrent'
    unfold endomorphismCoordinates
    rw [ContinuousLinearMap.inCoordinates_eq hCurrent' hCurrent']
    symm
    simp only [Function.comp_apply]
    rw [ContinuousLinearMap.inCoordinates_eq hCurrent' hCurrent']
    change
      (((trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real current hCurrent').toContinuousLinearMap.comp
        ((generalMetricFiniteFrameOperatorEquiv
          period hPeriod frame metric current).toContinuousLinearMap.comp
          ((trivializationAt ModelTangent
              (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
            Real current hCurrent').symm.toContinuousLinearMap)).inverse = _
    rw [ContinuousLinearMap.inverse_equiv_comp,
      ContinuousLinearMap.inverse_comp_equiv]
    change _ =
      ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hCurrent').toContinuousLinearMap.comp
        ((generalMetricFiniteFrameOperator
          period hPeriod frame metric current).inverse.comp
          ((trivializationAt ModelTangent
              (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
            Real current hCurrent').symm.toContinuousLinearMap)
    rw [show
      (generalMetricFiniteFrameOperator
        period hPeriod frame metric current).inverse =
          (generalMetricFiniteFrameOperatorEquiv
            period hPeriod frame metric current).symm.toContinuousLinearMap by
      change
        ((generalMetricFiniteFrameOperatorEquiv
          period hPeriod frame metric current).toContinuousLinearMap).inverse = _
      exact ContinuousLinearMap.inverse_equiv _]
    simp only [ContinuousLinearMap.inverse_equiv,
      ContinuousLinearEquiv.symm_symm]
    exact ContinuousLinearMap.comp_assoc _ _ _

@[simp]
theorem generalMetricFiniteFrameInverseOperator_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameInverseOperator
        period hPeriod frame metric point vector =
      (generalMetricFiniteFrameOperator
        period hPeriod frame metric point).inverse vector :=
  rfl

/-- Solve the finite-frame reconstruction equation smoothly for any smooth
tangent section. -/
def generalMetricFiniteFrameSolve
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothTangentSection period hPeriod where
  toFun := fun point =>
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric point).inverse (vector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_section]
    have hOperator := endomorphismCoordinates_contMDiffAt
      period hPeriod
      (generalMetricFiniteFrameOperator period hPeriod frame metric) anchor
    have hInverse :=
      (finiteFrameOperatorCoordinates_isInvertible
        period hPeriod frame metric anchor
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
    exact (inverseFiniteFrameCoordinates_apply_eq
      period hPeriod frame metric vector anchor current hCurrent').symm

@[simp]
theorem generalMetricFiniteFrameSolve_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricFiniteFrameSolve period hPeriod frame metric vector point =
      (generalMetricFiniteFrameOperator
        period hPeriod frame metric point).inverse (vector point) :=
  rfl

theorem generalMetricFiniteFrameOperator_solve
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricFiniteFrameOperator period hPeriod frame metric point
        (generalMetricFiniteFrameSolve
          period hPeriod frame metric vector point) =
      vector point := by
  exact (generalMetricFiniteFrameOperator_isInvertible
    period hPeriod frame metric point).self_apply_inverse (vector point)

/-- Canonical pointwise dual coefficient associated with the redundant smooth
spanning family. -/
def generalMetricFiniteFrameCoefficientAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin frame.count) :
    TangentFiber period hPeriod point →L[Real] Real :=
  (metric.tensor.tensor point (frame.vectorAt point index)).comp
    (generalMetricFiniteFrameOperator
      period hPeriod frame metric point).inverse

@[simp]
theorem generalMetricFiniteFrameCoefficientAt_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin frame.count)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point index vector =
      metric.tensor.tensor point (frame.vectorAt point index)
        ((generalMetricFiniteFrameOperator
          period hPeriod frame metric point).inverse vector) :=
  rfl

/-- Every smooth tangent section has global smooth coefficients in the
canonical redundant dual frame. -/
def generalMetricFiniteFrameCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (index : Fin frame.count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    metric.tensor.tensor point (frame.vectorAt point index)
      (generalMetricFiniteFrameSolve
        period hPeriod frame metric vector point)
  contMDiff_toFun := by
    have hApplied := metric.tensor.tensor.contMDiff.clm_bundle_apply₂
      (frame.contMDiff_vector index)
      (generalMetricFiniteFrameSolve
        period hPeriod frame metric vector).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem generalMetricFiniteFrameCoefficient_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricFiniteFrameCoefficient
        period hPeriod frame metric vector index point =
      generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point index (vector point) :=
  rfl

/-- Exact global reconstruction from the smooth redundant coefficients. -/
theorem generalMetricFiniteFrame_reconstructs
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    vector point =
      ∑ index : Fin frame.count,
        generalMetricFiniteFrameCoefficient
            period hPeriod frame metric vector index point •
          frame.vectorAt point index := by
  rw [← generalMetricFiniteFrameOperator_solve
    period hPeriod frame metric vector point]
  rw [generalMetricFiniteFrameOperator_apply]
  rfl

/-- Pointwise reconstruction, without first packaging the vector as a smooth
section. -/
theorem generalMetricFiniteFrameCoefficientAt_reconstructs
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    vector =
      ∑ index : Fin frame.count,
        generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point index vector •
          frame.vectorAt point index := by
  calc
    vector =
        generalMetricFiniteFrameOperator period hPeriod frame metric point
          ((generalMetricFiniteFrameOperator
            period hPeriod frame metric point).inverse vector) :=
      ((generalMetricFiniteFrameOperator_isInvertible
        period hPeriod frame metric point).self_apply_inverse vector).symm
    _ = ∑ index : Fin frame.count,
          metric.tensor.tensor point (frame.vectorAt point index)
              ((generalMetricFiniteFrameOperator
                period hPeriod frame metric point).inverse vector) •
            frame.vectorAt point index :=
      generalMetricFiniteFrameOperator_apply
        period hPeriod frame metric point _
    _ = ∑ index : Fin frame.count,
          generalMetricFiniteFrameCoefficientAt
              period hPeriod frame metric point index vector •
            frame.vectorAt point index := by rfl

/-! ## Faithful redundant matrix encoding -/

abbrev FiniteFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  Matrix (Fin frame.count) (Fin frame.count) Real

@[reducible] local instance finiteFrameMatrixNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) :
    NormedAddCommGroup (FiniteFrameMatrix period hPeriod frame) :=
  Matrix.normedAddCommGroup

local instance finiteFrameMatrixAddCommGroup
    (frame : SmoothD8Frame period hPeriod) :
    AddCommGroup (FiniteFrameMatrix period hPeriod frame) :=
  (finiteFrameMatrixNormedAddCommGroup period hPeriod frame).toAddCommGroup

local instance finiteFrameMatrixPseudoMetricSpace
    (frame : SmoothD8Frame period hPeriod) :
    PseudoMetricSpace (FiniteFrameMatrix period hPeriod frame) :=
  (finiteFrameMatrixNormedAddCommGroup
    period hPeriod frame).toPseudoMetricSpace

local instance finiteFrameMatrixUniformSpace
    (frame : SmoothD8Frame period hPeriod) :
    UniformSpace (FiniteFrameMatrix period hPeriod frame) :=
  (finiteFrameMatrixPseudoMetricSpace
    period hPeriod frame).toUniformSpace

local instance finiteFrameMatrixTopologicalSpace
    (frame : SmoothD8Frame period hPeriod) :
    TopologicalSpace (FiniteFrameMatrix period hPeriod frame) :=
  (finiteFrameMatrixUniformSpace
    period hPeriod frame).toTopologicalSpace

@[reducible] local instance finiteFrameMatrixNormedSpace
    (frame : SmoothD8Frame period hPeriod) :
    NormedSpace Real (FiniteFrameMatrix period hPeriod frame) :=
  Matrix.normedSpace

/-- Pointwise matrix encoding of an intrinsic tangent endomorphism in the
canonical redundant dual frame. -/
def finiteFrameEndomorphismMatrixAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :
    FiniteFrameMatrix period hPeriod frame :=
  fun row column =>
    generalMetricFiniteFrameCoefficientAt
      period hPeriod frame metric point row
        (endomorphism (frame.vectorAt point column))

@[simp]
theorem finiteFrameEndomorphismMatrixAt_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point)
    (row column : Fin frame.count) :
    finiteFrameEndomorphismMatrixAt
        period hPeriod frame metric point endomorphism row column =
      generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point row
          (endomorphism (frame.vectorAt point column)) :=
  rfl

/-- Matrix multiplication is exactly intrinsic endomorphism composition,
despite the redundant finite spanning family. -/
theorem finiteFrameEndomorphismMatrixAt_comp
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :
    finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
        (first.comp second) =
      finiteFrameEndomorphismMatrixAt period hPeriod frame metric point first *
      finiteFrameEndomorphismMatrixAt
          period hPeriod frame metric point second := by
  ext row column
  change
    generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point row
        (first (second (frame.vectorAt point column))) =
      ∑ index,
        generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point row
            (first (frame.vectorAt point index)) *
          generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point index
            (second (frame.vectorAt point column))
  have hReconstruct :=
    generalMetricFiniteFrameCoefficientAt_reconstructs
      period hPeriod frame metric point
        (second (frame.vectorAt point column))
  calc
    generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point row
        (first (second (frame.vectorAt point column))) =
      generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point row
        (first (∑ index : Fin frame.count,
          generalMetricFiniteFrameCoefficientAt
              period hPeriod frame metric point index
              (second (frame.vectorAt point column)) •
            frame.vectorAt point index)) := by rw [← hReconstruct]
    _ = ∑ index,
        generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point row
            (first (frame.vectorAt point index)) *
          generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point index
            (second (frame.vectorAt point column)) := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro index _
      ring

/-- The redundant matrix encoding remains faithful because the generators
span every tangent fiber. -/
theorem finiteFrameEndomorphismMatrixAt_injective
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (finiteFrameEndomorphismMatrixAt
        period hPeriod frame metric point) := by
  intro first second hMatrix
  have hLinear : first.toLinearMap = second.toLinearMap := by
    apply LinearMap.ext_on_range (frame.spansAt point)
    intro column
    have hColumn (row : Fin frame.count) :
        generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point row
            (first (frame.vectorAt point column)) =
          generalMetricFiniteFrameCoefficientAt
            period hPeriod frame metric point row
            (second (frame.vectorAt point column)) := by
      exact congrFun (congrFun hMatrix row) column
    calc
      first (frame.vectorAt point column) =
          ∑ row : Fin frame.count,
            generalMetricFiniteFrameCoefficientAt
                period hPeriod frame metric point row
                (first (frame.vectorAt point column)) •
              frame.vectorAt point row :=
        generalMetricFiniteFrameCoefficientAt_reconstructs
          period hPeriod frame metric point _
      _ = ∑ row : Fin frame.count,
            generalMetricFiniteFrameCoefficientAt
                period hPeriod frame metric point row
                (second (frame.vectorAt point column)) •
              frame.vectorAt point row := by
        apply Finset.sum_congr rfl
        intro row _
        rw [hColumn row]
      _ = second (frame.vectorAt point column) :=
        (generalMetricFiniteFrameCoefficientAt_reconstructs
          period hPeriod frame metric point _).symm
  apply ContinuousLinearMap.ext
  intro vector
  exact LinearMap.congr_fun hLinear vector

/-- The identity endomorphism is represented by a projector, not generally by
the identity matrix: this records the finite-frame redundancy explicitly. -/
def finiteFrameProjectorMatrixAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FiniteFrameMatrix period hPeriod frame :=
  finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
    (ContinuousLinearMap.id Real (TangentFiber period hPeriod point))

theorem finiteFrameProjectorMatrixAt_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectorMatrixAt period hPeriod frame metric point *
        finiteFrameProjectorMatrixAt period hPeriod frame metric point =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point := by
  unfold finiteFrameProjectorMatrixAt
  rw [← finiteFrameEndomorphismMatrixAt_comp]
  apply congrArg
    (finiteFrameEndomorphismMatrixAt period hPeriod frame metric point)
  ext vector
  rfl

theorem finiteFrameEndomorphismMatrixAt_left_projector
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :
    finiteFrameProjectorMatrixAt period hPeriod frame metric point *
        finiteFrameEndomorphismMatrixAt
          period hPeriod frame metric point endomorphism =
      finiteFrameEndomorphismMatrixAt
        period hPeriod frame metric point endomorphism := by
  unfold finiteFrameProjectorMatrixAt
  rw [← finiteFrameEndomorphismMatrixAt_comp]
  apply congrArg
    (finiteFrameEndomorphismMatrixAt period hPeriod frame metric point)
  ext vector
  rfl

theorem finiteFrameEndomorphismMatrixAt_right_projector
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :
    finiteFrameEndomorphismMatrixAt
          period hPeriod frame metric point endomorphism *
        finiteFrameProjectorMatrixAt period hPeriod frame metric point =
      finiteFrameEndomorphismMatrixAt
        period hPeriod frame metric point endomorphism := by
  unfold finiteFrameProjectorMatrixAt
  rw [← finiteFrameEndomorphismMatrixAt_comp]
  apply congrArg
    (finiteFrameEndomorphismMatrixAt period hPeriod frame metric point)
  ext vector
  rfl

/-- Smooth scalar coefficients of the redundant-frame projector. -/
def finiteFrameProjectorCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (row column : Fin frame.count) :
    SmoothQuotientField period hPeriod Real :=
  generalMetricFiniteFrameCoefficient period hPeriod frame metric
    (smoothFrameVectorSection period hPeriod frame column) row

@[simp]
theorem finiteFrameProjectorCoefficient_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (row column : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectorCoefficient
        period hPeriod frame metric row column point =
      generalMetricFiniteFrameCoefficientAt
        period hPeriod frame metric point row
          (frame.vectorAt point column) := by
  rw [finiteFrameProjectorCoefficient,
    generalMetricFiniteFrameCoefficient_apply]
  rfl

/-- The exact redundant-frame projector as a globally smooth matrix field. -/
def finiteFrameProjectorMatrix
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothQuotientField period hPeriod
      (FiniteFrameMatrix period hPeriod frame) where
  toFun := fun point row column =>
    finiteFrameProjectorCoefficient
      period hPeriod frame metric row column point
  contMDiff_toFun := by
    have hExpansion :
        ContMDiff coverModelWithCorners
          (modelWithCornersSelf Real
            (FiniteFrameMatrix period hPeriod frame)) ∞
          (fun point =>
            ∑ row : Fin frame.count, ∑ column : Fin frame.count,
              finiteFrameProjectorCoefficient
                  period hPeriod frame metric row column point •
                Matrix.single row column (1 : Real)) := by
      apply ContMDiff.sum
      intro row _
      apply ContMDiff.sum
      intro column _
      exact (finiteFrameProjectorCoefficient
        period hPeriod frame metric row column).contMDiff_toFun.smul
          contMDiff_const
    exact hExpansion.congr fun point => by
      simpa using
        (Matrix.matrix_eq_sum_single
          (fun row column =>
            finiteFrameProjectorCoefficient
              period hPeriod frame metric row column point))

@[simp]
theorem finiteFrameProjectorMatrix_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectorMatrix period hPeriod frame metric point =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point := by
  ext row column
  exact finiteFrameProjectorCoefficient_apply
    period hPeriod frame metric row column point

/-! ## Candidate-A root field -/

/-- Smooth root action on one member of the finite spanning family. -/
def globalCandidateARootFrameVectorSection
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (column : Fin frame.count) :
    SmoothTangentSection period hPeriod :=
  geometry.rootOperator
    (smoothFrameVectorSection period hPeriod frame column)

@[simp]
theorem globalCandidateARootFrameVectorSection_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (column : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    globalCandidateARootFrameVectorSection
        period hPeriod geometry frame column point =
      geometry.rootAt point (frame.vectorAt point column) := by
  exact geometry.rootOperator_apply
    (smoothFrameVectorSection period hPeriod frame column) point

/-- One globally smooth coefficient of the intrinsic Candidate-A root. -/
def globalCandidateAFiniteFrameRootCoefficient
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (row column : Fin frame.count) :
    SmoothQuotientField period hPeriod Real :=
  generalMetricFiniteFrameCoefficient period hPeriod frame geometry.plusMetric
    (globalCandidateARootFrameVectorSection
      period hPeriod geometry frame column) row

@[simp]
theorem globalCandidateAFiniteFrameRootCoefficient_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (row column : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    globalCandidateAFiniteFrameRootCoefficient
        period hPeriod geometry frame row column point =
      generalMetricFiniteFrameCoefficientAt
        period hPeriod frame geometry.plusMetric point row
          (geometry.rootAt point (frame.vectorAt point column)) := by
  rw [globalCandidateAFiniteFrameRootCoefficient]
  rw [generalMetricFiniteFrameCoefficient_apply]
  rw [globalCandidateARootFrameVectorSection_apply]

/-- The intrinsic root as a genuine globally smooth finite matrix field.  Its
size is the existing finite generator count, not a fictitious global rank-four
frame. -/
def globalCandidateAFiniteFrameRootMatrix
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    SmoothQuotientField period hPeriod
      (FiniteFrameMatrix period hPeriod frame) where
  toFun := fun point row column =>
    globalCandidateAFiniteFrameRootCoefficient
      period hPeriod geometry frame row column point
  contMDiff_toFun := by
    have hExpansion :
        ContMDiff coverModelWithCorners
          (modelWithCornersSelf Real
            (FiniteFrameMatrix period hPeriod frame)) ∞
          (fun point =>
            ∑ row : Fin frame.count, ∑ column : Fin frame.count,
              globalCandidateAFiniteFrameRootCoefficient
                  period hPeriod geometry frame row column point •
                Matrix.single row column (1 : Real)) := by
      apply ContMDiff.sum
      intro row _
      apply ContMDiff.sum
      intro column _
      exact (globalCandidateAFiniteFrameRootCoefficient
        period hPeriod geometry frame row column).contMDiff_toFun.smul
          contMDiff_const
    exact hExpansion.congr fun point => by
      simpa using
        (Matrix.matrix_eq_sum_single
          (fun row column =>
            globalCandidateAFiniteFrameRootCoefficient
              period hPeriod geometry frame row column point))

@[simp]
theorem globalCandidateAFiniteFrameRootMatrix_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalCandidateAFiniteFrameRootMatrix
        period hPeriod geometry frame point =
      finiteFrameEndomorphismMatrixAt period hPeriod frame
        geometry.plusMetric point (geometry.rootAt point) := by
  ext row column
  exact globalCandidateAFiniteFrameRootCoefficient_apply
    period hPeriod geometry frame row column point

/-- Exact reconstruction of the intrinsic root action from its globally smooth
redundant matrix coefficients. -/
theorem globalCandidateAFiniteFrameRootMatrix_reconstructs
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (column : Fin frame.count) :
    geometry.rootAt point (frame.vectorAt point column) =
      ∑ row : Fin frame.count,
        globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point row column •
          frame.vectorAt point row := by
  rw [globalCandidateAFiniteFrameRootMatrix_apply]
  exact generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod frame geometry.plusMetric point _

/-- The encoded intrinsic root satisfies the exact encoded square identity. -/
theorem globalCandidateAFiniteFrameRootMatrix_sq
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalCandidateAFiniteFrameRootMatrix period hPeriod geometry frame point *
        globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point =
      finiteFrameEndomorphismMatrixAt period hPeriod frame
        geometry.plusMetric point
          (relativeEndomorphismAt period hPeriod geometry.plusMetric
            geometry.minusMetric point) := by
  rw [globalCandidateAFiniteFrameRootMatrix_apply]
  rw [← finiteFrameEndomorphismMatrixAt_comp]
  rw [geometry.root_square point]

/-- The encoded intrinsic root lies in the exact projector corner determined
by the redundant finite frame. -/
theorem globalCandidateAFiniteFrameRootMatrix_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectorMatrixAt
          period hPeriod frame geometry.plusMetric point *
        globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point =
      globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point ∧
    globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point *
        finiteFrameProjectorMatrixAt
          period hPeriod frame geometry.plusMetric point =
      globalCandidateAFiniteFrameRootMatrix
        period hPeriod geometry frame point := by
  rw [globalCandidateAFiniteFrameRootMatrix_apply]
  exact ⟨finiteFrameEndomorphismMatrixAt_left_projector
      period hPeriod frame geometry.plusMetric point (geometry.rootAt point),
    finiteFrameEndomorphismMatrixAt_right_projector
      period hPeriod frame geometry.plusMetric point (geometry.rootAt point)⟩

/-! ## Canonical finite-generator specialization -/

/-- Canonical globally smooth redundant matrix field for any intrinsic
Candidate-A geometry, using the already constructed finite tangent
generators. -/
def canonicalGlobalCandidateARootMatrix
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    SmoothQuotientField period hPeriod
      (FiniteFrameMatrix period hPeriod
        (finiteSmoothTangentFrame period hPeriod)) :=
  globalCandidateAFiniteFrameRootMatrix period hPeriod geometry
    (finiteSmoothTangentFrame period hPeriod)

/-- Final intrinsic-to-matrix bridge: the canonical coefficient field is
smooth, reconstructs the root on every generator, satisfies the exact square
identity, and belongs to the exact projector corner. -/
theorem canonical_global_candidate_a_finite_frame_root_bridge
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    (∀ point,
      canonicalGlobalCandidateARootMatrix period hPeriod geometry point *
          canonicalGlobalCandidateARootMatrix period hPeriod geometry point =
        finiteFrameEndomorphismMatrixAt period hPeriod
          (finiteSmoothTangentFrame period hPeriod) geometry.plusMetric point
          (relativeEndomorphismAt period hPeriod geometry.plusMetric
            geometry.minusMetric point)) ∧
    (∀ point,
      finiteFrameProjectorMatrixAt period hPeriod
            (finiteSmoothTangentFrame period hPeriod) geometry.plusMetric point *
          canonicalGlobalCandidateARootMatrix period hPeriod geometry point =
        canonicalGlobalCandidateARootMatrix period hPeriod geometry point ∧
      canonicalGlobalCandidateARootMatrix period hPeriod geometry point *
          finiteFrameProjectorMatrixAt period hPeriod
            (finiteSmoothTangentFrame period hPeriod) geometry.plusMetric point =
        canonicalGlobalCandidateARootMatrix period hPeriod geometry point) ∧
    (∀ point column,
      geometry.rootAt point
          ((finiteSmoothTangentFrame period hPeriod).vectorAt point column) =
        ∑ row,
          canonicalGlobalCandidateARootMatrix period hPeriod geometry
              point row column •
            (finiteSmoothTangentFrame period hPeriod).vectorAt point row) := by
  exact ⟨fun point => globalCandidateAFiniteFrameRootMatrix_sq
      period hPeriod geometry (finiteSmoothTangentFrame period hPeriod) point,
    fun point => globalCandidateAFiniteFrameRootMatrix_corner
      period hPeriod geometry (finiteSmoothTangentFrame period hPeriod) point,
    fun point column => globalCandidateAFiniteFrameRootMatrix_reconstructs
      period hPeriod geometry (finiteSmoothTangentFrame period hPeriod)
        point column⟩

end

end P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
end JanusFormal
