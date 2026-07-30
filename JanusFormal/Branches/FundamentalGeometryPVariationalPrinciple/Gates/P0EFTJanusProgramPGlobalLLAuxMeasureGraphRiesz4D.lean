import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusThroatLinearOperationsZero4D

/-!
# Graph-Hilbert realization of the residual global LL slots

The `llAuxMetric` Hessian is a PT-averaged weighted `L2` pairing, while the
pure `llMeasure` Hessian is zero.  This file completes the two-slot smooth
core in the graph norm consisting of its raw `L2` values and the two actual
weighted auxiliary-metric features.  The resulting bounded Riesz operator
represents exactly the unchanged global LL action Hessian on the dense core.

No ellipticity, closed range, or Fredholm conclusion is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

open scoped Manifold ContDiff Topology ENNReal InnerProduct
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
open P0EFTJanusThroatLinearOperationsZero4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Smooth core of the two residual LL slots. -/
abbrev GlobalLLAuxMeasureSmooth :=
  SmoothThroatField period hPeriod LLMetricFiber ×
    SmoothThroatField period hPeriod Real

/-- Raw values retained by the graph norm, including the Hessian-null measure
slot. -/
abbrev GlobalLLAuxMeasureRawFiber :=
  WithLp 2 (LLMetricFiber × Real)

/-- The two weighted auxiliary-metric features on the direct and PT orbits. -/
abbrev GlobalLLAuxMeasureFeatureFiber :=
  WithLp 2 (LLMetricFiber × LLMetricFiber)

/-- Ambient graph fiber: raw values followed by the action features. -/
abbrev GlobalLLAuxMeasureGraphFiber :=
  WithLp 2 (GlobalLLAuxMeasureRawFiber × GlobalLLAuxMeasureFeatureFiber)

/-- Square-root weight of the direct auxiliary-metric Hessian. -/
def globalCandidateALLAuxWeight
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (point : EffectiveThroat period hPeriod) : Real :=
  Real.sqrt ((1 / 2 : Real) *
    throatDerivativeEnergy period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.boundary.llFields period hPeriod).llField point)

/-- Square-root weight of the PT auxiliary-metric Hessian. -/
def globalCandidateALLAuxPTWeight
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (point : EffectiveThroat period hPeriod) : Real :=
  Real.sqrt ((1 / 2 : Real) *
    throatDerivativeEnergy period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (throatPTPullback period hPeriod LLFieldFiber
        (data.boundary.llFields period hPeriod).llField) point)

theorem globalCandidateALLAuxWeight_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Continuous (globalCandidateALLAuxWeight period hPeriod data) := by
  exact (continuous_const.mul
    (throatDerivativeEnergy_continuous period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.boundary.llFields period hPeriod).llField)).sqrt

theorem globalCandidateALLAuxPTWeight_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Continuous (globalCandidateALLAuxPTWeight period hPeriod data) := by
  exact (continuous_const.mul
    (throatDerivativeEnergy_continuous period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (throatPTPullback period hPeriod LLFieldFiber
        (data.boundary.llFields period hPeriod).llField))).sqrt

theorem globalCandidateALLAuxWeight_sq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (point : EffectiveThroat period hPeriod) :
    globalCandidateALLAuxWeight period hPeriod data point ^ 2 =
      (1 / 2 : Real) *
        throatDerivativeEnergy period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (data.boundary.llFields period hPeriod).llField point := by
  apply Real.sq_sqrt
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem globalCandidateALLAuxPTWeight_sq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (point : EffectiveThroat period hPeriod) :
    globalCandidateALLAuxPTWeight period hPeriod data point ^ 2 =
      (1 / 2 : Real) *
        throatDerivativeEnergy period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (throatPTPullback period hPeriod LLFieldFiber
            (data.boundary.llFields period hPeriod).llField) point := by
  apply Real.sq_sqrt
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Raw values and the two square-root-weighted action features. -/
def globalCandidateALLAuxMeasureGraphFeature
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    GlobalLLAuxMeasureGraphFiber :=
  WithLp.toLp 2
    (WithLp.toLp 2 (direction.1 point, direction.2 point),
      WithLp.toLp 2
        (globalCandidateALLAuxWeight period hPeriod data point • direction.1 point,
          globalCandidateALLAuxPTWeight period hPeriod data point •
            differentialLLAuxMetricDirectionPT period hPeriod direction.1 point))

theorem globalCandidateALLAuxMeasureGraphFeature_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureSmooth period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    inner Real
        (globalCandidateALLAuxMeasureGraphFeature period hPeriod
          data first point).snd
        (globalCandidateALLAuxMeasureGraphFeature period hPeriod
          data second point).snd =
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod).llAuxMetric
        (data.boundary.llFields period hPeriod).llField
        first.1 second.1 0 0 point := by
  rw [WithLp.prod_inner_apply]
  simp only [globalCandidateALLAuxMeasureGraphFeature, WithLp.toLp_snd,
    real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← mul_assoc, ← pow_two, ← pow_two,
    globalCandidateALLAuxWeight_sq period hPeriod data point,
    globalCandidateALLAuxPTWeight_sq period hPeriod data point]
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    differentialLLKineticMixedHessianDensity
  simp [throatDerivativePairing, differentialLLFluxDirectionPT,
    differentialLLAuxMetricDirectionPT]
  ring

theorem globalCandidateALLAuxMeasureGraphFeature_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    Continuous
      (globalCandidateALLAuxMeasureGraphFeature period hPeriod data direction) := by
  have hRaw :
      Continuous (fun point =>
        WithLp.toLp 2 (direction.1 point, direction.2 point)) :=
    (WithLp.prodContinuousLinearEquiv 2 Real LLMetricFiber Real).symm.continuous.comp
      (direction.1.contMDiff_toFun.continuous.prodMk
        direction.2.contMDiff_toFun.continuous)
  have hFeature :
      Continuous (fun point =>
        WithLp.toLp 2
          (globalCandidateALLAuxWeight period hPeriod data point •
              direction.1 point,
            globalCandidateALLAuxPTWeight period hPeriod data point •
              differentialLLAuxMetricDirectionPT period hPeriod
                direction.1 point)) :=
    (WithLp.prodContinuousLinearEquiv 2 Real LLMetricFiber
      LLMetricFiber).symm.continuous.comp
        ((globalCandidateALLAuxWeight_continuous period hPeriod data).smul
          direction.1.contMDiff_toFun.continuous |>.prodMk
        ((globalCandidateALLAuxPTWeight_continuous period hPeriod data).smul
          (differentialLLAuxMetricDirectionPT period hPeriod
            direction.1).contMDiff_toFun.continuous))
  exact
    (WithLp.prodContinuousLinearEquiv 2 Real GlobalLLAuxMeasureRawFiber
      GlobalLLAuxMeasureFeatureFiber).symm.continuous.comp
        (hRaw.prodMk hFeature)

theorem globalCandidateALLAuxMeasureGraphFeature_memLp
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    MemLp (globalCandidateALLAuxMeasureGraphFeature period hPeriod data direction)
      (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (globalCandidateALLAuxMeasureGraphFeature_continuous period hPeriod data direction
    ).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Smooth graph feature as an element of the ambient Hilbert `L2`. -/
def globalCandidateALLAuxMeasureGraphToL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (globalCandidateALLAuxMeasureGraphFeature_memLp period hPeriod data direction).toLp
    (globalCandidateALLAuxMeasureGraphFeature period hPeriod data direction)

theorem globalCandidateALLAuxMeasureGraphToL2_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data direction :
        EffectiveThroat period hPeriod → GlobalLLAuxMeasureGraphFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      globalCandidateALLAuxMeasureGraphFeature period hPeriod data direction :=
  (globalCandidateALLAuxMeasureGraphFeature_memLp period hPeriod data direction).coeFn_toLp

theorem globalCandidateALLAuxMeasureGraphFeature_add
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureSmooth period hPeriod) :
    globalCandidateALLAuxMeasureGraphFeature period hPeriod data (first + second) =
      globalCandidateALLAuxMeasureGraphFeature period hPeriod data first +
        globalCandidateALLAuxMeasureGraphFeature period hPeriod data second := by
  funext point
  have hAux :
      (first + second).1.toFun point =
        first.1.toFun point + second.1.toFun point := rfl
  have hMeasure :
      (first + second).2.toFun point =
        first.2.toFun point + second.2.toFun point := rfl
  have hPT :
      differentialLLAuxMetricDirectionPT period hPeriod
          (first + second).1 point =
        differentialLLAuxMetricDirectionPT period hPeriod first.1 point +
          differentialLLAuxMetricDirectionPT period hPeriod second.1 point := rfl
  unfold globalCandidateALLAuxMeasureGraphFeature
  rw [hAux, hMeasure, hPT, smul_add, smul_add]
  change WithLp.toLp 2
      (WithLp.toLp 2
          (first.1 point + second.1 point, first.2 point + second.2 point),
        WithLp.toLp 2
          (globalCandidateALLAuxWeight period hPeriod data point • first.1 point +
              globalCandidateALLAuxWeight period hPeriod data point • second.1 point,
            globalCandidateALLAuxPTWeight period hPeriod data point •
                differentialLLAuxMetricDirectionPT period hPeriod first.1 point +
              globalCandidateALLAuxPTWeight period hPeriod data point •
                differentialLLAuxMetricDirectionPT period hPeriod second.1 point)) =
    WithLp.toLp 2
      (WithLp.toLp 2 (first.1 point, first.2 point),
        WithLp.toLp 2
          (globalCandidateALLAuxWeight period hPeriod data point • first.1 point,
            globalCandidateALLAuxPTWeight period hPeriod data point •
              differentialLLAuxMetricDirectionPT period hPeriod first.1 point)) +
    WithLp.toLp 2
      (WithLp.toLp 2 (second.1 point, second.2 point),
        WithLp.toLp 2
          (globalCandidateALLAuxWeight period hPeriod data point • second.1 point,
            globalCandidateALLAuxPTWeight period hPeriod data point •
              differentialLLAuxMetricDirectionPT period hPeriod second.1 point))
  rfl

theorem globalCandidateALLAuxMeasureGraphFeature_smul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (scalar : Real) (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    globalCandidateALLAuxMeasureGraphFeature period hPeriod data
        (scalar • direction) =
      scalar • globalCandidateALLAuxMeasureGraphFeature period hPeriod
        data direction := by
  funext point
  change globalCandidateALLAuxMeasureGraphFeature period hPeriod data
      (scalar • direction) point =
    scalar • globalCandidateALLAuxMeasureGraphFeature period hPeriod
      data direction point
  have hAux :
      (scalar • direction).1.toFun point =
        scalar • direction.1.toFun point := rfl
  have hMeasure :
      (scalar • direction).2.toFun point =
        scalar • direction.2.toFun point := rfl
  have hPT :
      differentialLLAuxMetricDirectionPT period hPeriod
          (scalar • direction).1 point =
        scalar • differentialLLAuxMetricDirectionPT period hPeriod
          direction.1 point := rfl
  unfold globalCandidateALLAuxMeasureGraphFeature
  rw [hAux, hMeasure, hPT, smul_smul, smul_smul]
  rw [mul_comm (globalCandidateALLAuxWeight period hPeriod data point) scalar,
    mul_comm (globalCandidateALLAuxPTWeight period hPeriod data point) scalar]
  rw [← smul_smul scalar
      (globalCandidateALLAuxWeight period hPeriod data point)
      (direction.1 point),
    ← smul_smul scalar
      (globalCandidateALLAuxPTWeight period hPeriod data point)
      (differentialLLAuxMetricDirectionPT period hPeriod direction.1 point)]
  rfl

/-- Linear smooth-core graph inclusion into ambient `L2`. -/
def globalCandidateALLAuxMeasureGraphL2LinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalLLAuxMeasureSmooth period hPeriod →ₗ[Real]
      Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := globalCandidateALLAuxMeasureGraphToL2 period hPeriod data
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data (first + second),
       globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data first,
       globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data second,
       Lp.coeFn_add
        (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data first)
        (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data second)]
      with point hSum hFirst hSecond hAdd
    rw [hSum, hAdd]
    simp only [Pi.add_apply]
    rw [hFirst, hSecond]
    exact congrFun
      (globalCandidateALLAuxMeasureGraphFeature_add period hPeriod data first second)
      point
  map_smul' scalar direction := by
    apply Lp.ext
    filter_upwards
      [globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data
        (scalar • direction),
       globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data direction,
       Lp.coeFn_smul scalar
        (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data direction)]
      with point hScaled hDirection hSmul
    rw [hScaled]
    simp only [RingHom.id_apply]
    rw [hSmul]
    simp only [Pi.smul_apply]
    rw [hDirection]
    exact congrFun
      (globalCandidateALLAuxMeasureGraphFeature_smul period hPeriod data
        scalar direction) point

/-- Closed graph completion of the genuine two-slot smooth core. -/
def globalCandidateALLAuxMeasureGraphSubmodule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Submodule Real
      (Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :=
  (LinearMap.range
    (globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data)
    ).topologicalClosure

/-- Hilbert graph completion of `llAuxMetric × llMeasure`. -/
abbrev GlobalLLAuxMeasureGraphHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :=
  globalCandidateALLAuxMeasureGraphSubmodule period hPeriod data

/-- Canonical smooth inclusion into the graph completion. -/
def globalCandidateALLAuxMeasureSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalLLAuxMeasureSmooth period hPeriod →ₗ[Real]
      GlobalLLAuxMeasureGraphHilbert period hPeriod data where
  toFun direction :=
    ⟨globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data direction,
      (LinearMap.range
        (globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data)
          direction)⟩
  map_add' first second := Subtype.ext
    ((globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data).map_add
      first second)
  map_smul' scalar direction := Subtype.ext
    ((globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data).map_smul
      scalar direction)

theorem globalCandidateALLAuxMeasureSmoothEmbedding_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    DenseRange
      (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalLLAuxMeasureGraphHilbert
  unfold globalCandidateALLAuxMeasureGraphSubmodule
  let graph :=
    globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data) =
        (LinearMap.range graph : Set
          (Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨direction, rfl⟩, rfl⟩
      exact ⟨direction, rfl⟩
    · rintro ⟨direction, rfl⟩
      exact
        ⟨globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data direction,
          ⟨direction, rfl⟩, rfl⟩
  change closure (LinearMap.range graph : Set
      (Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data))
  rw [hRange]

theorem globalCandidateALLAuxMeasureSmoothEmbedding_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Function.Injective
      (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data) := by
  intro first second hEqual
  have hL2 :
      globalCandidateALLAuxMeasureGraphToL2 period hPeriod data first =
        globalCandidateALLAuxMeasureGraphToL2 period hPeriod data second :=
    congrArg Subtype.val hEqual
  have hCoe :
      ((globalCandidateALLAuxMeasureGraphToL2 period hPeriod data first :
          Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
        EffectiveThroat period hPeriod → GlobalLLAuxMeasureGraphFiber) =
      ((globalCandidateALLAuxMeasureGraphToL2 period hPeriod data second :
          Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
        EffectiveThroat period hPeriod → GlobalLLAuxMeasureGraphFiber) :=
    congrArg
      (fun value :
        Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =>
        (value : EffectiveThroat period hPeriod →
          GlobalLLAuxMeasureGraphFiber)) hL2
  have hCoeAE :
      ((globalCandidateALLAuxMeasureGraphToL2 period hPeriod data first :
          Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
        EffectiveThroat period hPeriod → GlobalLLAuxMeasureGraphFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      ((globalCandidateALLAuxMeasureGraphToL2 period hPeriod data second :
          Lp GlobalLLAuxMeasureGraphFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
        EffectiveThroat period hPeriod → GlobalLLAuxMeasureGraphFiber) :=
    Filter.Eventually.of_forall fun point => congrFun hCoe point
  have hGraphAE :
      globalCandidateALLAuxMeasureGraphFeature period hPeriod data first =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        globalCandidateALLAuxMeasureGraphFeature period hPeriod data second :=
    (globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data first).symm.trans
      (hCoeAE.trans
        (globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data second))
  have hRawAE :
      (fun point : EffectiveThroat period hPeriod =>
        (first.1 point, first.2 point)) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (fun point : EffectiveThroat period hPeriod =>
        (second.1 point, second.2 point)) := by
    filter_upwards [hGraphAE] with point hPoint
    exact congrArg
      (fun value : GlobalLLAuxMeasureGraphFiber =>
        (value.fst.fst, value.fst.snd)) hPoint
  have hRaw :
      (fun point : EffectiveThroat period hPeriod =>
        (first.1 point, first.2 point)) =
      (fun point : EffectiveThroat period hPeriod =>
        (second.1 point, second.2 point)) :=
    Measure.eq_of_ae_eq hRawAE
      (first.1.contMDiff_toFun.continuous.prodMk
        first.2.contMDiff_toFun.continuous)
      (second.1.contMDiff_toFun.continuous.prodMk
        second.2.contMDiff_toFun.continuous)
  apply Prod.ext
  · apply SmoothThroatField.ext period hPeriod LLMetricFiber
    intro point
    exact congrArg Prod.fst (congrFun hRaw point)
  · apply SmoothThroatField.ext period hPeriod Real
    intro point
    exact congrArg Prod.snd (congrFun hRaw point)

@[implicit_reducible]
def globalCandidateALLAuxMeasureGraphCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) := by
  unfold GlobalLLAuxMeasureGraphHilbert
  unfold globalCandidateALLAuxMeasureGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateALLAuxMeasureGraphL2LinearMap period hPeriod data))

/-- Continuous projection onto the two actual weighted Hessian features. -/
def globalCandidateALLAuxMeasureFeatureProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalLLAuxMeasureGraphHilbert period hPeriod data →L[Real]
      Lp GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((WithLp.sndL 2 Real GlobalLLAuxMeasureRawFiber
      GlobalLLAuxMeasureFeatureFiber).compLpL (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
    (globalCandidateALLAuxMeasureGraphSubmodule period hPeriod data).subtypeL

theorem globalCandidateALLAuxMeasureFeatureProjection_smooth_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    ((globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
            data direction) :
        Lp GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalLLAuxMeasureFeatureFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (fun point =>
        (globalCandidateALLAuxMeasureGraphFeature period hPeriod
          data direction point).snd) := by
  have hProjection :=
    (WithLp.sndL 2 Real GlobalLLAuxMeasureRawFiber
      GlobalLLAuxMeasureFeatureFiber).coeFn_compLpL
        (p := (2 : ENNReal))
        (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data direction)
  have hGraph :=
    globalCandidateALLAuxMeasureGraphToL2_ae period hPeriod data direction
  filter_upwards [hProjection, hGraph] with point hProjection hGraph
  change
    (((WithLp.sndL 2 Real GlobalLLAuxMeasureRawFiber
        GlobalLLAuxMeasureFeatureFiber).compLpL (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateALLAuxMeasureGraphToL2 period hPeriod data direction) :
      Lp GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalLLAuxMeasureFeatureFiber) point = _
  rw [hProjection, hGraph]
  rfl

/-- The existing action has no pure measure feature: that slot is retained in
the graph norm but lies in the kernel of the Hessian projection. -/
theorem globalCandidateALLAuxMeasureFeatureProjection_pureMeasure
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data
          (0, dMeasure)) = 0 := by
  apply Lp.ext
  filter_upwards
    [globalCandidateALLAuxMeasureFeatureProjection_smooth_ae
      period hPeriod data (0, dMeasure),
     Lp.coeFn_zero GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hProjection hZero
  rw [hProjection, hZero]
  change WithLp.toLp 2
      (globalCandidateALLAuxWeight period hPeriod data point •
          SmoothThroatField.toFun
            (0 : SmoothThroatField period hPeriod LLMetricFiber) point,
        globalCandidateALLAuxPTWeight period hPeriod data point •
          differentialLLAuxMetricDirectionPT period hPeriod
            (0 : SmoothThroatField period hPeriod LLMetricFiber) point) = 0
  have hAuxZero :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLMetricFiber) point = 0 := rfl
  have hPTZero :
      differentialLLAuxMetricDirectionPT period hPeriod
        (0 : SmoothThroatField period hPeriod LLMetricFiber) point = 0 := by
    rw [show differentialLLAuxMetricDirectionPT period hPeriod
        (0 : SmoothThroatField period hPeriod LLMetricFiber) = 0 by
      unfold differentialLLAuxMetricDirectionPT
      exact throatPTPullback_zero period hPeriod LLMetricFiber]
    rfl
  rw [hAuxZero, hPTZero]
  simp

/-- Bounded Riesz operator of the residual same-action Hessian graph form. -/
def globalCandidateALLAuxMeasureGraphRieszOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalLLAuxMeasureGraphHilbert period hPeriod data →L[Real]
      GlobalLLAuxMeasureGraphHilbert period hPeriod data := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  exact
    (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint.comp
      (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data)

theorem globalCandidateALLAuxMeasureGraphRieszOperator_pureMeasure
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data
          (0, dMeasure)) = 0 := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  change
    (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
      (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data
          (0, dMeasure))) = 0
  rw [globalCandidateALLAuxMeasureFeatureProjection_pureMeasure
    period hPeriod data]
  exact map_zero _

/-- Exact total kernel: `P†P` vanishes precisely when the weighted feature
projection `P` vanishes. -/
theorem globalCandidateALLAuxMeasureGraphRieszOperator_ker_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    LinearMap.ker
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data).toLinearMap =
      LinearMap.ker
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).toLinearMap := by
  ext direction
  simp only [LinearMap.mem_ker]
  constructor
  · intro hRiesz
    letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
      globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
    change
      (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod
          data direction) = 0 at hRiesz
    have hPairing :=
      ContinuousLinearMap.adjoint_inner_left
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data)
        direction
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data direction)
    rw [hRiesz, inner_zero_left] at hPairing
    exact inner_self_eq_zero.mp hPairing.symm
  · intro hProjection
    letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
      globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
    change
      (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod
          data direction) = 0
    calc
      (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
          (globalCandidateALLAuxMeasureFeatureProjection period hPeriod
            data direction) =
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
          0 := congrArg _ hProjection
      _ = 0 := map_zero _

theorem globalCandidateALLAuxMeasureGraphRieszOperator_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureGraphHilbert period hPeriod data) :
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data first)
        second =
      inner Real first
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod
          data second) := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  change inner Real
      ((globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data first))
      second =
    inner Real first
      ((globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data second))
  calc
    _ = inner Real
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data first)
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data second) :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner Real
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data second)
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data first) :=
      real_inner_comm _ _
    _ = inner Real
        ((globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
          (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data second))
        first :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = _ := real_inner_comm _ _

/-- Pure-measure inclusion into the two-slot smooth core. -/
def globalCandidateALLPureMeasureDirection
    (period : Real) (hPeriod : period ≠ 0) :
    SmoothThroatField period hPeriod Real →ₗ[Real]
      GlobalLLAuxMeasureSmooth period hPeriod where
  toFun := fun dMeasure => (0, dMeasure)
  map_add' := fun _ _ => by simp
  map_smul' := fun _ _ => by simp

/-- Linear inclusion of smooth pure-measure directions into the graph
completion. -/
def globalCandidateALLPureMeasureSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    SmoothThroatField period hPeriod Real →ₗ[Real]
      GlobalLLAuxMeasureGraphHilbert period hPeriod data :=
  (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data).comp
    (globalCandidateALLPureMeasureDirection period hPeriod)

/-- Closed measure-radical generated by the actual smooth measure slot. -/
def globalCandidateALLPureMeasureKernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Submodule Real (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
  (LinearMap.range
    (globalCandidateALLPureMeasureSmoothEmbedding period hPeriod data)
    ).topologicalClosure

theorem globalCandidateALLPureMeasureKernel_isClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    IsClosed
      (globalCandidateALLPureMeasureKernel period hPeriod data :
        Set (GlobalLLAuxMeasureGraphHilbert period hPeriod data)) :=
  Submodule.isClosed_topologicalClosure _

/-- The entire closed pure-measure radical is contained in the exact total
kernel. Equality is not asserted because zero auxiliary weights may enlarge
the kernel. -/
theorem globalCandidateALLPureMeasureKernel_le_rieszKernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    globalCandidateALLPureMeasureKernel period hPeriod data ≤
      LinearMap.ker
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · rintro direction ⟨dMeasure, rfl⟩
    apply LinearMap.mem_ker.mpr
    simpa [globalCandidateALLPureMeasureSmoothEmbedding,
      globalCandidateALLPureMeasureDirection] using
      (globalCandidateALLAuxMeasureGraphRieszOperator_pureMeasure
        period hPeriod data dMeasure)
  · exact
      (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data).isClosed_ker

/-- Hilbert quotient by exactly the closed pure-measure radical.  No
auxiliary-metric zero mode is removed here. -/
abbrev GlobalLLAuxMeasureActionQuotient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :=
  let _ : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  let _ : IsClosed
      (globalCandidateALLPureMeasureKernel period hPeriod data :
        Set (GlobalLLAuxMeasureGraphHilbert period hPeriod data)) :=
    globalCandidateALLPureMeasureKernel_isClosed period hPeriod data
  GlobalLLAuxMeasureGraphHilbert period hPeriod data ⧸
    globalCandidateALLPureMeasureKernel period hPeriod data

/-- The unchanged Riesz operator descends through the measure radical and is
then projected to the same quotient. -/
def globalCandidateALLAuxMeasureActionQuotientOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalLLAuxMeasureActionQuotient period hPeriod data →L[Real]
      GlobalLLAuxMeasureActionQuotient period hPeriod data := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : IsClosed
      (globalCandidateALLPureMeasureKernel period hPeriod data :
        Set (GlobalLLAuxMeasureGraphHilbert period hPeriod data)) :=
    globalCandidateALLPureMeasureKernel_isClosed period hPeriod data
  let descended :
      GlobalLLAuxMeasureActionQuotient period hPeriod data →L[Real]
        GlobalLLAuxMeasureGraphHilbert period hPeriod data :=
    (globalCandidateALLPureMeasureKernel period hPeriod data).liftQL
      (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data)
      (globalCandidateALLPureMeasureKernel_le_rieszKernel
        period hPeriod data)
  exact
    (globalCandidateALLPureMeasureKernel period hPeriod data).mkQL.comp descended

/-- Action-faithful descent: on every representative the quotient operator is
exactly the quotient class of the unchanged graph Riesz operator. -/
theorem globalCandidateALLAuxMeasureActionQuotientOperator_mk
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalLLAuxMeasureGraphHilbert period hPeriod data) :
    globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod data
        ((globalCandidateALLPureMeasureKernel period hPeriod data).mkQ direction) =
      (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod
          data direction) := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : IsClosed
      (globalCandidateALLPureMeasureKernel period hPeriod data :
        Set (GlobalLLAuxMeasureGraphHilbert period hPeriod data)) :=
    globalCandidateALLPureMeasureKernel_isClosed period hPeriod data
  simp [globalCandidateALLAuxMeasureActionQuotientOperator,
    Submodule.liftQL_apply]

/-- The measure quotient is nondegenerate exactly when pure-measure
directions exhaust the total weighted-feature kernel.  This is the first
obstruction before any closed-range/Fredholm question. -/
theorem globalCandidateALLAuxMeasureActionQuotientOperator_injective_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Function.Injective
        (globalCandidateALLAuxMeasureActionQuotientOperator
          period hPeriod data) ↔
      globalCandidateALLPureMeasureKernel period hPeriod data =
        LinearMap.ker
          (globalCandidateALLAuxMeasureGraphRieszOperator
            period hPeriod data).toLinearMap := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : IsClosed
      (globalCandidateALLPureMeasureKernel period hPeriod data :
        Set (GlobalLLAuxMeasureGraphHilbert period hPeriod data)) :=
    globalCandidateALLPureMeasureKernel_isClosed period hPeriod data
  constructor
  · intro hInjective
    apply le_antisymm
    · exact globalCandidateALLPureMeasureKernel_le_rieszKernel
        period hPeriod data
    · intro direction hKernel
      have hQuotientImage :
          globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod data
              ((globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
                direction) = 0 := by
        rw [globalCandidateALLAuxMeasureActionQuotientOperator_mk
          period hPeriod data direction]
        have hOperatorZero := LinearMap.mem_ker.mp hKernel
        exact congrArg
          (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
          hOperatorZero
      have hQuotientZero :
          (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
            direction = 0 := by
        apply hInjective
        calc
          globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod data
              ((globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
                direction) = 0 := hQuotientImage
          _ = globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod
              data 0 :=
            (globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod
              data).map_zero.symm
      have hMkKernel :
          direction ∈ LinearMap.ker
            (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ :=
        LinearMap.mem_ker.mpr hQuotientZero
      simpa only [Submodule.ker_mkQ] using hMkKernel
  · intro hKernelExact
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro quotientDirection hQuotientKernel
      obtain ⟨direction, rfl⟩ :=
        Submodule.Quotient.mk_surjective
          (globalCandidateALLPureMeasureKernel period hPeriod data)
          quotientDirection
      have hQuotientImage :
          (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
            (globalCandidateALLAuxMeasureGraphRieszOperator
              period hPeriod data direction) = 0 := by
        have hOperatorZero := LinearMap.mem_ker.mp hQuotientKernel
        calc
          (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
              (globalCandidateALLAuxMeasureGraphRieszOperator
                period hPeriod data direction) =
            globalCandidateALLAuxMeasureActionQuotientOperator period hPeriod
              data ((globalCandidateALLPureMeasureKernel period hPeriod data).mkQ
                direction) :=
            (globalCandidateALLAuxMeasureActionQuotientOperator_mk
              period hPeriod data direction).symm
          _ = 0 := hOperatorZero
      have hImageInMeasure :
          globalCandidateALLAuxMeasureGraphRieszOperator
              period hPeriod data direction ∈
            globalCandidateALLPureMeasureKernel period hPeriod data := by
        rw [← Submodule.ker_mkQ
          (globalCandidateALLPureMeasureKernel period hPeriod data)]
        exact LinearMap.mem_ker.mpr hQuotientImage
      have hSecondImage :
          globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
              (globalCandidateALLAuxMeasureGraphRieszOperator
                period hPeriod data direction) = 0 := by
        rw [hKernelExact] at hImageInMeasure
        exact LinearMap.mem_ker.mp hImageInMeasure
      have hSymmetry :=
        globalCandidateALLAuxMeasureGraphRieszOperator_symmetric
          period hPeriod data direction
            (globalCandidateALLAuxMeasureGraphRieszOperator
              period hPeriod data direction)
      rw [hSecondImage, inner_zero_right] at hSymmetry
      have hImageZero :
          globalCandidateALLAuxMeasureGraphRieszOperator
            period hPeriod data direction = 0 :=
        inner_self_eq_zero.mp hSymmetry
      have hDirectionInMeasure :
          direction ∈ globalCandidateALLPureMeasureKernel period hPeriod data := by
        rw [hKernelExact]
        exact LinearMap.mem_ker.mpr hImageZero
      rw [Submodule.mem_bot]
      have hMkKernel :
          direction ∈ LinearMap.ker
            (globalCandidateALLPureMeasureKernel period hPeriod data).mkQ := by
        simpa only [Submodule.ker_mkQ] using hDirectionInMeasure
      exact LinearMap.mem_ker.mp hMkKernel
    · exact bot_le

/-- Riesz identity for the continuous residual graph pairing. -/
theorem globalCandidateALLAuxMeasureGraphRieszOperator_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureGraphHilbert period hPeriod data) :
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data first)
        second =
      inner Real
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data first)
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data second) := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  change inner Real
      ((globalCandidateALLAuxMeasureFeatureProjection period hPeriod data).adjoint
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data first))
      second = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem globalCandidateALLAuxMeasureHessian_eq_auxDensityIntegral
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureSmooth period hPeriod) :
    globalCandidateALLAuxMeasureHessian period hPeriod data
        first.1 second.1 first.2 second.2 =
      ∫ point, ptSymmetricDifferentialLLKineticMixedHessianDensity
        period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod).llAuxMetric
        (data.boundary.llFields period hPeriod).llField
        first.1 second.1 0 0 point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have zeroLL_apply (point : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLFieldFiber) point = 0 := rfl
  unfold globalCandidateALLAuxMeasureHessian fullLLHessian
    globalPTFullLLHessianForm globalPTDifferentialLLKineticMixedHessian
    globalPTLLWorldvolumeHessian ptLLWorldvolumeHessianDensity
    llWorldvolumeHessianDensity fullDirectionLLVariation
  simp [ptAverage, zeroLL_apply]

/-- On the dense smooth core, the continuous feature pairing is exactly the
same-action auxiliary-metric/measure Hessian. -/
theorem globalCandidateALLAuxMeasureFeatureProjection_smooth_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureSmooth period hPeriod) :
    inner Real
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
            data first))
        (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
            data second)) =
      globalCandidateALLAuxMeasureHessian period hPeriod data
        first.1 second.1 first.2 second.2 := by
  rw [L2.inner_def,
    globalCandidateALLAuxMeasureHessian_eq_auxDensityIntegral
      period hPeriod data first second]
  apply integral_congr_ae
  filter_upwards
    [globalCandidateALLAuxMeasureFeatureProjection_smooth_ae
      period hPeriod data first,
     globalCandidateALLAuxMeasureFeatureProjection_smooth_ae
      period hPeriod data second]
    with point hFirst hSecond
  rw [hFirst, hSecond]
  exact globalCandidateALLAuxMeasureGraphFeature_inner
    period hPeriod data first second point

/-- The bounded graph Riesz operator represents the exact unchanged global
LL Hessian on the injective dense smooth core. -/
theorem globalCandidateALLAuxMeasureGraphRieszOperator_smooth_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (first second : GlobalLLAuxMeasureSmooth period hPeriod) :
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
            data first))
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
          data second) =
      globalCandidateALLAuxMeasureHessian period hPeriod data
        first.1 second.1 first.2 second.2 := by
  rw [globalCandidateALLAuxMeasureGraphRieszOperator_pairing
    period hPeriod data]
  exact globalCandidateALLAuxMeasureFeatureProjection_smooth_inner
    period hPeriod data first second

end
end P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
end JanusFormal
