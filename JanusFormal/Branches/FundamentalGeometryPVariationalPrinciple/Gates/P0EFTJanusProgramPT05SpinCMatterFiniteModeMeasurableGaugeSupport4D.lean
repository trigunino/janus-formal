import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterFiniteCoreMeasurableLpSupport4D

/-!
# T05 finite-mode measurable-gauge support

`ContMDiffSection` makes a section smooth as a map into the bundle total
space.  Its displayed value in `D9DoubledMatterFiber`, however, is the local
coordinate selected by `d9PrimitiveSpinCVectorBundleCore.indexAt`.  The normal
part of that selector is `normalBundleIndexAt`, defined by `Classical.choose`
from quotient surjectivity; the current API gives it no measurability theorem.
Thus total-space smoothness alone does not provide measurability of the raw
fixed-fiber coordinates used by Gate 847.

For the algebraic core it is enough to solve this gauge issue on each signed
mode separately.  This module proves that reduction: measurability of the
unit basis syntheses implies measurability of every finite synthesis, hence
the exact finite-core `Lp` support of Gate 845.  No measurable gauge selector
is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterFiniteModeMeasurableGaugeSupport4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D
open P0EFTJanusProgramPT05SpinCMatterFiniteCoreMeasurableLpSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance spinCMatterFiniteModeMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterFiniteModeBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterFiniteModeFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private theorem programPT05SpinCMatterPointwiseCoordinates_add
    (first second : Sector → D9DoubledMatterFiber) :
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector => first sector + second sector) =
      programPT05SpinCMatterPointwiseCoordinates first +
        programPT05SpinCMatterPointwiseCoordinates second := by
  classical
  apply PiLp.ext
  intro index
  have hAdd :
      d9DoubledMatterFiberHalfSpinorLinearEquiv
          (first index.1 + second index.1) =
        d9DoubledMatterFiberHalfSpinorLinearEquiv (first index.1) +
          d9DoubledMatterFiberHalfSpinorLinearEquiv (second index.1) :=
    map_add d9DoubledMatterFiberHalfSpinorLinearEquiv _ _
  by_cases hComponent : index.2.1 = (0 : Fin 2)
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.fst hAdd) index.2.2
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.snd hAdd) index.2.2

private theorem programPT05SpinCMatterPointwiseCoordinates_complexAction
    (scalar : Complex) (field : Sector → D9DoubledMatterFiber) :
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector => d9PrimitiveSpinCComplexActionCLM scalar (field sector)) =
      scalar • programPT05SpinCMatterPointwiseCoordinates field := by
  classical
  apply PiLp.ext
  intro index
  have hAction :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction
      scalar (field index.1)
  by_cases hComponent : index.2.1 = (0 : Fin 2)
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.fst hAction) index.2.2
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.snd hAction) index.2.2

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_add_apply
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        (first + second) base =
      programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base +
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base := by
  have hSynthesis := map_add
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
      period hPeriod) first second
  have hField :
      (fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (first + second) sector base) =
        fun sector =>
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              first sector base) +
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              second sector base) := by
    funext sector
    exact congrArg
      (fun state => show D9DoubledMatterFiber from state base)
      (congrFun hSynthesis sector)
  change
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector =>
          show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              (first + second) sector base) = _
  rw [hField]
  exact programPT05SpinCMatterPointwiseCoordinates_add _ _

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_smul_apply
    (scalar : Complex)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        (scalar • coefficients) base =
      scalar •
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients base := by
  have hSynthesis := map_smul
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
      period hPeriod) scalar coefficients
  have hField :
      (fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (scalar • coefficients) sector base) =
        fun sector =>
          d9PrimitiveSpinCComplexActionCLM scalar
            (show D9DoubledMatterFiber from
              programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
                coefficients sector base) := by
    funext sector
    have hEval :
        (show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (scalar • coefficients) sector base) =
          (scalar •
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              coefficients sector) base := by
      exact congrArg
        (fun state => show D9DoubledMatterFiber from state base)
        (congrFun hSynthesis sector)
    rw [hEval]
    change d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          coefficients sector) base = _
    exact d9PrimitiveSpinCComplexScalarSection_apply_complexAction
      period hPeriod .positiveQuarter scalar
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        coefficients sector) base
  change
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector =>
          show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              (scalar • coefficients) sector base) = _
  rw [hField]
  exact programPT05SpinCMatterPointwiseCoordinates_complexAction _ _

/-- The raw fixed-fiber coordinate representative is algebraically linear;
measurability is the only missing property. -/
def programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      EffectiveThroat period hPeriod →
        ProgramPT05SpinCMatterPointwiseFiber where
  toFun :=
    programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
  map_add' first second := by
    funext base
    exact programPT05SpinCMatterFiniteCorePointwiseCoordinates_add_apply
      period hPeriod first second base
  map_smul' scalar coefficients := by
    funext base
    exact programPT05SpinCMatterFiniteCorePointwiseCoordinates_smul_apply
      period hPeriod scalar coefficients base

@[simp]
theorem programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap_apply
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap
        period hPeriod coefficients =
      programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        coefficients :=
  rfl

/-- Exact remaining gauge contract, reduced to the countable signed-mode
basis rather than all finite linear combinations. -/
structure ProgramPT05SpinCMatterFiniteModeCoordinateMeasurability where
  basis_aestronglyMeasurable :
    ∀ mode : ProgramPPrimitiveSpinCMatterMode,
      AEStronglyMeasurable
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          (Finsupp.single mode 1))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Basis-mode measurability extends algebraically to every finite synthesis. -/
def ProgramPT05SpinCMatterFiniteModeCoordinateMeasurability.toFiniteCore
    (measurability :
      ProgramPT05SpinCMatterFiniteModeCoordinateMeasurability period hPeriod) :
    ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod where
  aestronglyMeasurable := by
    intro coefficients
    change AEStronglyMeasurable
      (programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap
        period hPeriod coefficients)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    induction coefficients using Finsupp.induction with
    | zero =>
        rw [map_zero]
        exact aestronglyMeasurable_const
    | single_add mode coefficient rest _ _ inductionHypothesis =>
        rw [map_add, ← Finsupp.smul_single_one mode coefficient, map_smul]
        have hMode : AEStronglyMeasurable
            (programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap
              period hPeriod (Finsupp.single mode 1))
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
          measurability.basis_aestronglyMeasurable mode
        exact (hMode.const_smul coefficient).add inductionHypothesis

/-- Solving the measurable-gauge problem on individual modes supplies the
finite-core `Lp` realization and its exact norm. -/
def ProgramPT05SpinCMatterFiniteModeCoordinateMeasurability.toFiniteCoreLpSupport
    (measurability :
      ProgramPT05SpinCMatterFiniteModeCoordinateMeasurability period hPeriod) :
    ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod :=
  measurability.toFiniteCore.toFiniteCoreLpSupport

end
end P0EFTJanusProgramPT05SpinCMatterFiniteModeMeasurableGaugeSupport4D
end JanusFormal
