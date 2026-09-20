import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchLpTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D

/-!
# Smooth local Rellich bounds on the canonical LL throat

One scalar component of a smooth LL field is localized on a genuine throat
patch.  Its Euclidean value and gradient are transported to the canonical
patch measure and controlled by the actual completed LL energy norm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchLpTransport4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

private abbrev PatchSourceLp (Fiber : Type*)
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    (finiteThroatGeneratorPatchCanonicalSourceMeasure
      period hPeriod patch)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatVolumeIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

/-- Euclidean fiber containing all four values and all three-by-four local
derivative components. -/
abbrev FiniteThroatGeneratorPatchJetFiber :=
  EuclideanSpace Real
    (Fin 4 ⊕ (FiniteThroatGeneratorBasisIndex × Fin 4))

/-- The patch-local first jet used in the pointwise graph estimate. -/
def finiteThroatGeneratorPatchLocalFirstJet
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch) :
    FiniteThroatGeneratorPatchJetFiber :=
  (EuclideanSpace.equiv
      (Fin 4 ⊕ (FiniteThroatGeneratorBasisIndex × Fin 4)) Real).symm
    fun index =>
      match index with
      | Sum.inl component =>
          finiteThroatGeneratorPatchCutField
            period hPeriod patch field point.1 component
      | Sum.inr derivativeIndex =>
          finiteThroatGeneratorLocalDerivative
            period hPeriod LLFieldFiber
            (finiteThroatGeneratorPatchCutField
              period hPeriod patch field)
            patch derivativeIndex.1 point.1 derivativeIndex.2

@[simp]
theorem finiteThroatGeneratorPatchLocalFirstJet_value
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (component : Fin 4) :
    finiteThroatGeneratorPatchLocalFirstJet
        period hPeriod patch field point (Sum.inl component) =
      finiteThroatGeneratorPatchCutField
        period hPeriod patch field point.1 component := by
  rfl

@[simp]
theorem finiteThroatGeneratorPatchLocalFirstJet_derivative
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (component : Fin 4) :
    finiteThroatGeneratorPatchLocalFirstJet
        period hPeriod patch field point (Sum.inr (basisIndex, component)) =
      finiteThroatGeneratorLocalDerivative
        period hPeriod LLFieldFiber
        (finiteThroatGeneratorPatchCutField
          period hPeriod patch field)
        patch basisIndex point.1 component := by
  rfl

/-- Uniform pointwise control of one localized scalar value and gradient by
the full local LL jet. -/
theorem exists_finiteThroatGeneratorPatchPointwiseGraphBound
    (patch : Patch period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
        (component : Fin 4) (field : LLWeakTestSpace period hPeriod),
        ‖finiteThroatGeneratorPatchLocalizedCoordinateFunction
            period hPeriod patch component field
            (finiteThroatGeneratorPatchHilbertCoordinate
              period hPeriod patch point)‖ ≤
            constant *
              ‖finiteThroatGeneratorPatchLocalFirstJet
                period hPeriod patch field point‖ ∧
          ‖RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
              (E := CanonicalThroatChartHilbertCoordinates)
              (finiteThroatGeneratorPatchLocalizedCoordinateFunction
                period hPeriod patch component field)
              (finiteThroatGeneratorPatchHilbertCoordinate
                period hPeriod patch point)‖ ≤
            constant *
              ‖finiteThroatGeneratorPatchLocalFirstJet
                period hPeriod patch field point‖ := by
  let gradientMap :=
    finiteThroatGeneratorPatchLocalCoordinateGradient
      period hPeriod patch
  let constant := max 1 ‖gradientMap‖
  have hConstantNonneg : 0 ≤ constant :=
    (by positivity : 0 ≤ (1 : Real)).trans (le_max_left _ _)
  refine ⟨constant, hConstantNonneg, ?_⟩
  intro point component field
  let jet :=
    finiteThroatGeneratorPatchLocalFirstJet
      period hPeriod patch field point
  have hValueJet :
      ‖finiteThroatGeneratorPatchCutField
          period hPeriod patch field point.1 component‖ ≤ ‖jet‖ := by
    simpa [jet] using
      (PiLp.norm_apply_le jet (Sum.inl component))
  have hDerivativeJet (basisIndex : FiniteThroatGeneratorBasisIndex) :
      ‖finiteThroatGeneratorLocalDerivative
          period hPeriod LLFieldFiber
          (finiteThroatGeneratorPatchCutField
            period hPeriod patch field)
          patch basisIndex point.1 component‖ ≤ ‖jet‖ := by
    simpa [jet] using
      (PiLp.norm_apply_le jet (Sum.inr (basisIndex, component)))
  have hScalarDerivativeJet
      (basisIndex : FiniteThroatGeneratorBasisIndex) :
      ‖finiteThroatGeneratorLocalDerivative
          period hPeriod Real
          (finiteThroatGeneratorPatchCutComponent
            period hPeriod patch component field)
          patch basisIndex point.1‖ ≤ ‖jet‖ := by
    rw [finiteThroatGeneratorPatchCutComponent_localDerivative]
    exact hDerivativeJet basisIndex
  constructor
  · rw [finiteThroatGeneratorPatchLocalizedCoordinateFunction_coordinate
      period hPeriod patch point component field]
    exact hValueJet.trans
      (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
  · rw [finiteThroatGeneratorPatchLocalizedCoordinateFunction_grad
      period hPeriod patch point component field]
    apply (gradientMap.le_opNorm _).trans
    apply mul_le_mul
    · exact le_max_right _ _
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg jet)).2
        hScalarDerivativeJet
    · exact norm_nonneg _
    · exact hConstantNonneg

/-- The localized coordinate representative as a Euclidean `C¹_c`
function. -/
def finiteThroatGeneratorPatchLocalizedC1c
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c
      (E := CanonicalThroatChartHilbertCoordinates)) :=
  ⟨finiteThroatGeneratorPatchLocalizedCoordinateFunction
      period hPeriod patch component field,
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_contDiff
      period hPeriod patch component field).of_le (by simp),
    HasCompactSupport.intro
      (finiteThroatGeneratorPatchHilbertSupport_isCompact
        period hPeriod patch)
      (fun coordinate hCoordinate => by
        by_contra hNe
        exact hCoordinate
          (finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
            period hPeriod patch component field (subset_closure hNe)))⟩

/-- Global throat `L²` representative of one localized scalar component. -/
def finiteThroatGeneratorPatchCutComponentL2
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (smoothThroatField_memLp period hPeriod Real
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteThroatGeneratorPatchCutComponent
      period hPeriod patch component field)).toLp
        (finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field).toFun

theorem finiteThroatGeneratorPatchCutComponentL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component field :
      EffectiveThroat period hPeriod → Real) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (finiteThroatGeneratorPatchCutComponent
        period hPeriod patch component field).toFun :=
  (smoothThroatField_memLp period hPeriod Real
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteThroatGeneratorPatchCutComponent
      period hPeriod patch component field)).coeFn_toLp

/-- Restriction of one localized scalar component to its closed patch. -/
def finiteThroatGeneratorPatchCutComponentRestrictedL2
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    Lp Real (2 : ENNReal)
      ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (finiteThroatGeneratorClosedPatch period hPeriod patch)) :=
  MeasureTheory.Lp.changeMeasureL
    (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (ν := (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
      (finiteThroatGeneratorClosedPatch period hPeriod patch))
    (E := Real) (p := (2 : ENNReal)) (c := 1)
    (by simp) (by simpa using
      (Measure.restrict_le_self :
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch period hPeriod patch) ≤
          intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (by simp)
    (finiteThroatGeneratorPatchCutComponentL2
      period hPeriod patch component field)

theorem finiteThroatGeneratorPatchCutComponentRestrictedL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchCutComponentRestrictedL2
        period hPeriod patch component field :
      EffectiveThroat period hPeriod → Real) =ᵐ[
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
          (finiteThroatGeneratorClosedPatch period hPeriod patch)]
      (finiteThroatGeneratorPatchCutComponent
        period hPeriod patch component field).toFun := by
  have hChanged :
      (finiteThroatGeneratorPatchCutComponentRestrictedL2
          period hPeriod patch component field :
        EffectiveThroat period hPeriod → Real) =ᵐ[
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch period hPeriod patch)]
        finiteThroatGeneratorPatchCutComponentL2
          period hPeriod patch component field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
              (finiteThroatGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (by simp)
      (finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component field)
  exact hChanged.trans
    (Measure.absolutelyContinuous_restrict.ae_eq
      (finiteThroatGeneratorPatchCutComponentL2_coeFn_ae_eq
        period hPeriod patch component field))

/-- Value component of one localized smooth Euclidean graph. -/
def finiteThroatGeneratorPatchLocalizedValueL2
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    Lp Real (2 : ENNReal)
      (volume : Measure CanonicalThroatChartHilbertCoordinates) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
    (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
    (E := CanonicalThroatChartHilbertCoordinates)
    (finiteThroatGeneratorPatchLocalizedC1c
      period hPeriod patch component field)

/-- Gradient component of one localized smooth Euclidean graph. -/
def finiteThroatGeneratorPatchLocalizedGradientL2
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    Lp CanonicalThroatChartHilbertCoordinates (2 : ENNReal)
      (volume : Measure CanonicalThroatChartHilbertCoordinates) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
    (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
    (E := CanonicalThroatChartHilbertCoordinates)
    (finiteThroatGeneratorPatchLocalizedC1c
      period hPeriod patch component field)

theorem finiteThroatGeneratorPatchLocalizedValueL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchLocalizedValueL2
        period hPeriod patch component field :
      CanonicalThroatChartHilbertCoordinates → Real) =ᵐ[volume]
      finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component field := by
  exact
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (E := CanonicalThroatChartHilbertCoordinates)
      (finiteThroatGeneratorPatchLocalizedC1c
        period hPeriod patch component field).2).coeFn_toLp

theorem finiteThroatGeneratorPatchLocalizedGradientL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchLocalizedGradientL2
        period hPeriod patch component field :
      CanonicalThroatChartHilbertCoordinates →
        CanonicalThroatChartHilbertCoordinates) =ᵐ[volume]
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
        (E := CanonicalThroatChartHilbertCoordinates)
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field) := by
  exact
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (E := CanonicalThroatChartHilbertCoordinates)
      (finiteThroatGeneratorPatchLocalizedC1c
        period hPeriod patch component field).2).coeFn_toLp

theorem finiteThroatGeneratorPatchLocalizedValueL2_zero_off_support
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    ∀ᵐ coordinate ∂(volume :
        Measure CanonicalThroatChartHilbertCoordinates),
      coordinate ∉ finiteThroatGeneratorPatchHilbertSupport
          period hPeriod patch →
        finiteThroatGeneratorPatchLocalizedValueL2
          period hPeriod patch component field coordinate = 0 := by
  filter_upwards [
    finiteThroatGeneratorPatchLocalizedValueL2_coeFn_ae_eq
      period hPeriod patch component field] with coordinate hValue
  intro hCoordinate
  rw [hValue]
  by_contra hNe
  exact hCoordinate
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch component field (subset_closure hNe))

theorem finiteThroatGeneratorPatchLocalizedGradientL2_zero_off_support
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    ∀ᵐ coordinate ∂(volume :
        Measure CanonicalThroatChartHilbertCoordinates),
      coordinate ∉ finiteThroatGeneratorPatchHilbertSupport
          period hPeriod patch →
        finiteThroatGeneratorPatchLocalizedGradientL2
          period hPeriod patch component field coordinate = 0 := by
  filter_upwards [
    finiteThroatGeneratorPatchLocalizedGradientL2_coeFn_ae_eq
      period hPeriod patch component field] with coordinate hGradient
  intro hCoordinate
  rw [hGradient]
  by_contra hNe
  exact hCoordinate
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch component field
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field) (subset_closure hNe)))

/-- A globally smooth representative of the local first jet.  The local
vectors are replaced outside the patch by their plateau extensions. -/
def finiteThroatGeneratorPatchExtendedFirstJetField
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    SmoothThroatField period hPeriod
      FiniteThroatGeneratorPatchJetFiber where
  toFun point :=
    (EuclideanSpace.equiv
        (Fin 4 ⊕ (FiniteThroatGeneratorBasisIndex × Fin 4)) Real).symm
      fun index =>
        match index with
        | Sum.inl component =>
            finiteThroatGeneratorPatchCutField
              period hPeriod patch field point component
        | Sum.inr derivativeIndex =>
            ∑ canonicalIndex :
                Fin (canonicalDivergenceFreeLLFrame period hPeriod).count,
              finiteThroatGeneratorCanonicalCoefficient
                  period hPeriod patch derivativeIndex.1
                  canonicalIndex point *
                throatFrameDerivative period hPeriod LLFieldFiber
                  (canonicalDivergenceFreeLLFrame period hPeriod)
                  (finiteThroatGeneratorPatchCutField
                    period hPeriod patch field)
                  point canonicalIndex derivativeIndex.2
  contMDiff_toFun := by
    apply (EuclideanSpace.equiv
      (Fin 4 ⊕ (FiniteThroatGeneratorBasisIndex × Fin 4))
      Real).symm.toContinuousLinearMap.contDiff.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    cases index with
    | inl component =>
        exact (llFieldComponentProjection component).contDiff.contMDiff.comp
          (finiteThroatGeneratorPatchCutField
            period hPeriod patch field).contMDiff_toFun
    | inr derivativeIndex =>
        apply ContMDiff.sum
        intro canonicalIndex _
        exact
          (finiteThroatGeneratorCanonicalCoefficient
            period hPeriod patch derivativeIndex.1
            canonicalIndex).contMDiff_toFun.mul
          ((llFieldComponentProjection
              derivativeIndex.2).contDiff.contMDiff.comp
            ((contMDiff_pi_space.mp
              (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
                (canonicalDivergenceFreeLLFrame period hPeriod)
                (finiteThroatGeneratorPatchCutField
                  period hPeriod patch field))) canonicalIndex))

@[simp]
theorem finiteThroatGeneratorPatchExtendedFirstJetField_value
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (component : Fin 4) :
    finiteThroatGeneratorPatchExtendedFirstJetField
        period hPeriod patch field point (Sum.inl component) =
      finiteThroatGeneratorPatchCutField
        period hPeriod patch field point component := by
  rfl

theorem finiteThroatGeneratorPatchExtendedFirstJetField_derivative
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (component : Fin 4) :
    finiteThroatGeneratorPatchExtendedFirstJetField
        period hPeriod patch field point (Sum.inr (basisIndex, component)) =
      finiteThroatGeneratorExtendedDerivative
        period hPeriod LLFieldFiber
        (finiteThroatGeneratorPatchCutField
          period hPeriod patch field)
        patch basisIndex point component := by
  rw [finiteThroatGeneratorExtendedDerivative_eq_sum]
  change
    (∑ canonicalIndex :
        Fin (canonicalDivergenceFreeLLFrame period hPeriod).count,
      finiteThroatGeneratorCanonicalCoefficient
          period hPeriod patch basisIndex canonicalIndex point *
        throatFrameDerivative period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (finiteThroatGeneratorPatchCutField
            period hPeriod patch field)
          point canonicalIndex component) =
      llFieldComponentProjection component
        (∑ canonicalIndex :
            Fin (canonicalDivergenceFreeLLFrame period hPeriod).count,
          finiteThroatGeneratorCanonicalCoefficient
              period hPeriod patch basisIndex canonicalIndex point •
            throatFrameDerivative period hPeriod LLFieldFiber
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (finiteThroatGeneratorPatchCutField
                period hPeriod patch field)
              point canonicalIndex)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro canonicalIndex _
  rw [map_smul, llFieldComponentProjection_apply]
  rfl

/-- The extended first jet as a global canonical throat `L²` class. -/
def finiteThroatGeneratorPatchExtendedFirstJetL2
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    Lp FiniteThroatGeneratorPatchJetFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (smoothThroatField_memLp period hPeriod
    FiniteThroatGeneratorPatchJetFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteThroatGeneratorPatchExtendedFirstJetField
      period hPeriod patch field)).toLp
        (finiteThroatGeneratorPatchExtendedFirstJetField
          period hPeriod patch field).toFun

theorem finiteThroatGeneratorPatchExtendedFirstJetL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchExtendedFirstJetL2
        period hPeriod patch field :
      EffectiveThroat period hPeriod →
        FiniteThroatGeneratorPatchJetFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (finiteThroatGeneratorPatchExtendedFirstJetField
        period hPeriod patch field).toFun :=
  (smoothThroatField_memLp period hPeriod
    FiniteThroatGeneratorPatchJetFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteThroatGeneratorPatchExtendedFirstJetField
      period hPeriod patch field)).coeFn_toLp

theorem finiteThroatGeneratorPatchExtendedFirstJet_norm_sq
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ‖finiteThroatGeneratorPatchExtendedFirstJetField
        period hPeriod patch field point‖ ^ 2 =
      ‖finiteThroatGeneratorPatchCutField
        period hPeriod patch field point‖ ^ 2 +
        ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ‖finiteThroatGeneratorExtendedDerivative
            period hPeriod LLFieldFiber
            (finiteThroatGeneratorPatchCutField
              period hPeriod patch field)
            patch basisIndex point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_sum_type,
    finiteThroatGeneratorPatchExtendedFirstJetField_value,
    finiteThroatGeneratorPatchExtendedFirstJetField_derivative,
    Fintype.sum_prod_type]
  rw [← EuclideanSpace.real_norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro basisIndex _
  rw [EuclideanSpace.real_norm_sq_eq]

theorem finiteThroatGeneratorPatchExtendedFirstJetL2_norm_sq
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    ‖finiteThroatGeneratorPatchExtendedFirstJetL2
        period hPeriod patch field‖ ^ 2 =
      ∫ point,
        ‖finiteThroatGeneratorPatchExtendedFirstJetField
          period hPeriod patch field point‖ ^ 2
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    finiteThroatGeneratorPatchExtendedFirstJetL2_coeFn_ae_eq
      period hPeriod patch field] with point hPoint
  rw [hPoint, real_inner_self_eq_norm_sq]

/-- The extended jet density is uniformly controlled by the canonical
frame-H¹ density of the cut field. -/
theorem exists_finiteThroatGeneratorPatchExtendedFirstJet_density_bound
    (patch : Patch period hPeriod) :
    ∃ constant : Real, 0 < constant ∧
      ∀ (field : LLWeakTestSpace period hPeriod)
        (point : EffectiveThroat period hPeriod),
        ‖finiteThroatGeneratorPatchExtendedFirstJetField
            period hPeriod patch field point‖ ^ 2 ≤
          constant *
            llCanonicalFrameH1Density period hPeriod
              (finiteThroatGeneratorPatchCutField
                period hPeriod patch field) point := by
  obtain ⟨massBound, hMassBound, hMass⟩ :=
    exists_finiteThroatGeneratorCanonicalCoefficientMass_bound
      period hPeriod patch
  let constant := max 1 massBound
  have hConstant : 0 < constant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨constant, hConstant, ?_⟩
  intro field point
  let cutField :=
    finiteThroatGeneratorPatchCutField
      period hPeriod patch field
  have hEnergyNonneg :
      0 ≤ throatDerivativeEnergy period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) cutField point :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDerivative :=
    finiteThroatGeneratorExtendedDerivativeEnergy_le_mass
      period hPeriod cutField patch point
  have hMassEnergy :
      finiteThroatGeneratorCanonicalCoefficientMass
          period hPeriod patch point *
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point ≤
        massBound *
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point :=
    mul_le_mul_of_nonneg_right (hMass point) hEnergyNonneg
  rw [finiteThroatGeneratorPatchExtendedFirstJet_norm_sq]
  change
    ‖cutField point‖ ^ 2 +
        ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ‖finiteThroatGeneratorExtendedDerivative
            period hPeriod LLFieldFiber cutField patch basisIndex point‖ ^ 2 ≤
      constant *
        (‖cutField point‖ ^ 2 +
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point)
  calc
    ‖cutField point‖ ^ 2 +
        ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ‖finiteThroatGeneratorExtendedDerivative
            period hPeriod LLFieldFiber cutField patch basisIndex point‖ ^ 2 ≤
      ‖cutField point‖ ^ 2 +
        massBound *
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point :=
      add_le_add (le_refl _) (hDerivative.trans hMassEnergy)
    _ ≤ constant * ‖cutField point‖ ^ 2 +
        constant *
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point := by
      apply add_le_add
      · simpa [constant] using
          (mul_le_mul_of_nonneg_right
            (le_max_left (1 : Real) massBound) (sq_nonneg ‖cutField point‖))
      · simpa [constant] using
          (mul_le_mul_of_nonneg_right
            (le_max_right (1 : Real) massBound) hEnergyNonneg)
    _ = constant *
        (‖cutField point‖ ^ 2 +
          throatDerivativeEnergy period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) cutField point) := by
      ring

/-- The global extended jet is bounded by the actual completed LL energy on
the smooth core. -/
theorem exists_finiteThroatGeneratorPatchExtendedFirstJetL2_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod) :
    ∃ constant : Real, 0 < constant ∧
      ∀ u : LLH1Smooth period hPeriod
          (analysis.llH1Data period hPeriod),
        ‖finiteThroatGeneratorPatchExtendedFirstJetL2
            period hPeriod patch u.toTest‖ ≤
          constant * ‖u‖ := by
  obtain ⟨densityConstant, hDensityConstant, hDensity⟩ :=
    exists_finiteThroatGeneratorPatchExtendedFirstJet_density_bound
      period hPeriod patch
  obtain ⟨energyConstant, hEnergyConstant, hEnergy⟩ :=
    canonicalLLSmooth_cutoff_frameH1_bound period hPeriod analysis
      (finiteThroatGeneratorCutoff period hPeriod patch)
  let totalConstant := densityConstant * energyConstant
  have hTotalConstant : 0 < totalConstant :=
    mul_pos hDensityConstant hEnergyConstant
  refine ⟨Real.sqrt totalConstant, Real.sqrt_pos.2 hTotalConstant, ?_⟩
  intro u
  have hJetIntegrable :
      Integrable (fun point =>
        ‖finiteThroatGeneratorPatchExtendedFirstJetField
          period hPeriod patch u.toTest point‖ ^ 2)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    ((finiteThroatGeneratorPatchExtendedFirstJetField
      period hPeriod patch u.toTest).contMDiff_toFun.continuous.norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDensityIntegrable :
      Integrable (llCanonicalFrameH1Density period hPeriod
        (finiteThroatGeneratorPatchCutField
          period hPeriod patch u.toTest))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (llCanonicalFrameH1Density_continuous period hPeriod
      (finiteThroatGeneratorPatchCutField
        period hPeriod patch u.toTest)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hIntegral := integral_mono hJetIntegrable
    (hDensityIntegrable.const_mul densityConstant)
    (hDensity u.toTest)
  rw [integral_const_mul] at hIntegral
  have hCutoff :
      llCanonicalFrameH1SizeSq period hPeriod
          (finiteThroatGeneratorPatchCutField
            period hPeriod patch u.toTest) ≤
        energyConstant * ‖u‖ ^ 2 := by
    simpa [finiteThroatGeneratorPatchCutField] using hEnergy u
  have hSq :
      ‖finiteThroatGeneratorPatchExtendedFirstJetL2
          period hPeriod patch u.toTest‖ ^ 2 ≤
        totalConstant * ‖u‖ ^ 2 := by
    rw [finiteThroatGeneratorPatchExtendedFirstJetL2_norm_sq]
    unfold llCanonicalFrameH1SizeSq at hCutoff
    calc
      ∫ point,
          ‖finiteThroatGeneratorPatchExtendedFirstJetField
            period hPeriod patch u.toTest point‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) ≤
        densityConstant *
          ∫ point,
            llCanonicalFrameH1Density period hPeriod
              (finiteThroatGeneratorPatchCutField
                period hPeriod patch u.toTest) point
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
        hIntegral
      _ ≤ densityConstant * (energyConstant * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCutoff hDensityConstant.le
      _ = totalConstant * ‖u‖ ^ 2 := by
        rw [show totalConstant = densityConstant * energyConstant from rfl]
        ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg totalConstant) (norm_nonneg u))).1
  rw [mul_pow, Real.sq_sqrt hTotalConstant.le]
  exact hSq

/-- The global extended jet restricted to the measured patch source. -/
def finiteThroatGeneratorPatchSmoothFirstJetSourceL2
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    PatchSourceLp (Fiber := FiniteThroatGeneratorPatchJetFiber)
      period hPeriod patch :=
  finiteThroatGeneratorPatchRestrictQuotientLp
    (Fiber := FiniteThroatGeneratorPatchJetFiber)
    period hPeriod patch
    (finiteThroatGeneratorPatchExtendedFirstJetL2
      period hPeriod patch field)

theorem finiteThroatGeneratorPatchSmoothFirstJetSourceL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchSmoothFirstJetSourceL2
        period hPeriod patch field :
      FiniteThroatGeneratorPatchDomain period hPeriod patch →
        FiniteThroatGeneratorPatchJetFiber) =ᵐ[
          finiteThroatGeneratorPatchCanonicalSourceMeasure
            period hPeriod patch]
      finiteThroatGeneratorPatchLocalFirstJet
        period hPeriod patch field := by
  let globalJet :=
    finiteThroatGeneratorPatchExtendedFirstJetL2
      period hPeriod patch field
  have hRestricted :=
    finiteThroatGeneratorPatchRestrictQuotientLp_coeFn_ae_eq
      (Fiber := FiniteThroatGeneratorPatchJetFiber)
      period hPeriod patch globalJet
  have hGlobal :=
    finiteThroatGeneratorPatchExtendedFirstJetL2_coeFn_ae_eq
      period hPeriod patch field
  have hSubtypeQMP :
      Measure.QuasiMeasurePreserving
        (Subtype.val :
          FiniteThroatGeneratorPatchDomain period hPeriod patch →
            EffectiveThroat period hPeriod)
        (finiteThroatGeneratorPatchCanonicalSourceMeasure
          period hPeriod patch)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (finiteThroatGeneratorPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.mono_right
        Measure.absolutelyContinuous_restrict
  filter_upwards [hRestricted, hSubtypeQMP.ae_eq_comp hGlobal]
    with point hRestricted hGlobal
  change
    ((finiteThroatGeneratorPatchRestrictQuotientLp
        (Fiber := FiniteThroatGeneratorPatchJetFiber)
        period hPeriod patch globalJet :
      FiniteThroatGeneratorPatchDomain period hPeriod patch →
        FiniteThroatGeneratorPatchJetFiber) point) = _
  rw [hRestricted]
  change
    (((finiteThroatGeneratorPatchExtendedFirstJetL2
        period hPeriod patch field :
      EffectiveThroat period hPeriod →
        FiniteThroatGeneratorPatchJetFiber) ∘ Subtype.val) point) = _
  rw [hGlobal]
  apply (EuclideanSpace.equiv
    (Fin 4 ⊕ (FiniteThroatGeneratorBasisIndex × Fin 4)) Real).injective
  funext index
  cases index with
  | inl component => rfl
  | inr derivativeIndex =>
      change
        finiteThroatGeneratorPatchExtendedFirstJetField
            period hPeriod patch field point.1
            (Sum.inr derivativeIndex) =
          finiteThroatGeneratorPatchLocalFirstJet
            period hPeriod patch field point
            (Sum.inr derivativeIndex)
      rw [finiteThroatGeneratorPatchExtendedFirstJetField_derivative,
        finiteThroatGeneratorPatchLocalFirstJet_derivative]
      exact congrArg (fun value : LLFieldFiber => value derivativeIndex.2)
        (finiteThroatGeneratorLocalDerivative_eq_extended
          period hPeriod LLFieldFiber
          (finiteThroatGeneratorPatchCutField
            period hPeriod patch field)
          patch derivativeIndex.1 point.1 point.2).symm

theorem finiteThroatGeneratorPatchSmoothFirstJetSourceL2_norm_le
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ u : LLH1Smooth period hPeriod
          (analysis.llH1Data period hPeriod),
        ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
            period hPeriod patch u.toTest‖ ≤
          constant * ‖u‖ := by
  obtain ⟨jetConstant, hJetConstant, hJet⟩ :=
    exists_finiteThroatGeneratorPatchExtendedFirstJetL2_bound
      period hPeriod analysis patch
  let restrictionNorm :=
    ‖finiteThroatGeneratorPatchRestrictQuotientLp
      (Fiber := FiniteThroatGeneratorPatchJetFiber)
      period hPeriod patch‖
  refine ⟨restrictionNorm * jetConstant,
    mul_nonneg (norm_nonneg _) hJetConstant.le, ?_⟩
  intro u
  calc
    ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
        period hPeriod patch u.toTest‖ ≤
      restrictionNorm *
        ‖finiteThroatGeneratorPatchExtendedFirstJetL2
          period hPeriod patch u.toTest‖ :=
      (finiteThroatGeneratorPatchRestrictQuotientLp
        (Fiber := FiniteThroatGeneratorPatchJetFiber)
        period hPeriod patch).le_opNorm _
    _ ≤ restrictionNorm * (jetConstant * ‖u‖) :=
      mul_le_mul_of_nonneg_left (hJet u) (norm_nonneg _)
    _ = (restrictionNorm * jetConstant) * ‖u‖ := by ring

theorem finiteThroatGeneratorPatchLocalizedValueSource_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchAmbientToSourceLp
        (Fiber := Real) period hPeriod patch comparison
        (finiteThroatGeneratorPatchLocalizedValueL2
          period hPeriod patch component field) :
      FiniteThroatGeneratorPatchDomain period hPeriod patch → Real) =ᵐ[
        finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field
          (finiteThroatGeneratorPatchHilbertCoordinate
            period hPeriod patch point) := by
  refine
    (finiteThroatGeneratorPatchAmbientToSourceLp_coeFn_ae_eq
      (Fiber := Real) period hPeriod patch comparison
      (finiteThroatGeneratorPatchLocalizedValueL2
        period hPeriod patch component field)).trans ?_
  exact
    (finiteThroatGeneratorPatchHilbertCoordinateQuasiMeasurePreserving
      period hPeriod patch comparison).ae_eq_comp
      (finiteThroatGeneratorPatchLocalizedValueL2_coeFn_ae_eq
        period hPeriod patch component field)

/-- The localized Euclidean value pulls back to the scalar component of the
cut LL field on the measured patch. -/
theorem finiteThroatGeneratorPatchLocalizedValueSource_eq_cutPullback
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchAmbientToSourceLp
        (Fiber := Real) period hPeriod patch comparison
        (finiteThroatGeneratorPatchLocalizedValueL2
          period hPeriod patch component field) =
      finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
        period hPeriod patch
        (finiteThroatGeneratorPatchCutComponentRestrictedL2
          period hPeriod patch component field) := by
  apply Lp.ext
  have hLeft :=
    finiteThroatGeneratorPatchLocalizedValueSource_coeFn_ae_eq
      period hPeriod patch comparison component field
  have hRight :
      (finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
          period hPeriod patch
          (finiteThroatGeneratorPatchCutComponentRestrictedL2
            period hPeriod patch component field) :
        FiniteThroatGeneratorPatchDomain period hPeriod patch → Real) =ᵐ[
          finiteThroatGeneratorPatchCanonicalSourceMeasure
            period hPeriod patch]
        fun point =>
          finiteThroatGeneratorPatchCutComponentRestrictedL2
            period hPeriod patch component field point.1 :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      (finiteThroatGeneratorPatchCutComponentRestrictedL2
        period hPeriod patch component field)
      (finiteThroatGeneratorPatchSubtypeMeasurePreserving
        period hPeriod patch)
  have hCut :=
    (finiteThroatGeneratorPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        (finiteThroatGeneratorPatchCutComponentRestrictedL2_coeFn_ae_eq
          period hPeriod patch component field)
  filter_upwards [hLeft, hRight, hCut]
    with point hLeft hRight hCut
  rw [hLeft,
    finiteThroatGeneratorPatchLocalizedCoordinateFunction_coordinate
      period hPeriod patch point component field,
    hRight]
  simpa [finiteThroatGeneratorPatchCutComponent_apply,
    Function.comp_apply] using hCut.symm

/-- Extension by zero of the restricted cut component recovers its global
canonical throat `L²` class. -/
theorem finiteThroatGeneratorPatchCutComponentExtension_eq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteThroatGeneratorClosedPatch period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet)
        (finiteThroatGeneratorPatchCutComponentRestrictedL2
          period hPeriod patch component field) =
      finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component field := by
  apply Lp.ext
  let closedPatch :=
    finiteThroatGeneratorClosedPatch period hPeriod patch
  have hClosedPatchMeasurable : MeasurableSet closedPatch :=
    (finiteThroatGeneratorClosedPatch_isClosed
      period hPeriod patch).measurableSet
  have hExtended :
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
          (E := Real) (p := (2 : ENNReal))
          (s := closedPatch) hClosedPatchMeasurable)
          (finiteThroatGeneratorPatchCutComponentRestrictedL2
            period hPeriod patch component field) :
        EffectiveThroat period hPeriod → Real) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        closedPatch.indicator fun point =>
          finiteThroatGeneratorPatchCutComponentRestrictedL2
            period hPeriod patch component field point :=
    MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
      hClosedPatchMeasurable
      (finiteThroatGeneratorPatchCutComponentRestrictedL2
        period hPeriod patch component field)
  have hRestrictedOn :
      ∀ᵐ point ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod,
        point ∈ closedPatch →
          finiteThroatGeneratorPatchCutComponentRestrictedL2
              period hPeriod patch component field point =
            finiteThroatGeneratorPatchCutComponent
              period hPeriod patch component field point :=
    (ae_restrict_iff' hClosedPatchMeasurable).1
      (finiteThroatGeneratorPatchCutComponentRestrictedL2_coeFn_ae_eq
        period hPeriod patch component field)
  have hGlobal :=
    finiteThroatGeneratorPatchCutComponentL2_coeFn_ae_eq
      period hPeriod patch component field
  filter_upwards [hExtended, hRestrictedOn, hGlobal]
    with point hExtended hRestricted hGlobal
  rw [hExtended, hGlobal]
  by_cases hPoint : point ∈ closedPatch
  · simp [Set.indicator_of_mem hPoint, hRestricted hPoint]
  · have hWeight :
        finiteThroatGeneratorWeight period hPeriod patch point = 0 := by
      by_contra hNe
      exact hPoint (subset_closure hNe)
    simp [Set.indicator_of_notMem hPoint,
      finiteThroatGeneratorPatchCutComponent_apply, hWeight]

/-- Transporting a localized Euclidean value back to the throat gives its
global cut component exactly. -/
theorem finiteThroatGeneratorPatchLocalizedValueExtension_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchSourceToQuotientL2 period hPeriod patch
        (finiteThroatGeneratorPatchAmbientToSourceLp
          (Fiber := Real) period hPeriod patch comparison
          (finiteThroatGeneratorPatchLocalizedValueL2
            period hPeriod patch component field)) =
      finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component field := by
  rw [finiteThroatGeneratorPatchLocalizedValueSource_eq_cutPullback
      period hPeriod patch comparison component field,
    finiteThroatGeneratorPatchSourceToQuotientL2_pullback
      period hPeriod patch,
    finiteThroatGeneratorPatchCutComponentExtension_eq
      period hPeriod patch component field]

theorem finiteThroatGeneratorPatchLocalizedGradientSource_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    (finiteThroatGeneratorPatchAmbientToSourceLp
        (Fiber := CanonicalThroatChartHilbertCoordinates)
        period hPeriod patch comparison
        (finiteThroatGeneratorPatchLocalizedGradientL2
          period hPeriod patch component field) :
      FiniteThroatGeneratorPatchDomain period hPeriod patch →
        CanonicalThroatChartHilbertCoordinates) =ᵐ[
          finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
          (E := CanonicalThroatChartHilbertCoordinates)
          (finiteThroatGeneratorPatchLocalizedCoordinateFunction
            period hPeriod patch component field)
          (finiteThroatGeneratorPatchHilbertCoordinate
            period hPeriod patch point) := by
  refine
    (finiteThroatGeneratorPatchAmbientToSourceLp_coeFn_ae_eq
      (Fiber := CanonicalThroatChartHilbertCoordinates)
      period hPeriod patch comparison
      (finiteThroatGeneratorPatchLocalizedGradientL2
        period hPeriod patch component field)).trans ?_
  exact
    (finiteThroatGeneratorPatchHilbertCoordinateQuasiMeasurePreserving
      period hPeriod patch comparison).ae_eq_comp
      (finiteThroatGeneratorPatchLocalizedGradientL2_coeFn_ae_eq
        period hPeriod patch component field)

/-- Both localized Euclidean graph components are controlled on canonical
patch volume by the restricted local first jet. -/
theorem exists_finiteThroatGeneratorPatchLocalizedSourceGraphBound
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (component : Fin 4) (field : LLWeakTestSpace period hPeriod),
        ‖finiteThroatGeneratorPatchAmbientToSourceLp
            (Fiber := Real) period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedValueL2
              period hPeriod patch component field)‖ ≤
          constant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖ ∧
        ‖finiteThroatGeneratorPatchAmbientToSourceLp
            (Fiber := CanonicalThroatChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedGradientL2
              period hPeriod patch component field)‖ ≤
          constant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖ := by
  obtain ⟨constant, hConstant, hPointwise⟩ :=
    exists_finiteThroatGeneratorPatchPointwiseGraphBound
      period hPeriod patch
  refine ⟨constant, hConstant, ?_⟩
  intro component field
  constructor
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      finiteThroatGeneratorPatchLocalizedValueSource_coeFn_ae_eq
        period hPeriod patch comparison component field,
      finiteThroatGeneratorPatchSmoothFirstJetSourceL2_coeFn_ae_eq
        period hPeriod patch field] with point hValue hJet
    rw [hValue, hJet]
    exact (hPointwise point component field).1
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      finiteThroatGeneratorPatchLocalizedGradientSource_coeFn_ae_eq
        period hPeriod patch comparison component field,
      finiteThroatGeneratorPatchSmoothFirstJetSourceL2_coeFn_ae_eq
        period hPeriod patch field] with point hGradient hJet
    rw [hGradient, hJet]
    exact (hPointwise point component field).2

/-- Ambient Euclidean value and gradient norms are bounded by the completed
LL energy norm on the smooth core. -/
theorem exists_finiteThroatGeneratorPatchLocalizedAmbientGraphBound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (component : Fin 4) :
    ∃ constant : Real,
      ∀ u : LLH1Smooth period hPeriod
          (analysis.llH1Data period hPeriod),
        ‖finiteThroatGeneratorPatchLocalizedValueL2
            period hPeriod patch component u.toTest‖ ≤
          constant * ‖u‖ ∧
        ‖finiteThroatGeneratorPatchLocalizedGradientL2
            period hPeriod patch component u.toTest‖ ≤
          constant * ‖u‖ := by
  obtain ⟨sourceConstant, hSourceConstant, hSource⟩ :=
    exists_finiteThroatGeneratorPatchLocalizedSourceGraphBound
      period hPeriod patch comparison
  obtain ⟨jetConstant, hJetConstant, hJet⟩ :=
    finiteThroatGeneratorPatchSmoothFirstJetSourceL2_norm_le
      period hPeriod analysis patch
  let valueTransportNorm :=
    ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
      (Fiber := Real) period hPeriod patch comparison‖
  let gradientTransportNorm :=
    ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
      (Fiber := CanonicalThroatChartHilbertCoordinates)
      period hPeriod patch comparison‖
  let transportNorm := max valueTransportNorm gradientTransportNorm
  let constant := transportNorm * sourceConstant * jetConstant
  have hTransportNonneg : 0 ≤ transportNorm :=
    (norm_nonneg _).trans (le_max_left _ _)
  refine ⟨constant, ?_⟩
  intro u
  have hSourceField := hSource component u.toTest
  constructor
  · calc
      ‖finiteThroatGeneratorPatchLocalizedValueL2
          period hPeriod patch component u.toTest‖ ≤
        valueTransportNorm *
          ‖finiteThroatGeneratorPatchAmbientToSourceLp
            (Fiber := Real) period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedValueL2
              period hPeriod patch component u.toTest)‖ := by
        exact
          finiteThroatGeneratorPatchAmbient_norm_le_source_norm_of_support
            (Fiber := Real) period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedValueL2
              period hPeriod patch component u.toTest)
            (finiteThroatGeneratorPatchLocalizedValueL2_zero_off_support
              period hPeriod patch component u.toTest)
      _ ≤ valueTransportNorm *
          (sourceConstant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch u.toTest‖) :=
        mul_le_mul_of_nonneg_left hSourceField.1 (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch u.toTest‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_max_left _ _
        · exact mul_nonneg hSourceConstant (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant * (jetConstant * ‖u‖)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (hJet u) hSourceConstant
        · exact hTransportNonneg
      _ = constant * ‖u‖ := by
        simp only [constant]
        ring
  · calc
      ‖finiteThroatGeneratorPatchLocalizedGradientL2
          period hPeriod patch component u.toTest‖ ≤
        gradientTransportNorm *
          ‖finiteThroatGeneratorPatchAmbientToSourceLp
            (Fiber := CanonicalThroatChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedGradientL2
              period hPeriod patch component u.toTest)‖ := by
        exact
          finiteThroatGeneratorPatchAmbient_norm_le_source_norm_of_support
            (Fiber := CanonicalThroatChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteThroatGeneratorPatchLocalizedGradientL2
              period hPeriod patch component u.toTest)
            (finiteThroatGeneratorPatchLocalizedGradientL2_zero_off_support
              period hPeriod patch component u.toTest)
      _ ≤ gradientTransportNorm *
          (sourceConstant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch u.toTest‖) :=
        mul_le_mul_of_nonneg_left hSourceField.2 (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant *
            ‖finiteThroatGeneratorPatchSmoothFirstJetSourceL2
              period hPeriod patch u.toTest‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_max_right _ _
        · exact mul_nonneg hSourceConstant (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant * (jetConstant * ‖u‖)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (hJet u) hSourceConstant
        · exact hTransportNonneg
      _ = constant * ‖u‖ := by
        simp only [constant]
        ring

/-- The smooth scalar chart localizer on one actual throat patch. -/
def finiteThroatGeneratorPatchSmoothEuclideanH1
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c.toH1On
    (E := CanonicalThroatChartHilbertCoordinates)
    (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch)
    (finiteThroatGeneratorPatchLocalizedC1c
      period hPeriod patch component field)
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch component field)

theorem finiteThroatGeneratorPatchSmoothEuclideanH1_norm
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    ‖finiteThroatGeneratorPatchSmoothEuclideanH1
        period hPeriod patch component field‖ =
      max
        ‖finiteThroatGeneratorPatchLocalizedValueL2
          period hPeriod patch component field‖
        ‖finiteThroatGeneratorPatchLocalizedGradientL2
          period hPeriod patch component field‖ := by
  change
    ‖(finiteThroatGeneratorPatchLocalizedValueL2
        period hPeriod patch component field,
      finiteThroatGeneratorPatchLocalizedGradientL2
        period hPeriod patch component field)‖ = _
  rw [Prod.norm_def]

/-- The smooth chart localizer has the graph-norm bound required for
extension to the completed LL energy space. -/
theorem exists_finiteThroatGeneratorPatchSmoothEuclideanH1_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4) :
    ∃ constant : Real,
      ∀ u : LLH1Smooth period hPeriod
          (analysis.llH1Data period hPeriod),
        ‖finiteThroatGeneratorPatchSmoothEuclideanH1
            period hPeriod patch component u.toTest‖ ≤
          constant * ‖u‖ := by
  obtain ⟨constant, hBound⟩ :=
    exists_finiteThroatGeneratorPatchLocalizedAmbientGraphBound
      period hPeriod analysis patch
      (finiteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) component
  refine ⟨constant, ?_⟩
  intro u
  rw [finiteThroatGeneratorPatchSmoothEuclideanH1_norm,
    max_le_iff]
  exact hBound u

end
end P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D
end JanusFormal
