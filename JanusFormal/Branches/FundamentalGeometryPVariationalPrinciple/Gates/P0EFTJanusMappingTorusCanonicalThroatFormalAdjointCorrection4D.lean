import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D

/-!
# Formal-adjoint correction for the canonical throat LL operator

The current strong LL operator uses the raw divergence of a finite family of
partition-of-unity-weighted frame fields.  Those generators are not known to
be divergence-free for the canonical measure.  This gate therefore isolates
the exact smooth correction represented by the weak/strong adjoint defect.

Any such correction produces the correct pointwise strong equation.  The
previous zero-boundary IPP is recovered exactly when the correction vanishes;
no vanishing or existence claim is hidden here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatFormalAdjointCorrection4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

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
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatMeasureIsOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Difference between the implemented weak first variation and pairing with
the raw PT-symmetric strong field.  This is the exact formal-adjoint defect. -/
def canonicalThroatPTSymmetricLLFormalAdjointDefect
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) fields direction
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
    ∫ point,
      inner Real
        (ptSymmetricStrongDifferentialLLEulerField period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) regularity
          fields point)
        (direction point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- A smooth field representing the formal-adjoint defect against every
smooth LL test field.  Existence is an explicit analytic obligation. -/
structure CanonicalThroatPTSymmetricLLFormalAdjointCorrection
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)) where
  correction : SmoothThroatField period hPeriod LLFieldFiber
  realizes : ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    canonicalThroatPTSymmetricLLFormalAdjointDefect period hPeriod fields
        regularity direction =
      ∫ point, inner Real (correction point) (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Strong PT-symmetric Euler field with the exact represented adjoint
correction included. -/
def canonicalThroatCorrectedPTSymmetricStrongLLEulerField
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (formalAdjoint :
      CanonicalThroatPTSymmetricLLFormalAdjointCorrection period hPeriod
        fields regularity) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  ptSymmetricStrongDifferentialLLEulerField period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields +
    formalAdjoint.correction

private theorem smoothThroatInner_integrable
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    Integrable (fun point => inner Real (first point) (second point))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (first.contMDiff_toFun.continuous.inner
      second.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The represented defect converts the weak first variation into pairing
with the corrected strong field, with no further boundary hypothesis. -/
theorem globalPTSymmetricDifferentialLLFluxFirstVariation_eq_correctedStrong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (formalAdjoint :
      CanonicalThroatPTSymmetricLLFormalAdjointCorrection period hPeriod
        fields regularity)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ point,
        inner Real
          (canonicalThroatCorrectedPTSymmetricStrongLLEulerField period hPeriod
            formalAdjoint point)
          (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let rawStrong :=
    ptSymmetricStrongDifferentialLLEulerField period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields
  have hRawIntegrable := smoothThroatInner_integrable period hPeriod
    rawStrong direction
  have hCorrectionIntegrable := smoothThroatInner_integrable period hPeriod
    formalAdjoint.correction direction
  have hDefect := formalAdjoint.realizes direction
  unfold canonicalThroatPTSymmetricLLFormalAdjointDefect at hDefect
  calc
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      (∫ point, inner Real (rawStrong point) (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      ∫ point, inner Real (formalAdjoint.correction point) (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          linarith
    _ = _ := by
      rw [← integral_add hRawIntegrable hCorrectionIntegrable]
      apply integral_congr_ae
      filter_upwards [] with point
      exact (inner_add_left _ _ _).symm

/-- With a represented formal-adjoint correction, the weak equation is
exactly the pointwise corrected strong equation. -/
theorem canonicalThroat_weak_iff_correctedStrong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (formalAdjoint :
      CanonicalThroatPTSymmetricLLFormalAdjointCorrection period hPeriod
        fields regularity) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      ∀ point : EffectiveThroat period hPeriod,
        canonicalThroatCorrectedPTSymmetricStrongLLEulerField period hPeriod
          formalAdjoint point = 0 := by
  constructor
  · intro hWeak
    apply (smoothLLField_pairing_detects_pointwise_zero period hPeriod
      (canonicalThroatCorrectedPTSymmetricStrongLLEulerField period hPeriod
        formalAdjoint)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).mp
    intro direction
    rw [← globalPTSymmetricDifferentialLLFluxFirstVariation_eq_correctedStrong
      period hPeriod fields regularity formalAdjoint direction]
    exact hWeak direction
  · intro hStrong direction
    rw [globalPTSymmetricDifferentialLLFluxFirstVariation_eq_correctedStrong
      period hPeriod fields regularity formalAdjoint direction]
    have hIntegrand :
        (fun point =>
          inner Real
            (canonicalThroatCorrectedPTSymmetricStrongLLEulerField period
              hPeriod formalAdjoint point)
            (direction point)) = 0 := by
      funext point
      rw [hStrong point]
      simp
    rw [hIntegrand]
    simp

/-- Exact residual criterion: the old zero-boundary IPP for the raw operator
holds if and only if its represented formal-adjoint correction is zero. -/
theorem formalAdjointCorrection_eq_zero_iff_globalIPP
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (formalAdjoint :
      CanonicalThroatPTSymmetricLLFormalAdjointCorrection period hPeriod
        fields regularity) :
    formalAdjoint.correction = 0 ↔
      CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP period hPeriod
        fields regularity := by
  constructor
  · intro hCorrectionZero direction
    have hDefect := formalAdjoint.realizes direction
    unfold canonicalThroatPTSymmetricLLFormalAdjointDefect at hDefect
    have hCorrectionPointwise : ∀ point,
        formalAdjoint.correction point = (0 : LLFieldFiber) := by
      intro point
      rw [hCorrectionZero]
      rfl
    have hIntegrand :
        (fun point =>
          inner Real (formalAdjoint.correction point) (direction point)) = 0 := by
      funext point
      rw [hCorrectionPointwise point]
      simp
    rw [hIntegrand] at hDefect
    rw [MeasureTheory.integral_zero'] at hDefect
    exact sub_eq_zero.mp hDefect
  · intro hIPP
    have hPairingZero :
        ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
          (∫ point,
            inner Real (formalAdjoint.correction point) (direction point)
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0 := by
      intro direction
      rw [← formalAdjoint.realizes direction]
      unfold canonicalThroatPTSymmetricLLFormalAdjointDefect
      rw [hIPP direction]
      exact sub_self _
    have hPointwise :=
      (smoothLLField_pairing_detects_pointwise_zero period hPeriod
        formalAdjoint.correction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).mp hPairingZero
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro point
    change formalAdjoint.correction point = (0 : LLFieldFiber)
    exact hPointwise point

end

end P0EFTJanusMappingTorusCanonicalThroatFormalAdjointCorrection4D
end JanusFormal
