import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D

/-!
# L2 realization of the scalar Cauchy trace on the cut boundary

The orientation-double cut boundary carries the canonical doubled-period throat
measure.  Its continuous value and normal traces are therefore genuine L2
vectors.  The value image is even under the residual deck involution while the
normal image is odd.

This is the honest Hilbert realization of the two scalar boundary components.
It deliberately keeps their deck parities visible instead of identifying the
odd normal local system with an ordinary scalar on the one-sided throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryScalarCauchyL24D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D
open P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance cutBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance cutBoundaryCompactSpace :
    CompactSpace (CutThroatBoundary period hPeriod) :=
  P0EFTJanusMappingTorusSmoothQuotientManifold.fixedThroatQuotientCompactSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance cutBoundaryMeasurableSpace :
    MeasurableSpace (CutThroatBoundary period hPeriod) := borel _

local instance cutBoundaryBorelSpace :
    BorelSpace (CutThroatBoundary period hPeriod) where
  measurable_eq := rfl

local instance cutBoundaryCanonicalMeasureFinite :
    IsFiniteMeasure (cutBoundaryCanonicalMeasure period hPeriod) := by
  unfold cutBoundaryCanonicalMeasure
  exact intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- Canonical scalar L2 space on the connected oriented cut boundary. -/
abbrev CanonicalCutBoundaryScalarL2 :=
  Lp Real (2 : ENNReal) (cutBoundaryCanonicalMeasure period hPeriod)

/-- The continuous value trace belongs to cut-boundary L2. -/
theorem cutBoundaryScalarValueTrace_memLp
    (field : SmoothQuotientField period hPeriod Real) :
    MemLp (cutBoundaryScalarValueTrace period hPeriod field)
      (2 : ENNReal) (cutBoundaryCanonicalMeasure period hPeriod) :=
  (cutBoundaryScalarValueTrace_continuous period hPeriod field)
    |>.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The continuous normal trace belongs to cut-boundary L2. -/
theorem cutBoundaryScalarNormalTrace_memLp
    (field : SmoothQuotientField period hPeriod Real) :
    MemLp (cutBoundaryScalarNormalTrace period hPeriod field)
      (2 : ENNReal) (cutBoundaryCanonicalMeasure period hPeriod) :=
  (cutBoundaryScalarNormalTrace_continuous period hPeriod field)
    |>.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Smooth scalar value trace in the physical cut-boundary L2 space. -/
def smoothCutBoundaryScalarValueTraceL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalCutBoundaryScalarL2 period hPeriod where
  toFun field :=
    (cutBoundaryScalarValueTrace_memLp period hPeriod field).toLp
      (cutBoundaryScalarValueTrace period hPeriod field)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(cutBoundaryScalarValueTrace_memLp period hPeriod (first + second)).coeFn_toLp,
       (cutBoundaryScalarValueTrace_memLp period hPeriod first).coeFn_toLp,
       (cutBoundaryScalarValueTrace_memLp period hPeriod second).coeFn_toLp,
       Lp.coeFn_add
        ((cutBoundaryScalarValueTrace_memLp period hPeriod first).toLp
          (cutBoundaryScalarValueTrace period hPeriod first))
        ((cutBoundaryScalarValueTrace_memLp period hPeriod second).toLp
          (cutBoundaryScalarValueTrace period hPeriod second))]
      with boundary hSum hFirst hSecond hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    exact cutBoundaryScalarValueTrace_add period hPeriod first second boundary
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [(cutBoundaryScalarValueTrace_memLp period hPeriod (scalar • field)).coeFn_toLp,
       (cutBoundaryScalarValueTrace_memLp period hPeriod field).coeFn_toLp,
       Lp.coeFn_smul scalar
        ((cutBoundaryScalarValueTrace_memLp period hPeriod field).toLp
          (cutBoundaryScalarValueTrace period hPeriod field))]
      with boundary hScaled hField hSmul
    rw [hScaled, hSmul, hField]
    exact cutBoundaryScalarValueTrace_smul
      period hPeriod scalar field boundary

/-- Smooth scalar normal trace in the physical cut-boundary L2 space. -/
def smoothCutBoundaryScalarNormalTraceL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalCutBoundaryScalarL2 period hPeriod where
  toFun field :=
    (cutBoundaryScalarNormalTrace_memLp period hPeriod field).toLp
      (cutBoundaryScalarNormalTrace period hPeriod field)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(cutBoundaryScalarNormalTrace_memLp period hPeriod (first + second)).coeFn_toLp,
       (cutBoundaryScalarNormalTrace_memLp period hPeriod first).coeFn_toLp,
       (cutBoundaryScalarNormalTrace_memLp period hPeriod second).coeFn_toLp,
       Lp.coeFn_add
        ((cutBoundaryScalarNormalTrace_memLp period hPeriod first).toLp
          (cutBoundaryScalarNormalTrace period hPeriod first))
        ((cutBoundaryScalarNormalTrace_memLp period hPeriod second).toLp
          (cutBoundaryScalarNormalTrace period hPeriod second))]
      with boundary hSum hFirst hSecond hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    exact cutBoundaryScalarNormalTrace_add period hPeriod first second boundary
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [(cutBoundaryScalarNormalTrace_memLp period hPeriod (scalar • field)).coeFn_toLp,
       (cutBoundaryScalarNormalTrace_memLp period hPeriod field).coeFn_toLp,
       Lp.coeFn_smul scalar
        ((cutBoundaryScalarNormalTrace_memLp period hPeriod field).toLp
          (cutBoundaryScalarNormalTrace period hPeriod field))]
      with boundary hScaled hField hSmul
    rw [hScaled, hSmul, hField]
    exact cutBoundaryScalarNormalTrace_smul
      period hPeriod scalar field boundary

/-- Agreement of the value L2 trace with the continuous representative. -/
theorem smoothCutBoundaryScalarValueTraceL2_ae
    (field : SmoothQuotientField period hPeriod Real) :
    (smoothCutBoundaryScalarValueTraceL2 period hPeriod field :
      CutThroatBoundary period hPeriod → Real) =ᵐ[
        cutBoundaryCanonicalMeasure period hPeriod]
      cutBoundaryScalarValueTrace period hPeriod field :=
  (cutBoundaryScalarValueTrace_memLp period hPeriod field).coeFn_toLp

/-- Agreement of the normal L2 trace with the continuous representative. -/
theorem smoothCutBoundaryScalarNormalTraceL2_ae
    (field : SmoothQuotientField period hPeriod Real) :
    (smoothCutBoundaryScalarNormalTraceL2 period hPeriod field :
      CutThroatBoundary period hPeriod → Real) =ᵐ[
        cutBoundaryCanonicalMeasure period hPeriod]
      cutBoundaryScalarNormalTrace period hPeriod field :=
  (cutBoundaryScalarNormalTrace_memLp period hPeriod field).coeFn_toLp

/-- Residual deck pullback on cut-boundary L2. -/
def cutBoundaryDeckL2Pullback :
    CanonicalCutBoundaryScalarL2 period hPeriod →L[Real]
      CanonicalCutBoundaryScalarL2 period hPeriod :=
  (Lp.compMeasurePreservingₗᵢ Real
    (orientationDeck period hPeriod)
    (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
      period hPeriod)).toContinuousLinearMap

/-- The deck L2 pullback is involutive. -/
theorem cutBoundaryDeckL2Pullback_involutive
    (boundaryField : CanonicalCutBoundaryScalarL2 period hPeriod) :
    cutBoundaryDeckL2Pullback period hPeriod
        (cutBoundaryDeckL2Pullback period hPeriod boundaryField) =
      boundaryField := by
  change Lp.compMeasurePreserving (orientationDeck period hPeriod) _
      (Lp.compMeasurePreserving (orientationDeck period hPeriod) _
        boundaryField) = boundaryField
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_compMeasurePreserving boundaryField
      ((cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
        period hPeriod).comp
        (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
          period hPeriod))]
    with boundary hBoundary
  simpa [Function.comp_def, orientationDeck_involutive] using hBoundary

/-- Smooth value traces lie in the deck-even L2 sector. -/
theorem cutBoundaryDeckL2Pullback_valueTrace
    (field : SmoothQuotientField period hPeriod Real) :
    cutBoundaryDeckL2Pullback period hPeriod
        (smoothCutBoundaryScalarValueTraceL2 period hPeriod field) =
      smoothCutBoundaryScalarValueTraceL2 period hPeriod field := by
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_compMeasurePreserving
      (smoothCutBoundaryScalarValueTraceL2 period hPeriod field)
      (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
        period hPeriod),
     smoothCutBoundaryScalarValueTraceL2_ae period hPeriod field,
     (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
        period hPeriod).quasiMeasurePreserving
       |>.ae_preimage
         (smoothCutBoundaryScalarValueTraceL2_ae period hPeriod field)]
    with boundary hDeck hValue hValueDeck
  rw [hDeck, hValueDeck, hValue]
  exact cutBoundaryScalarValueTrace_deck period hPeriod field boundary

/-- Smooth normal traces lie in the deck-odd L2 sector. -/
theorem cutBoundaryDeckL2Pullback_normalTrace
    (field : SmoothQuotientField period hPeriod Real) :
    cutBoundaryDeckL2Pullback period hPeriod
        (smoothCutBoundaryScalarNormalTraceL2 period hPeriod field) =
      -smoothCutBoundaryScalarNormalTraceL2 period hPeriod field := by
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_compMeasurePreserving
      (smoothCutBoundaryScalarNormalTraceL2 period hPeriod field)
      (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
        period hPeriod),
     smoothCutBoundaryScalarNormalTraceL2_ae period hPeriod field,
     (cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
        period hPeriod).quasiMeasurePreserving
       |>.ae_preimage
         (smoothCutBoundaryScalarNormalTraceL2_ae period hPeriod field),
     Lp.coeFn_neg
       (smoothCutBoundaryScalarNormalTraceL2 period hPeriod field)]
    with boundary hDeck hNormal hNormalDeck hNeg
  rw [hDeck, hNormalDeck, hNeg, hNormal]
  exact cutBoundaryScalarNormalTrace_deck period hPeriod field boundary

/-- Deck-even cut-boundary L2 sector. -/
def CutBoundaryEvenL2Submodule :
    Submodule Real (CanonicalCutBoundaryScalarL2 period hPeriod) :=
  LinearMap.ker
    ((cutBoundaryDeckL2Pullback period hPeriod).toLinearMap - LinearMap.id)

/-- Deck-odd cut-boundary L2 sector. -/
def CutBoundaryOddL2Submodule :
    Submodule Real (CanonicalCutBoundaryScalarL2 period hPeriod) :=
  LinearMap.ker
    ((cutBoundaryDeckL2Pullback period hPeriod).toLinearMap + LinearMap.id)

/-- The value trace lands in the even L2 sector. -/
def smoothCutBoundaryScalarValueTraceEvenL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CutBoundaryEvenL2Submodule period hPeriod where
  toFun field :=
    ⟨smoothCutBoundaryScalarValueTraceL2 period hPeriod field, by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        cutBoundaryDeckL2Pullback_valueTrace, sub_self]⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- The normal trace lands in the odd L2 sector. -/
def smoothCutBoundaryScalarNormalTraceOddL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CutBoundaryOddL2Submodule period hPeriod where
  toFun field :=
    ⟨smoothCutBoundaryScalarNormalTraceL2 period hPeriod field, by
      rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
        cutBoundaryDeckL2Pullback_normalTrace, neg_add_cancel]⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- Concrete parity-resolved L2 Cauchy-trace certificate. -/
theorem cutBoundaryScalarCauchyL2_certificate
    (field : SmoothQuotientField period hPeriod Real) :
    cutBoundaryDeckL2Pullback period hPeriod
        (smoothCutBoundaryScalarValueTraceL2 period hPeriod field) =
      smoothCutBoundaryScalarValueTraceL2 period hPeriod field ∧
    cutBoundaryDeckL2Pullback period hPeriod
        (smoothCutBoundaryScalarNormalTraceL2 period hPeriod field) =
      -smoothCutBoundaryScalarNormalTraceL2 period hPeriod field :=
  ⟨cutBoundaryDeckL2Pullback_valueTrace period hPeriod field,
    cutBoundaryDeckL2Pullback_normalTrace period hPeriod field⟩

end
end P0EFTJanusMappingTorusCutBoundaryScalarCauchyL24D
end JanusFormal
