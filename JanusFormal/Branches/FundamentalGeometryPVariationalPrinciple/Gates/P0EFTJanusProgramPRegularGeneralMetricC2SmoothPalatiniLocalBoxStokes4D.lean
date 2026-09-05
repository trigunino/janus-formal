import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

/-! # Local box Stokes theorem for the smooth Palatini current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The holonomic coordinates of the genuine Palatini vector are smooth. -/
theorem regularGeneralMetricC2PalatiniVectorLocal_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
        patch) := by
  unfold regularGeneralMetricC2PalatiniVectorLocal
  apply ContDiff.sum
  intro index _
  have hCoefficient : ContDiff Real ∞ (fun coordinate =>
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor index
        (patch.coordinateMap coordinate)) :=
    ((regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor index
      ).contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff
  have hSmooth := hCoefficient.smul
    (pulledRegularFrameVector_contDiff period hPeriod metric patch index)
  convert hSmooth using 1
  funext coordinate
  rw [← regularFrameSmoothPalatiniCoefficient_apply]
  rfl

/-- Coordinate current `sqrt(|det g|) V` associated with the actual smooth
metric variation. -/
def regularGeneralMetricC2DensitizedPalatiniLocalCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Vector4 :=
  fun coordinate =>
    localMetricVolumeFactor period hPeriod metric.metric patch coordinate •
      regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
        patch coordinate

/-- The actual densitized coordinate current is smooth. -/
theorem regularGeneralMetricC2DensitizedPalatiniLocalCurrent_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
        metric tensor patch) := by
  exact (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch).smul
    (regularGeneralMetricC2PalatiniVectorLocal_contDiff period hPeriod metric
      tensor patch)

/-- Ordinary coordinate divergence of the actual densitized Palatini
current. -/
def regularGeneralMetricC2DensitizedPalatiniLocalDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ index : Index4,
    fderiv Real
        (regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
          metric tensor patch) coordinate (Pi.single index 1) index

/-- The coordinate divergence is integrable on every compact box. -/
theorem regularGeneralMetricC2DensitizedPalatiniLocalDivergence_integrableOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch) (Icc box.lower box.upper) := by
  have hCurrent :=
    regularGeneralMetricC2DensitizedPalatiniLocalCurrent_contDiff period hPeriod
      metric tensor patch
  have hDerivative : Continuous (fun coordinate =>
      fderiv Real
        (regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
          metric tensor patch) coordinate) :=
    hCurrent.continuous_fderiv (by simp)
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact Continuous.continuousOn (by
    unfold regularGeneralMetricC2DensitizedPalatiniLocalDivergence
    fun_prop)

/-- Concrete Bochner Stokes theorem for the actual smooth Palatini current on
every compact holonomic coordinate box. -/
theorem integral_regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_faces
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch coordinate) =
      ∑ index : Index4,
        ((∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
              metric tensor patch
                (index.insertNth (box.upper index) face) index) -
          ∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
              metric tensor patch
                (index.insertNth (box.lower index) face) index) := by
  let current :=
    regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod metric
      tensor patch
  let derivative : Vector4 → Vector4 →L[Real] Vector4 :=
    fun coordinate => fderiv Real current coordinate
  have hCurrent : ContDiff Real ∞ current :=
    regularGeneralMetricC2DensitizedPalatiniLocalCurrent_contDiff period hPeriod
      metric tensor patch
  have hStokes :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      box.lower box.upper box.lower_le_upper current derivative ∅
      Set.countable_empty hCurrent.continuous.continuousOn
      (fun coordinate _ =>
        (hCurrent.differentiable (by simp) coordinate).hasFDerivAt)
      (regularGeneralMetricC2DensitizedPalatiniLocalDivergence_integrableOn
        period hPeriod metric tensor patch box)
  simpa [current, derivative,
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence] using hStokes

/-- Gate marker for the unconditional local Stokes realization. -/
theorem regular_general_metric_c2_smooth_palatini_local_box_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch coordinate) =
      ∑ index : Index4,
        ((∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
              metric tensor patch
                (index.insertNth (box.upper index) face) index) -
          ∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
              metric tensor patch
                (index.insertNth (box.lower index) face) index) :=
  integral_regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_faces
    period hPeriod metric tensor patch box

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D
end JanusFormal
