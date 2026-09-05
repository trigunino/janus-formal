import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D

/-! # Local Einstein--Hilbert Palatini Stokes identity -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalEinsteinHilbertStokes4D

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
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D

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

/-- Metric-volume density of the actual Palatini scalar occurring in the
Einstein--Hilbert first variation. -/
def regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
    palatiniScalarVelocity
      (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
        (patch.coordinateMap coordinate))
      (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
        (patch.coordinateMap coordinate))

/-- The coordinate divergence density is exactly the density of the genuine
Einstein--Hilbert Palatini scalar. -/
theorem regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_ehDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch coordinate =
      regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
        metric tensor patch coordinate := by
  calc
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
          metric tensor patch coordinate =
        localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
          regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
            metric tensor patch coordinate :=
      regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_volume_mul
        period hPeriod metric tensor patch coordinate
    _ = localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
          regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
            tensor (patch.coordinateMap coordinate) := by
      rw [regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth]
    _ = regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
          metric tensor patch coordinate := by
      unfold regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity
      rw [regularGeneralMetricC0PalatiniScalarVelocity_eq_smoothDivergence]

/-- Concrete Stokes formula for the metric-volume density of the actual
Einstein--Hilbert Palatini scalar on every compact coordinate box. -/
theorem integral_regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity_eq_faces
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
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
  calc
    (∫ coordinate in Icc box.lower box.upper,
        regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
          metric tensor patch coordinate) =
      ∫ coordinate in Icc box.lower box.upper,
        regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
          metric tensor patch coordinate := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with coordinate
        exact
          (regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_ehDensity
            period hPeriod metric tensor patch coordinate).symm
    _ = _ :=
      integral_regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_faces
        period hPeriod metric tensor patch box

/-- Gate marker for the concrete local Einstein--Hilbert Stokes identity. -/
theorem regular_general_metric_c2_smooth_palatini_local_einstein_hilbert_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
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
  integral_regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity_eq_faces
    period hPeriod metric tensor patch box

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalEinsteinHilbertStokes4D
end JanusFormal
