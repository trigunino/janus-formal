import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalEinsteinHilbertStokes4D

/-! # Local invariant Einstein residual with exact Palatini face flux -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertLocalInvariantStokes4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalEinsteinHilbertStokes4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev Index4 := Fin 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Coordinate density of the invariant Einstein bulk residual. -/
def regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  -(localMetricVolumeFactor period hPeriod metric.metric patch coordinate /
      (2 * couplings.gravitationalCoupling)) *
    generalMetricTensorPairingAt period hPeriod metric.metric
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        couplings.cosmologicalConstant) tensor (patch.coordinateMap coordinate)

/-- Coordinate form of the complete EH first-variation density before
Stokes, using the genuine holonomic metric volume. -/
def regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  localMetricVolumeFactor period hPeriod metric.metric patch coordinate /
      (2 * couplings.gravitationalCoupling) *
    (tensorPairing
        (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
          (patch.coordinateMap coordinate))
        (einsteinTensorAt
          (regularFrameMetricMatrixMap period hPeriod metric
            (patch.coordinateMap coordinate))
          (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
            (patch.coordinateMap coordinate))
          (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0
            (patch.coordinateMap coordinate))
          couplings.cosmologicalConstant) +
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
        tensor (patch.coordinateMap coordinate))

/-- Oriented face flux of the actual densitized Palatini current. -/
def regularGeneralMetricC2PalatiniLocalOrientedFaceFlux
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) : Real :=
  ∑ index : Index4,
    ((∫ face in
          Icc (box.lower ∘ index.succAbove) (box.upper ∘ index.succAbove),
        regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
          metric tensor patch (index.insertNth (box.upper index) face) index) -
      ∫ face in
          Icc (box.lower ∘ index.succAbove) (box.upper ∘ index.succAbove),
        regularGeneralMetricC2DensitizedPalatiniLocalCurrent period hPeriod
          metric tensor patch (index.insertNth (box.lower index) face) index)

/-- Pointwise split into invariant bulk density and densitized Palatini
divergence. -/
theorem regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity_split
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity period
        hPeriod metric couplings tensor patch coordinate =
      regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity period
          hPeriod metric couplings tensor patch coordinate +
        (1 / (2 * couplings.gravitationalCoupling)) *
          regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period
            hPeriod metric tensor patch coordinate := by
  unfold regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity
    regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity
    regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity
  rw [regularGeneralMetricC0EinsteinInverseVelocity_pairing_invariant]
  rw [regularGeneralMetricC0PalatiniScalarVelocity_eq_smoothDivergence]
  ring

private theorem invariantLocalBulkDensity_integrableOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity period
        hPeriod metric couplings tensor patch)
      (Icc box.lower box.upper) := by
  have hVolume :=
    localMetricVolumeFactor_continuous period hPeriod metric.metric patch
  have hPairing :=
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        couplings.cosmologicalConstant) tensor).comp
      patch.coordinateMap_contMDiff.continuous
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact ((hVolume.div_const _).neg.mul hPairing).continuousOn

private theorem palatiniEinsteinHilbertLocalDensity_integrableOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity period hPeriod
        metric tensor patch) (Icc box.lower box.upper) := by
  have hDivergence :=
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence_integrableOn
      period hPeriod metric tensor patch box
  exact hDivergence.congr (Filter.Eventually.of_forall fun coordinate =>
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_ehDensity
      period hPeriod metric tensor patch coordinate)

/-- Exact local EH identity: the Palatini contribution is entirely the
oriented face flux, while the bulk is the invariant Einstein residual. -/
theorem integral_regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity_eq_invariantBulk_add_faces
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity period
        hPeriod metric couplings tensor patch coordinate) =
      (∫ coordinate in Icc box.lower box.upper,
        regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity period
          hPeriod metric couplings tensor patch coordinate) +
        (1 / (2 * couplings.gravitationalCoupling)) *
          regularGeneralMetricC2PalatiniLocalOrientedFaceFlux period hPeriod
            metric tensor patch box := by
  let bulk := regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity
    period hPeriod metric couplings tensor patch
  let palatini := regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity
    period hPeriod metric tensor patch
  have hBulk : IntegrableOn bulk (Icc box.lower box.upper) :=
    invariantLocalBulkDensity_integrableOn period hPeriod metric couplings
      tensor patch box
  have hPalatini : IntegrableOn palatini (Icc box.lower box.upper) :=
    palatiniEinsteinHilbertLocalDensity_integrableOn period hPeriod metric
      tensor patch box
  calc
    _ = ∫ coordinate in Icc box.lower box.upper,
        (bulk coordinate +
          (1 / (2 * couplings.gravitationalCoupling)) *
            palatini coordinate) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun coordinate =>
        regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity_split
          period hPeriod metric couplings tensor patch coordinate
    _ = (∫ coordinate in Icc box.lower box.upper, bulk coordinate) +
        ∫ coordinate in Icc box.lower box.upper,
          (1 / (2 * couplings.gravitationalCoupling)) *
            palatini coordinate := integral_add hBulk (hPalatini.const_mul _)
    _ = _ := by
      rw [integral_const_mul]
      unfold bulk palatini regularGeneralMetricC2PalatiniLocalOrientedFaceFlux
      rw [integral_regularGeneralMetricC2PalatiniEinsteinHilbertLocalDensity_eq_faces]

/-- Gate marker for the invariant local metric PDE and exact Palatini flux. -/
theorem regular_general_metric_c2_einstein_hilbert_local_invariant_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity period
        hPeriod metric couplings tensor patch coordinate) =
      (∫ coordinate in Icc box.lower box.upper,
        regularGeneralMetricC2EinsteinHilbertInvariantLocalBulkDensity period
          hPeriod metric couplings tensor patch coordinate) +
        (1 / (2 * couplings.gravitationalCoupling)) *
          regularGeneralMetricC2PalatiniLocalOrientedFaceFlux period hPeriod
            metric tensor patch box :=
  integral_regularGeneralMetricC2EinsteinHilbertLocalFirstVariationDensity_eq_invariantBulk_add_faces
    period hPeriod metric couplings tensor patch box

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertLocalInvariantStokes4D
end JanusFormal
