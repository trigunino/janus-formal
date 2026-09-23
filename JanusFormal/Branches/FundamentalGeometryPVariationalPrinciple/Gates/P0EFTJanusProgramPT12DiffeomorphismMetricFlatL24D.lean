import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Bounded metric lowering and sector normalization of the shared BRST triplet. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

open P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D
open P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D
open P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric normalization : SmoothGeneralLorentzMetric period hPeriod)

def metricFlatMatrix : Fin (finiteSmoothTangentFrame period hPeriod).count → Fin 4 → SmoothScalarField period hPeriod :=
  fun row column => globalSmoothCovectorFrameCoefficient period hPeriod
    (globalSmoothMetricFlat period hPeriod metric (reference.frame column)) row

theorem metricFlatMatrix_smooth (coefficients : Fin 4 → SmoothScalarField period hPeriod)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    globalSmoothCovectorFrameCoefficient period hPeriod
      (globalSmoothMetricFlat period hPeriod metric
        (regularFrameGhostFromCoefficients period hPeriod reference coefficients)) row =
      ∑ column, canonicalScalarMul period hPeriod (metricFlatMatrix period hPeriod reference metric row column)
        (coefficients column) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  change metric.tensor.tensor point (regularFrameGhostFromCoefficients period hPeriod reference coefficients point)
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point row) =
    ∑ column, metric.tensor.tensor point (reference.frame column point)
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point row) * coefficients column point
  rw [regularFrameGhostFromCoefficients_apply]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro column _
  ring

def metricFlatL2 : CartanGhostL2 period hPeriod →L[Real] GlobalDiffeomorphismVectorL2 period hPeriod :=
  canonicalSmoothMatrixL2 period hPeriod (metricFlatMatrix period hPeriod reference metric)

theorem metricFlatL2_smooth (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    metricFlatL2 period hPeriod reference metric (regularFrameGhostL2 period hPeriod coefficients) =
      globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
        (regularFrameGhostFromCoefficients period hPeriod reference coefficients) := by
  apply PiLp.ext
  intro row
  exact (canonicalSmoothMatrixL2_smooth period hPeriod (metricFlatMatrix period hPeriod reference metric) coefficients row).trans
    (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (metricFlatMatrix_smooth period hPeriod reference metric coefficients row).symm)

theorem metricFlatL2_actual (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    metricFlatL2 period hPeriod reference metric
      (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost)) =
      globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric ghost := by
  rw [metricFlatL2_smooth, regularFrameGhostFromCoefficients_reconstructs]

def sectorTripletL2 (index : Fin 3) : DiffeomorphismL2 period hPeriod normalization →L[Real]
    GlobalDiffeomorphismVectorL2 period hPeriod :=
  (regularGhostL2Transport period hPeriod reference metric).comp
    ((regularGhostL2Recovery period hPeriod reference normalization).comp
      (diffeomorphismTripletReadout period hPeriod normalization index))

theorem sectorTripletL2_smooth (index : Fin 3) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference metric normalization index (diffeomorphismL2Smooth period hPeriod normalization field) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        (![field.nonminimal.ghost.field, field.nonminimal.antighost.field, field.nonminimal.nakanishiLautrup.field] index) := by
  simp only [sectorTripletL2, ContinuousLinearMap.comp_apply, diffeomorphismTripletReadout_smooth,
    regularGhostL2Recovery_actual, regularGhostL2Transport_actual]

def sectorTripletFlatL2 (index : Fin 3) : DiffeomorphismL2 period hPeriod normalization →L[Real]
    GlobalDiffeomorphismVectorL2 period hPeriod :=
  (metricFlatL2 period hPeriod reference metric).comp
    ((regularGhostL2Recovery period hPeriod reference normalization).comp
      (diffeomorphismTripletReadout period hPeriod normalization index))

theorem sectorTripletFlatL2_smooth (index : Fin 3) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletFlatL2 period hPeriod reference metric normalization index (diffeomorphismL2Smooth period hPeriod normalization field) =
      globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
        (![field.nonminimal.ghost.field, field.nonminimal.antighost.field, field.nonminimal.nakanishiLautrup.field] index) := by
  simp only [sectorTripletFlatL2, ContinuousLinearMap.comp_apply, diffeomorphismTripletReadout_smooth,
    regularGhostL2Recovery_actual, metricFlatL2_actual]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
