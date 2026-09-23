import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! Bounded transport from regular ghost coefficients to the original normalized L² coordinates. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Transport4D
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
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)


open Set
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

def regularGhostNormalizedMatrix :
    Fin (finiteSmoothTangentFrame period hPeriod).count → Fin 4 → SmoothScalarField period hPeriod :=
  fun row column => globalNormalizedVectorCoordinate period hPeriod metric (reference.frame column) row

theorem regularGhostNormalizedMatrix_smooth
    (coefficients : Fin 4 → SmoothScalarField period hPeriod)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    globalNormalizedVectorCoordinate period hPeriod metric
      (regularFrameGhostFromCoefficients period hPeriod reference coefficients) row =
      ∑ column, canonicalScalarMul period hPeriod
        (regularGhostNormalizedMatrix period hPeriod reference metric row column) (coefficients column) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  simp only [canonicalScalarMul, LinearMap.coe_mk, AddHom.coe_mk,
    P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D.smoothScalarFieldMul,
    regularGhostNormalizedMatrix, globalNormalizedVectorCoordinate_apply,
    regularFrameGhostFromCoefficients_apply]
  unfold finiteTangentGeneratorLocalCoefficient
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  ring

def regularGhostL2Transport :
    CartanGhostL2 period hPeriod →L[Real] GlobalDiffeomorphismVectorL2 period hPeriod :=
  canonicalSmoothMatrixL2 period hPeriod (regularGhostNormalizedMatrix period hPeriod reference metric)

theorem regularGhostL2Transport_smooth (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularGhostL2Transport period hPeriod reference metric (regularFrameGhostL2 period hPeriod coefficients) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        (regularFrameGhostFromCoefficients period hPeriod reference coefficients) := by
  apply PiLp.ext
  intro row
  exact (canonicalSmoothMatrixL2_smooth period hPeriod
    (regularGhostNormalizedMatrix period hPeriod reference metric) coefficients row).trans
    (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (regularGhostNormalizedMatrix_smooth period hPeriod reference metric coefficients row).symm)

theorem regularGhostL2Transport_actual (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    regularGhostL2Transport period hPeriod reference metric
      (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost)) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric ghost := by
  rw [regularGhostL2Transport_smooth, regularFrameGhostFromCoefficients_reconstructs]

end
end JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Transport4D
