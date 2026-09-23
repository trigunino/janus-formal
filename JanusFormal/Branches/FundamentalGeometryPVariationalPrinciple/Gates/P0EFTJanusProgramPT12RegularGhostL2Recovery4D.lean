import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Transport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D

/-! Recovery of regular ghost coefficients from the original normalized L² coordinates. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
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

open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

def regularGhostRecoveryMatrix :
    Fin 4 → Fin (finiteSmoothTangentFrame period hPeriod).count → SmoothScalarField period hPeriod :=
  fun row column => canonicalScalarMul period hPeriod (inverseSmoothMetricRatio period hPeriod metric)
    (regularFrameCartanGhostCoefficient period hPeriod reference
      (frameTangentField period hPeriod (finiteSmoothTangentFrame period hPeriod) column) row)

theorem regularGhostRecoveryMatrix_smooth (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (row : Fin 4) :
    (∑ column, canonicalScalarMul period hPeriod
      (regularGhostRecoveryMatrix period hPeriod reference metric row column)
      (globalNormalizedVectorCoordinate period hPeriod metric ghost column)) =
      regularFrameCartanGhostCoefficient period hPeriod reference ghost row := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  let dual := generalMetricFiniteFrameCoefficientAt period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric point row
  have hPair := globalFiniteTangentPairingFactorizationPublic period hPeriod point dual (ghost point)
  have hRatio := (globalMetricVolumeRatio_pos period hPeriod metric point).ne'
  have hWeight := (globalFiniteTangentWeightSquareSum_pos period hPeriod point).ne'
  change (∑ column, ((globalMetricVolumeRatio period hPeriod metric point)⁻¹ *
    dual ((finiteSmoothTangentFrame period hPeriod).vectorAt point column)) *
    globalNormalizedVectorCoordinate period hPeriod metric ghost column point) = dual (ghost point)
  simp only [globalNormalizedVectorCoordinate_apply]
  simp only [globalGeneralMetricDeDonderPairingNormalization]
  calc
    _ = ((globalMetricVolumeRatio period hPeriod metric point)⁻¹ *
        (globalMetricVolumeRatio period hPeriod metric point /
          globalFiniteTangentWeightSquareSum period hPeriod point)) *
        (globalFiniteTangentWeightSquareSum period hPeriod point * dual (ghost point)) := by
      rw [← hPair, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring
    _ = dual (ghost point) := by field_simp

def regularGhostL2Recovery :
    GlobalDiffeomorphismVectorL2 period hPeriod →L[Real] CartanGhostL2 period hPeriod :=
  canonicalSmoothMatrixL2 period hPeriod (regularGhostRecoveryMatrix period hPeriod reference metric)

theorem regularGhostL2Recovery_actual (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    regularGhostL2Recovery period hPeriod reference metric
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric ghost) =
      regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost) := by
  apply PiLp.ext
  intro row
  exact (canonicalSmoothMatrixL2_smooth period hPeriod
    (regularGhostRecoveryMatrix period hPeriod reference metric)
    (globalNormalizedVectorCoordinate period hPeriod metric ghost) row).trans
    (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (regularGhostRecoveryMatrix_smooth period hPeriod reference metric ghost row))

theorem regularFrameGhostFromCoefficients_injective :
    Function.Injective (regularFrameGhostFromCoefficients period hPeriod reference) := by
  intro first second h
  funext row
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hPoint := congrArg (fun ghost : CInfinityDiffeomorphismGhost period hPeriod =>
    (reference.frameEquiv point).symm (ghost point)) h
  simp only [regularFrameGhostFromCoefficients_apply, map_sum, map_smul,
    RegularGeneralLorentzMetric.frame_eq_basisFun, ContinuousLinearEquiv.symm_apply_apply] at hPoint
  have hFirst := (Pi.basisFun Real (Fin 4)).sum_repr (fun index => first index point)
  have hSecond := (Pi.basisFun Real (Fin 4)).sum_repr (fun index => second index point)
  exact congrArg (fun coordinates : Fin 4 → Real => coordinates row)
    (hFirst.symm.trans (hPoint.trans hSecond))

theorem regularFrameGhostCoefficients_reconstructed
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameCartanGhostCoefficient period hPeriod reference
      (regularFrameGhostFromCoefficients period hPeriod reference coefficients) = coefficients :=
  regularFrameGhostFromCoefficients_injective period hPeriod reference
    (regularFrameGhostFromCoefficients_reconstructs period hPeriod reference _)

theorem regularGhostL2Recovery_transport (field : CartanGhostL2 period hPeriod) :
    regularGhostL2Recovery period hPeriod reference metric
      (regularGhostL2Transport period hPeriod reference metric field) = field := by
  have hClosed : IsClosed {field : CartanGhostL2 period hPeriod |
      regularGhostL2Recovery period hPeriod reference metric
        (regularGhostL2Transport period hPeriod reference metric field) = field} :=
    isClosed_eq ((regularGhostL2Recovery period hPeriod reference metric).continuous.comp
      (regularGhostL2Transport period hPeriod reference metric).continuous) continuous_id
  have hAll : (Set.univ : Set (CartanGhostL2 period hPeriod)) ⊆
      {field | regularGhostL2Recovery period hPeriod reference metric
        (regularGhostL2Transport period hPeriod reference metric field) = field} := by
    rw [← (regularFrameGhostL2_denseRange period hPeriod).closure_range]
    apply closure_minimal _ hClosed
    rintro _ ⟨coefficients, rfl⟩
    change regularGhostL2Recovery period hPeriod reference metric
      (regularGhostL2Transport period hPeriod reference metric (regularFrameGhostL2 period hPeriod coefficients)) = _
    rw [regularGhostL2Transport_smooth, regularGhostL2Recovery_actual,
      regularFrameGhostCoefficients_reconstructed]
  exact hAll (Set.mem_univ field)

theorem regularGhostL2Transport_injective :
    Function.Injective (regularGhostL2Transport period hPeriod reference metric) :=
  Function.LeftInverse.injective (regularGhostL2Recovery_transport period hPeriod reference metric)

end
end JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
