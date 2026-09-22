import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12L2VolumeMultiplier4D

/-! Concrete bounded volume transport, including its smooth-core action. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12PairedVolumeEquiv4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D


local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
set_option backward.isDefEq.respectTransparency false

open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D
open scoped BoundedContinuousFunction

/-- The actual smooth positive ratio, bounded by compactness. -/
def boundedMetricRatio (metric : SmoothGeneralLorentzMetric period hPeriod) :
    EffectiveQuotient period hPeriod →ᵇ Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨globalSmoothMetricVolumeRatio period hPeriod metric,
      (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.continuous⟩

def boundedInverseMetricRatio (metric : SmoothGeneralLorentzMetric period hPeriod) :
    EffectiveQuotient period hPeriod →ᵇ Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨inverseSmoothMetricRatio period hPeriod metric,
      (inverseSmoothMetricRatio period hPeriod metric).contMDiff_toFun.continuous⟩

def metricVolumeL2Equiv (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CanonicalPhysicalBulkL2 period hPeriod ≃L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  l2VolumeEquiv (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (boundedMetricRatio period hPeriod metric) (boundedInverseMetricRatio period hPeriod metric)
    (fun point => mul_inv_cancel₀ (globalMetricVolumeRatio_pos period hPeriod metric point).ne')

/-- Multiplication by the actual sectorwise volume ratio on the full canonical paired L2. -/
def pairedVolumeL2Equiv (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieL2 period hPeriod ≃L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Sector × Fin 2 => CanonicalPhysicalBulkL2 period hPeriod)).trans
    ((ContinuousLinearEquiv.piCongrRight (fun index : Sector × Fin 2 =>
      metricVolumeL2Equiv period hPeriod (metric index.1))).trans
      (PiLp.continuousLinearEquiv 2 Real (fun _ : Sector × Fin 2 => CanonicalPhysicalBulkL2 period hPeriod)).symm)

def pairedSmoothVolumeWeight (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] GlobalPairedGaugeLieSmooth period hPeriod where
  toFun field sector := smoothGaugeWeight period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod (metric sector)) (field sector)
  map_add' first second := by funext sector; exact map_add _ _ _
  map_smul' scalar field := by
    funext sector
    exact map_smul (smoothGaugeWeight period hPeriod
      (globalSmoothMetricVolumeRatio period hPeriod (metric sector))) scalar (field sector)

def pairedSmoothInverseVolumeWeight (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] GlobalPairedGaugeLieSmooth period hPeriod where
  toFun field sector := smoothGaugeWeight period hPeriod
    (inverseSmoothMetricRatio period hPeriod (metric sector)) (field sector)
  map_add' first second := by funext sector; exact map_add _ _ _
  map_smul' scalar field := by
    funext sector
    exact map_smul (smoothGaugeWeight period hPeriod
      (inverseSmoothMetricRatio period hPeriod (metric sector))) scalar (field sector)

theorem pairedVolumeL2Equiv_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedVolumeL2Equiv period hPeriod metric (globalPairedGaugeLieL2LinearMap period hPeriod field) =
      globalPairedGaugeLieL2LinearMap period hPeriod (pairedSmoothVolumeWeight period hPeriod metric field) := by
  apply PiLp.ext
  intro index
  apply Lp.ext
  filter_upwards [l2VolumeMultiplier_ae (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (boundedMetricRatio period hPeriod (metric index.1))
    (globalGaugeLieFieldL2Coordinates period hPeriod (field index.1) index.2),
    smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod (field index.1) index.2),
    smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod (pairedSmoothVolumeWeight period hPeriod metric field index.1) index.2)]
    with point hMul hField hWeighted
  exact hMul.trans ((congrArg (fun value : Real =>
    globalMetricVolumeRatio period hPeriod (metric index.1) point * value) hField).trans hWeighted.symm)

theorem pairedSmoothVolumeWeight_inverse
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedSmoothVolumeWeight period hPeriod metric (pairedSmoothInverseVolumeWeight period hPeriod metric field) = field := by
  funext sector
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  change globalMetricVolumeRatio period hPeriod (metric sector) point •
    ((globalMetricVolumeRatio period hPeriod (metric sector) point)⁻¹ • field sector point) = _
  rw [smul_smul, mul_inv_cancel₀ (globalMetricVolumeRatio_pos period hPeriod (metric sector) point).ne', one_smul]

theorem pairedVolumeL2Equiv_symm_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    (pairedVolumeL2Equiv period hPeriod metric).symm (globalPairedGaugeLieL2LinearMap period hPeriod field) =
      globalPairedGaugeLieL2LinearMap period hPeriod (pairedSmoothInverseVolumeWeight period hPeriod metric field) := by
  apply (pairedVolumeL2Equiv period hPeriod metric).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, pairedVolumeL2Equiv_smooth, pairedSmoothVolumeWeight_inverse]

theorem pairedVolumeL2Equiv_symmetric
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedGaugeLieL2 period hPeriod) :
    inner Real (pairedVolumeL2Equiv period hPeriod metric first) second =
      inner Real first (pairedVolumeL2Equiv period hPeriod metric second) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro index _
  exact l2VolumeMultiplier_symmetric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (boundedMetricRatio period hPeriod (metric index.1)) (first index) (second index)

end
end P0EFTJanusProgramPT12PairedVolumeEquiv4D
end JanusFormal
