import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! Exact paired FP adjunction in canonical L2. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
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

def pairedFPCanonicalAdjointSmooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] GlobalPairedGaugeLieSmooth period hPeriod where
  toFun test sector := canonicalFPFormalAdjoint period hPeriod (metric sector) (test sector)
  map_add' first second := by
    funext sector
    exact map_add (canonicalFPFormalAdjoint period hPeriod (metric sector)) _ _
  map_smul' scalar test := by
    funext sector
    exact map_smul (canonicalFPFormalAdjoint period hPeriod (metric sector)) _ _

def pairedFPCanonicalAdjointL2
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedGaugeLieL2LinearMap period hPeriod).comp
    (pairedFPCanonicalAdjointSmooth period hPeriod metric)

theorem pairedFPCanonicalAdjoint_pairing
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (field test : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod (fun sector => (metric sector).metric) field)
        (globalPairedGaugeLieL2LinearMap period hPeriod test) =
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
        (pairedFPCanonicalAdjointL2 period hPeriod (fun sector => (metric sector).metric) test) := by
  change inner Real (globalPairedGaugeLieL2LinearMap period hPeriod
    (fun sector => globalGeneralMetricAbelianFaddeevPopov period hPeriod (metric sector).metric (field sector)))
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
      (globalPairedGaugeLieL2LinearMap period hPeriod
        (fun sector => canonicalFPFormalAdjoint period hPeriod (metric sector).metric (test sector)))
  rw [globalPairedGaugeLieL2_inner_eq_sum_integral, globalPairedGaugeLieL2_inner_eq_sum_integral]
  apply Finset.sum_congr rfl
  intro sector _
  unfold globalGaugeLiePairingAt
  rw [integral_finsetSum Finset.univ (fun component _ =>
    globalGaugeLieComponentProduct_integrable period hPeriod _ _ component),
    integral_finsetSum Finset.univ (fun component _ =>
      globalGaugeLieComponentProduct_integrable period hPeriod _ _ component)]
  apply Finset.sum_congr rfl
  intro component _
  exact canonicalFPFormalAdjoint_component_pairing period hPeriod (metric sector) (field sector) (test sector) component

end
end P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
end JanusFormal
