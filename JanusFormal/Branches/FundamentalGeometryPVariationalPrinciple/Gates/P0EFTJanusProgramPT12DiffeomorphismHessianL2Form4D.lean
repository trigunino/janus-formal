import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderL2Closed4D
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

/-! Exact signed BRST Hessian on the common L² differential-feature domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D
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

open P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
open P0EFTJanusProgramPT12DeDonderL2Closed4D

open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
open P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
open P0EFTJanusProgramPT12SignedBRSTGram4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

def auxiliarySectorL2Riesz (sector : Sector) : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  -(1 / 2 : Real) • signedCross (H := DiffeomorphismL2 period hPeriod (metric .plus))
    (V := GlobalDiffeomorphismVectorL2 period hPeriod)
    (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2)

theorem auxiliarySectorL2Riesz_pairing (sector : Sector) (first second : DiffeomorphismL2 period hPeriod (metric .plus)) :
    inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector first) second =
      -(1 / 2 : Real) *
        (inner Real (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 first)
          (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second) +
        inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first)
          (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 second)) := by
  change inner Real (-(1 / 2 : Real) •
    (signedCross (H := DiffeomorphismL2 period hPeriod (metric .plus))
      (V := GlobalDiffeomorphismVectorL2 period hPeriod)
      (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2)
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2) first)) second = _
  let p : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real] GlobalDiffeomorphismVectorL2 period hPeriod :=
    sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
  let q : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real] GlobalDiffeomorphismVectorL2 period hPeriod :=
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
  have h := signedCross_pairing (H := DiffeomorphismL2 period hPeriod (metric .plus))
    (V := GlobalDiffeomorphismVectorL2 period hPeriod) p q first second
  exact (real_inner_smul_left (signedCross p q first) second (-(1 / 2 : Real))).trans
    (congrArg (fun value : Real => -(1 / 2 : Real) * value)
      h)

def hessianSectorForm (sector : Sector) (first second : (hessianFeatureMinimal period hPeriod metric).domain) : Real :=
  inner Real ((hessianFeatureMinimal period hPeriod metric first (0, sector)).val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second.val) +
  inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    ((hessianFeatureMinimal period hPeriod metric second (0, sector)).val) -
  (1 / 2 : Real) * inner Real (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second.val) -
  (1 / 2 : Real) * inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 second.val) -
  inner Real ((hessianFeatureMinimal period hPeriod metric first (1, sector)).val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 second.val) -
  inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 first.val)
    ((hessianFeatureMinimal period hPeriod metric second (1, sector)).val)

theorem hessianSectorForm_comm (sector : Sector) (first second : (hessianFeatureMinimal period hPeriod metric).domain) :
    hessianSectorForm period hPeriod reference metric sector first second =
      hessianSectorForm period hPeriod reference metric sector second first := by
  let d := (hessianFeatureMinimal period hPeriod metric first (0, sector)).val
  let e := (hessianFeatureMinimal period hPeriod metric second (0, sector)).val
  let b := sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val
  let a := sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second.val
  let p := sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val
  let q := sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 second.val
  let f := (hessianFeatureMinimal period hPeriod metric first (1, sector)).val
  let g := (hessianFeatureMinimal period hPeriod metric second (1, sector)).val
  let c := sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 first.val
  let k := sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 second.val
  change inner Real d a + inner Real b e - (1 / 2 : Real) * inner Real p a -
    (1 / 2 : Real) * inner Real b q - inner Real f k - inner Real c g =
    inner Real e b + inner Real a d - (1 / 2 : Real) * inner Real q b -
    (1 / 2 : Real) * inner Real a p - inner Real g c - inner Real k f
  rw [real_inner_comm e b, real_inner_comm a d, real_inner_comm q b,
    real_inner_comm a p, real_inner_comm g c, real_inner_comm k f]
  ring

theorem hessianSectorForm_add_left (sector : Sector) (first second test : (hessianFeatureMinimal period hPeriod metric).domain) :
    hessianSectorForm period hPeriod reference metric sector (first + second) test =
      hessianSectorForm period hPeriod reference metric sector first test +
        hessianSectorForm period hPeriod reference metric sector second test := by
  simp only [hessianSectorForm, LinearPMap.map_add, Submodule.coe_add, map_add, PiLp.add_apply,
    inner_add_left]
  ring

theorem hessianSectorForm_smul_left (sector : Sector) (scalar : Real)
    (first test : (hessianFeatureMinimal period hPeriod metric).domain) :
    hessianSectorForm period hPeriod reference metric sector (scalar • first) test =
      scalar * hessianSectorForm period hPeriod reference metric sector first test := by
  simp only [hessianSectorForm, LinearPMap.map_smul, Submodule.coe_smul, map_smul, PiLp.smul_apply,
    real_inner_smul_left]
  ring

theorem hessianSectorForm_smooth (sector : Sector)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSectorForm period hPeriod reference metric sector
      (hessianFeatureSmoothDomain period hPeriod metric first) (hessianFeatureSmoothDomain period hPeriod metric second) =
    globalDiffeomorphismOffShellHessian period hPeriod (metric sector)
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric sector)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod sector first))
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric sector)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod sector second)) := by
  rw [globalDiffeomorphismOffShellHessian_apply]
  simp only [hessianSectorForm, hessianFeatureMinimal_smooth]
  simp only [hessianFeatureSmoothDomain,
    hessianFeaturesSmooth_deDonder, hessianFeaturesSmooth_fp, actualFPSmoothOutput_original,
    sectorTripletL2_smooth, sectorTripletFlatL2_smooth,
    globalDiffeomorphismOffShellDeDonderProjection_smooth, globalDiffeomorphismOffShellBProjection_smooth,
    globalDiffeomorphismOffShellBFlatProjection_smooth, globalDiffeomorphismOffShellFPProjection_smooth,
    globalDiffeomorphismOffShellAntighostProjection_smooth]
  rfl

def hessianL2Form (couplings : GlobalCandidateAActionCouplings)
    (first second : (hessianFeatureMinimal period hPeriod metric).domain) : Real :=
  candidateAPlusEinsteinKineticWeight couplings * hessianSectorForm period hPeriod reference metric .plus first second +
    candidateAMinusEinsteinKineticWeight couplings * hessianSectorForm period hPeriod reference metric .minus first second

theorem hessianL2Form_comm (couplings : GlobalCandidateAActionCouplings)
    (first second : (hessianFeatureMinimal period hPeriod metric).domain) :
    hessianL2Form period hPeriod reference metric couplings first second =
      hessianL2Form period hPeriod reference metric couplings second first := by
  unfold hessianL2Form
  rw [hessianSectorForm_comm period hPeriod reference metric .plus first second,
    hessianSectorForm_comm period hPeriod reference metric .minus first second]

theorem hessianL2Form_smooth_eq_actual (couplings : GlobalCandidateAActionCouplings)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianL2Form period hPeriod reference metric couplings
      (hessianFeatureSmoothDomain period hPeriod metric first) (hessianFeatureSmoothDomain period hPeriod metric second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric first second := by
  rw [← globalCandidateADiagonalDiffeomorphismOffShellHessian_smooth_eq_BRST,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
  simp only [hessianL2Form, hessianSectorForm_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D
