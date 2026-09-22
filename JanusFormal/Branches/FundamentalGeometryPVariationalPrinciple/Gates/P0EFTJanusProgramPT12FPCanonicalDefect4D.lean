import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPClosable4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

/-! Exact canonical adjoint correction in the actual ghost mixed Hessian. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12FPCanonicalDefect4D
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

open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

open P0EFTJanusProgramPT12PairedFPClosable4D
open P0EFTJanusProgramPT12GhostRotationDefect4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

/-- The exact canonical-volume correction, without a presumed symmetry. -/
def pairedFPCanonicalCorrection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  pairedFPCanonicalAdjointL2 period hPeriod metric -
    globalPairedAbelianFPL2LinearMap period hPeriod metric

theorem pairedFPDefect_eq_canonicalCorrection
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (fun sector => (metric sector).metric)) first second =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod first)
      (pairedFPCanonicalCorrection period hPeriod (fun sector => (metric sector).metric) second) := by
  unfold fpPairingDefect pairedFPCanonicalCorrection
  rw [LinearMap.sub_apply, inner_sub_right, pairedFPCanonicalAdjoint_pairing]

theorem pairedFPDefect_all_zero_iff_canonicalCorrection_zero
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (second : GlobalPairedGaugeLieSmooth period hPeriod) :
    (∀ first, fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (fun sector => (metric sector).metric)) first second = 0) ↔
    pairedFPCanonicalCorrection period hPeriod (fun sector => (metric sector).metric) second = 0 := by
  simp only [pairedFPDefect_eq_canonicalCorrection]
  constructor
  · intro hZero
    have hAll : (fun x : GlobalPairedGaugeLieL2 period hPeriod => inner Real x
        (pairedFPCanonicalCorrection period hPeriod (fun sector => (metric sector).metric) second)) =
        (fun x => inner Real x (0 : GlobalPairedGaugeLieL2 period hPeriod)) := by
      apply (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod).equalizer
      · fun_prop
      · fun_prop
      · funext first
        exact (hZero first).trans (inner_zero_right _).symm
    exact ext_inner_left Real (congrFun hAll)
  · intro hZero first
    rw [hZero, inner_zero_right]

/-- Weak adjunction remains exact on every vector of the closed FP graph. -/
theorem canonicalPairedFPGraph_adjoint_pairing
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (graph : CanonicalPairedFPGraph period hPeriod (fun sector => (metric sector).metric))
    (test : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real graph.val.2 (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real graph.val.1
      (pairedFPCanonicalAdjointL2 period hPeriod (fun sector => (metric sector).metric) test) :=
  linearFeatureGraphClosure_pairing _ _ _
    (pairedFPCanonicalAdjoint_pairing period hPeriod metric) graph test

/-- The actual mixed ghost Hessian reads the canonical adjoint correction. -/
theorem regularGhostRotation_mixed_hessian
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod (fun sector => (metric sector).metric)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun sector => (metric sector).metric)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • first) ((1 / 2 : Real) • first)))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun sector => (metric sector).metric)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • second) (-(1 / 2 : Real) • second))) =
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod first)
        (pairedFPCanonicalCorrection period hPeriod (fun sector => (metric sector).metric) second) / 4 := by
  rw [pureAbelianGhostPair_hessian, ghostCrossPairing_mixed_signed,
    pairedFPDefect_eq_canonicalCorrection]

end
end P0EFTJanusProgramPT12FPCanonicalDefect4D
end JanusFormal
