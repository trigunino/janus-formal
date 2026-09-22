import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TwoSidedGhostPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzShearPairing4D

/-! Continuous signed realization and exact Hessian on the completed two-sided graph. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

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

open P0EFTJanusProgramPT12GhostRotationDefect4D

open P0EFTJanusProgramPT12TwoSidedGhostAmbient4D
open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPT12NilpotentGraphShear4D

open P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
open P0EFTJanusProgramPT12AbelianLorenzShearPairing4D
open P0EFTJanusProgramPT12TwoSidedGhostPairing4D

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

/-- Inverse ghost rotation and Lorenz shear, on the whole strengthened graph. -/
def abelianTwoSidedSignedRealization :
    AbelianTwoSidedGraph period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (abelianLorenzGraphShear period hPeriod metric).toContinuousLinearMap.comp
    ((abelianTwoSidedForget period hPeriod metric).comp
      (abelianTwoSidedGhostRotation period hPeriod metric).symm.toContinuousLinearMap)

theorem abelianTwoSidedSignedRealization_denseRange :
    DenseRange (abelianTwoSidedSignedRealization period hPeriod metric) :=
  (abelianLorenzGraphShear period hPeriod metric).surjective.denseRange.comp
    ((abelianTwoSidedForget_denseRange period hPeriod metric).comp
      (abelianTwoSidedGhostRotation period hPeriod metric).symm.surjective.denseRange
      (abelianTwoSidedForget period hPeriod metric).continuous)
    (abelianLorenzGraphShear period hPeriod metric).continuous

theorem abelianTwoSidedSignedRealization_smooth
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianTwoSidedSignedRealization period hPeriod metric
        (abelianTwoSidedSmoothEmbedding period hPeriod metric state) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod state +
          abelianLorenzSmoothIncrement period hPeriod metric
            (abelianGhostSignedReconstruct period hPeriod state)) := by
  change abelianLorenzGraphShear period hPeriod metric
    (abelianTwoSidedForget period hPeriod metric
      ((abelianTwoSidedGhostRotation period hPeriod metric).symm
        (abelianTwoSidedSmoothEmbedding period hPeriod metric state))) = _
  rw [abelianTwoSidedGhostRotation_inverse_smooth, abelianTwoSidedForget_smooth]
  exact abelianLorenzGraphShear_smooth period hPeriod metric _

/-- The true completed Hessian is signed diagonal plus the explicit FP defects.
No symmetry or closability of the raw L2 FP operator is assumed. -/
theorem abelianTwoSidedSignedRealization_pairing
    (first second : AbelianTwoSidedGraph period hPeriod metric) :
    globalPairedAbelianOffShellHessian period hPeriod metric
      (abelianTwoSidedSignedRealization period hPeriod metric first)
      (abelianTwoSidedSignedRealization period hPeriod metric second) =
    inner Real (globalPairedAbelianOffShellLorenzProjection period hPeriod metric
      (abelianTwoSidedForget period hPeriod metric first))
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric
        (abelianTwoSidedForget period hPeriod metric second)) -
    inner Real (globalPairedAbelianOffShellBProjection period hPeriod metric
      (abelianTwoSidedForget period hPeriod metric first))
      (globalPairedAbelianOffShellBProjection period hPeriod metric
        (abelianTwoSidedForget period hPeriod metric second)) +
    twoSidedSignedGhostPairing first.val second.val := by
  change globalPairedAbelianOffShellHessian period hPeriod metric
    (abelianLorenzGraphShear period hPeriod metric
      (abelianTwoSidedForget period hPeriod metric
        ((abelianTwoSidedGhostRotation period hPeriod metric).symm first)))
    (abelianLorenzGraphShear period hPeriod metric
      (abelianTwoSidedForget period hPeriod metric
        ((abelianTwoSidedGhostRotation period hPeriod metric).symm second))) = _
  rw [abelianLorenzShear_hessian_pairing, add_assoc]
  exact congrArg (fun ghost =>
    inner Real first.val.fst.fst.snd second.val.fst.fst.snd -
      inner Real first.val.fst.snd.fst second.val.fst.snd.fst + ghost)
    (twoSidedSignedGhostPairing_eq_rotated first.val second.val)

/-- Riesz congruence in the strengthened graph norm, not an L2 spectral identification. -/
def abelianTwoSidedSignedRiesz :
    AbelianTwoSidedGraph period hPeriod metric →L[Real]
      AbelianTwoSidedGraph period hPeriod metric := by
  let adjoint : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      AbelianTwoSidedGraph period hPeriod metric :=
    ContinuousLinearMap.adjoint (𝕜 := Real)
      (E := AbelianTwoSidedGraph period hPeriod metric)
      (F := GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
      (abelianTwoSidedSignedRealization period hPeriod metric)
  exact adjoint.comp
    ((globalPairedAbelianOffShellRieszOperator period hPeriod metric).comp
      (abelianTwoSidedSignedRealization period hPeriod metric))

theorem abelianTwoSidedSignedRiesz_pairing
    (first second : AbelianTwoSidedGraph period hPeriod metric) :
    inner Real (abelianTwoSidedSignedRiesz period hPeriod metric first) second =
      globalPairedAbelianOffShellHessian period hPeriod metric
        (abelianTwoSidedSignedRealization period hPeriod metric first)
        (abelianTwoSidedSignedRealization period hPeriod metric second) := by
  unfold abelianTwoSidedSignedRiesz
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  exact globalPairedAbelianOffShellRieszOperator_pairing period hPeriod metric _ _

theorem abelianTwoSidedSignedRiesz_symmetric
    (first second : AbelianTwoSidedGraph period hPeriod metric) :
    inner Real (abelianTwoSidedSignedRiesz period hPeriod metric first) second =
      inner Real first (abelianTwoSidedSignedRiesz period hPeriod metric second) := by
  calc
    _ = globalPairedAbelianOffShellHessian period hPeriod metric
        (abelianTwoSidedSignedRealization period hPeriod metric first)
        (abelianTwoSidedSignedRealization period hPeriod metric second) :=
      abelianTwoSidedSignedRiesz_pairing period hPeriod metric first second
    _ = globalPairedAbelianOffShellHessian period hPeriod metric
        (abelianTwoSidedSignedRealization period hPeriod metric second)
        (abelianTwoSidedSignedRealization period hPeriod metric first) :=
      globalPairedAbelianOffShellHessian_comm period hPeriod metric _ _
    _ = inner Real (abelianTwoSidedSignedRiesz period hPeriod metric second) first :=
      (abelianTwoSidedSignedRiesz_pairing period hPeriod metric second first).symm
    _ = _ := real_inner_comm _ _

end
end P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D
end JanusFormal
