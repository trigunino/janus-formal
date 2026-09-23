import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D

/-! The exact bounded self-adjoint auxiliary mass on the actual metric–B Hilbert space. -/
namespace JanusFormal.P0EFTJanusProgramPT12BosonBoundedMass4D
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

open P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
open P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

open P0EFTJanusProgramPT12HessianGhostSmooth4D
open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12HessianGhostCommutation4D
open P0EFTJanusProgramPT12HessianL2OperatorCore4D
open P0EFTJanusProgramPT12HessianL2OperatorClosed4D

open P0EFTJanusProgramPT12HessianGhostMinimal4D
open P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D

open P0EFTJanusProgramPT12HessianBosonReduced4D
open P0EFTJanusProgramPT12HessianBosonForm4D

local instance bosonInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range

local instance bosonContinuousStar :
    Star (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →L[Real]
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  ⟨ContinuousLinearMap.adjoint (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))⟩

theorem auxiliarySectorL2Riesz_symmetric (sector : Sector)
    (first second : DiffeomorphismL2 period hPeriod (metric .plus)) :
    inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector first) second =
      inner Real first (auxiliarySectorL2Riesz period hPeriod reference metric sector second) := by
  calc
    _ = inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector second) first := by
      rw [auxiliarySectorL2Riesz_pairing, auxiliarySectorL2Riesz_pairing]
      let b := sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      let f := sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      change -(1 / 2 : Real) * (inner Real (f first) (b second) + inner Real (b first) (f second)) =
        -(1 / 2 : Real) * (inner Real (f second) (b first) + inner Real (b second) (f first))
      rw [real_inner_comm (f first) (b second), real_inner_comm (b first) (f second), add_comm]
    _ = _ := real_inner_comm _ _

def bosonFullMass : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  candidateAPlusEinsteinKineticWeight couplings • auxiliarySectorL2Riesz period hPeriod reference metric .plus +
    candidateAMinusEinsteinKineticWeight couplings • auxiliarySectorL2Riesz period hPeriod reference metric .minus

theorem bosonFullMass_pairing (first second : DiffeomorphismL2 period hPeriod (metric .plus)) :
    inner Real (bosonFullMass period hPeriod reference metric couplings first) second =
    candidateAPlusEinsteinKineticWeight couplings *
      inner Real (auxiliarySectorL2Riesz period hPeriod reference metric .plus first) second +
    candidateAMinusEinsteinKineticWeight couplings *
      inner Real (auxiliarySectorL2Riesz period hPeriod reference metric .minus first) second := by
  change inner Real
    (candidateAPlusEinsteinKineticWeight couplings • auxiliarySectorL2Riesz period hPeriod reference metric .plus first +
     candidateAMinusEinsteinKineticWeight couplings • auxiliarySectorL2Riesz period hPeriod reference metric .minus first) second = _
  rw [inner_add_left]
  exact congrArg₂ (fun x y : Real => x + y)
    (real_inner_smul_left (auxiliarySectorL2Riesz period hPeriod reference metric .plus first) second
      (candidateAPlusEinsteinKineticWeight couplings))
    (real_inner_smul_left (auxiliarySectorL2Riesz period hPeriod reference metric .minus first) second
      (candidateAMinusEinsteinKineticWeight couplings))
theorem bosonFullMass_symmetric (first second : DiffeomorphismL2 period hPeriod (metric .plus)) :
    inner Real (bosonFullMass period hPeriod reference metric couplings first) second =
      inner Real first (bosonFullMass period hPeriod reference metric couplings second) := by
  have h (sector : Sector) :
      inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector first) second =
        inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector second) first :=
    (auxiliarySectorL2Riesz_symmetric period hPeriod reference metric sector first second).trans
      (real_inner_comm _ _)
  calc
    _ = inner Real (bosonFullMass period hPeriod reference metric couplings second) first := by
      rw [bosonFullMass_pairing, bosonFullMass_pairing, h .plus, h .minus]
    _ = _ := real_inner_comm _ _

attribute [local irreducible] bosonFullMass diffeomorphismBosonProjection
def bosonBoundedMass : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →L[Real]
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  (ContinuousLinearMap.adjoint (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (F := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range.subtypeL).comp
    ((bosonFullMass period hPeriod reference metric couplings).comp
      (diffeomorphismBosonProjection period hPeriod (metric .plus)).range.subtypeL)
theorem bosonBoundedMass_pairing
    (first second : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    inner Real (bosonBoundedMass period hPeriod reference metric couplings first) second =
      inner Real (bosonFullMass period hPeriod reference metric couplings first.val) second.val := by
  unfold bosonBoundedMass
  change inner Real
    ((ContinuousLinearMap.adjoint (𝕜 := Real)
      (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus))
      (diffeomorphismBosonProjection period hPeriod (metric .plus)).range.subtypeL)
      (bosonFullMass period hPeriod reference metric couplings first.val)) second = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem bosonBoundedMass_symmetric
    (first second : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    inner Real (bosonBoundedMass period hPeriod reference metric couplings first) second =
      inner Real first (bosonBoundedMass period hPeriod reference metric couplings second) := by
  calc
    _ = inner Real (bosonFullMass period hPeriod reference metric couplings first.val) second.val :=
      bosonBoundedMass_pairing period hPeriod reference metric couplings first second
    _ = inner Real first.val (bosonFullMass period hPeriod reference metric couplings second.val) :=
      bosonFullMass_symmetric period hPeriod reference metric couplings first.val second.val
    _ = inner Real (bosonFullMass period hPeriod reference metric couplings second.val) first.val := real_inner_comm _ _
    _ = inner Real (bosonBoundedMass period hPeriod reference metric couplings second) first :=
      (bosonBoundedMass_pairing period hPeriod reference metric couplings second first).symm
    _ = _ := real_inner_comm _ _

theorem bosonBoundedMass_selfAdjoint :
    IsSelfAdjoint (bosonBoundedMass period hPeriod reference metric couplings) :=
  (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric Real
    (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    _ _ (bosonInnerProductSpace period hPeriod metric) _
    (bosonBoundedMass period hPeriod reference metric couplings)).mpr
    (bosonBoundedMass_symmetric period hPeriod reference metric couplings)

theorem bosonBoundedMass_smooth_pairing
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (bosonBoundedMass period hPeriod reference metric couplings
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) first))
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) second) =
    inner Real (bosonFullMass period hPeriod reference metric couplings
      (diffeomorphismL2Smooth period hPeriod (metric .plus) first))
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) := by
  rw [bosonBoundedMass_pairing]
  change inner Real (bosonFullMass period hPeriod reference metric couplings
    (diffeomorphismBosonProjection period hPeriod (metric .plus)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) first)))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) = _
  rw [hessianBosonSmooth_L2, hessianBosonSmooth_L2]
  simp only [bosonFullMass_pairing, auxiliarySectorL2Riesz_pairing,
    hessianBosonSmooth_B, hessianBosonSmooth_BFlat]

end
end JanusFormal.P0EFTJanusProgramPT12BosonBoundedMass4D