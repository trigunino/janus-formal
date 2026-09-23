import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BosonBoundedMass4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonReducedCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedPerturbationCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D

/-! The closed actual de Donder cross operator obtained by subtracting the bounded auxiliary mass. -/
namespace JanusFormal.P0EFTJanusProgramPT12BosonDeDonderCore4D
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

open P0EFTJanusProgramPT12BosonBoundedMass4D
open P0EFTJanusProgramPT12HessianBosonReducedCore4D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
open P0EFTJanusProgramPT12BoundedPerturbationCore4D

attribute [local irreducible] hessianBosonReduced bosonBoundedMass

def bosonDeDonderMinimal : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  boundedPerturbation (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (hessianBosonReduced period hPeriod reference metric couplings)
    (-bosonBoundedMass period hPeriod reference metric couplings)

theorem bosonDeDonderMinimal_domain :
    (bosonDeDonderMinimal period hPeriod reference metric couplings).domain =
      (hessianBosonReduced period hPeriod reference metric couplings).domain := rfl

theorem bosonDeDonderMinimal_isClosed :
    (bosonDeDonderMinimal period hPeriod reference metric couplings).IsClosed :=
  boundedPerturbation_isClosed (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ _ (hessianBosonReduced_isClosed period hPeriod reference metric couplings)

theorem bosonDeDonderMinimal_denseDomain : Dense
    ((bosonDeDonderMinimal period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))) :=
  hessianBosonReduced_denseDomain period hPeriod reference metric couplings

theorem bosonDeDonderMinimal_hasCore :
    (bosonDeDonderMinimal period hPeriod reference metric couplings).HasCore
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus)).range :=
  boundedPerturbation_hasCore (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ _
    (hessianBosonReduced_isClosed period hPeriod reference metric couplings).isClosable _
    (hessianBosonReduced_hasCore period hPeriod reference metric couplings)

def bosonDeDonderSmoothOutput (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  hessianBosonReducedSmoothOutput period hPeriod reference metric couplings field -
    bosonBoundedMass period hPeriod reference metric couplings
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field)

theorem bosonDeDonderMinimal_smooth_graph
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field,
     bosonDeDonderSmoothOutput period hPeriod reference metric couplings field) ∈
      (bosonDeDonderMinimal period hPeriod reference metric couplings).graph := by
  rw [bosonDeDonderMinimal, boundedPerturbation_mem_graph_iff]
  simp only [bosonDeDonderSmoothOutput, neg_apply, sub_neg_eq_add, sub_add_cancel]
  exact hessianBosonReduced_smooth_graph period hPeriod reference metric couplings field

theorem bosonDeDonderMinimal_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real)
      (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (bosonDeDonderMinimal period hPeriod reference metric couplings)
      (bosonDeDonderMinimal period hPeriod reference metric couplings) := by
  change ∀ (first second : (hessianBosonReduced period hPeriod reference metric couplings).domain),
    inner Real
    (-bosonBoundedMass period hPeriod reference metric couplings first.val +
      hessianBosonReduced period hPeriod reference metric couplings first) second.val =
    inner Real first.val
      (-bosonBoundedMass period hPeriod reference metric couplings second.val +
        hessianBosonReduced period hPeriod reference metric couplings second)
  intro first second
  rw [inner_add_left (𝕜 := Real) (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)), inner_add_right (𝕜 := Real) (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)), inner_neg_left (𝕜 := Real) (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)), inner_neg_right (𝕜 := Real) (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)),
    bosonBoundedMass_symmetric, hessianBosonReduced_isFormalAdjoint]

theorem bosonDeDonderMinimal_restore :
    boundedPerturbation (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (bosonDeDonderMinimal period hPeriod reference metric couplings)
      (bosonBoundedMass period hPeriod reference metric couplings) =
    hessianBosonReduced period hPeriod reference metric couplings := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [boundedPerturbation_mem_graph_iff, bosonDeDonderMinimal, boundedPerturbation_mem_graph_iff]
  simp only [neg_apply, sub_neg_eq_add, sub_add_cancel]

end
end JanusFormal.P0EFTJanusProgramPT12BosonDeDonderCore4D