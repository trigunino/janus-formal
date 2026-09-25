import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Native physical sector readouts from the established H11 source L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismH11Readouts4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Ghost" => CInfinityDiffeomorphismGhost period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Ambient" => GlobalDiffeomorphismVectorL2 period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusH1GraphTrace4D
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
local notation "h" => generalMetricFrameCoefficient period hPeriod frame
local notation "bracket" => finiteFrameStructureCoefficient period hPeriod frame metric
local notation "deriv" => canonicalFrameDerivativeSmooth period hPeriod frame
local notation "mul" => canonicalScalarMul period hPeriod

open P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
open P0EFTJanusProgramPT12FrameFreeCartanScalar4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
local notation "Core" => FrameFreeGhostL2 period hPeriod metric
local instance ghostGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (ghostGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local notation "q" => frameFreeGhostCoordinate period hPeriod metric
local notation "inc" => frameFreeGhostL2Smooth period hPeriod metric
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod

open P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusFiniteFrameMetricContraction4D
local notation "g" => finiteFrameInverseMetricCoefficient period hPeriod frame metric metric
local notation "Γ" => finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric
local notation "derivAdj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame
local notation "cartanAdj" => frameFreeCartanAdjointColumn period hPeriod metric metric.tensor

open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local instance ambientGroup : NormedAddCommGroup Ambient := inferInstance
local instance : SeminormedAddCommGroup Ambient := (ambientGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Ambient := inferInstance
local instance : InnerProductSpace Real Ambient := inferInstance
local notation "action" => frameFreeDiffeomorphismFPSmoothL2 period hPeriod metric
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPSmoothAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D
local notation "TensorL2" => FrameTensorL2Completion period hPeriod frame
local instance tensorGroup : NormedAddCommGroup TensorL2 := inferInstance
local instance : SeminormedAddCommGroup TensorL2 := (tensorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real TensorL2 := inferInstance
local instance : InnerProductSpace Real TensorL2 := Submodule.innerProductSpace (𝕜 := Real) _
local notation "minimal" => frameFreeDeDonderMinimal period hPeriod metric

open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "tensorInc" => frameTensorL2Smooth period hPeriod frame

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
local notation "Source" => DiffeomorphismL2 period hPeriod metric
local notation "Full" => FrameFreeDiffeomorphismFullL2 period hPeriod metric
local instance sourceGroup : NormedAddCommGroup Source := inferInstance
local instance : SeminormedAddCommGroup Source := (sourceGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Source := inferInstance
local instance : InnerProductSpace Real Source := Submodule.innerProductSpace (𝕜 := Real) _
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
local notation "smooth" => diffeomorphismL2Smooth period hPeriod metric

/-- The metric readout lands in the actual tensor completion, not its redundant ambient. -/
def frameFreeH11TensorReadout (selected : Sector) : Source →L[Real] TensorL2 :=
  (diffeomorphismTensorReadout period hPeriod metric selected).codRestrict
    (frameTensorL2Space period hPeriod frame) (diffeomorphismTensorReadout_mem period hPeriod metric selected)

private theorem triplet_mem (index : Fin 3) (point : Source) :
    diffeomorphismTripletReadout period hPeriod metric index point ∈ frameFreeGhostL2Space period hPeriod metric := by
  have hClosed : IsClosed {value : Source | diffeomorphismTripletReadout period hPeriod metric index value ∈
      frameFreeGhostL2Space period hPeriod metric} :=
    (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.isClosed_topologicalClosure.preimage
      (diffeomorphismTripletReadout period hPeriod metric index).continuous
  apply closure_minimal (s := Set.range smooth) ?_ hClosed
    (by rw [(diffeomorphismL2Smooth_denseRange period hPeriod metric).closure_range]; trivial)
  rintro _ ⟨state, rfl⟩
  change diffeomorphismTripletReadout period hPeriod metric index (smooth state) ∈
    frameFreeGhostL2Space period hPeriod metric
  rw [diffeomorphismTripletReadout_smooth]
  exact (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.le_topologicalClosure ⟨_, rfl⟩

def frameFreeH11TripletReadout (index : Fin 3) : Source →L[Real] Core :=
  (diffeomorphismTripletReadout period hPeriod metric index).codRestrict
    (frameFreeGhostL2Space period hPeriod metric) (triplet_mem period hPeriod metric index)

theorem frameFreeH11TensorReadout_smooth (selected : Sector) (state : State) :
    frameFreeH11TensorReadout period hPeriod metric selected (smooth state) =
      tensorInc (state.metricPerturbation selected) := rfl

theorem frameFreeH11TripletReadout_smooth (index : Fin 3) (state : State) :
    frameFreeH11TripletReadout period hPeriod metric index (smooth state) =
      inc (![state.nonminimal.ghost.field, state.nonminimal.antighost.field,
        state.nonminimal.nakanishiLautrup.field] index) := by
  apply Subtype.ext
  exact diffeomorphismTripletReadout_smooth period hPeriod metric index state

private def pairCLM {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D] [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (first : D →L[Real] E) (second : D →L[Real] F) : D →L[Real] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toContinuousLinearMap.comp (first.prod second)

/-- Both sector readouts use the original single H11 triplet. -/
def frameFreeH11SectorReadout (selected : Sector) : Source →L[Real] Full :=
  pairCLM
    (pairCLM (frameFreeH11TensorReadout period hPeriod metric selected) (frameFreeH11TripletReadout period hPeriod metric 2))
    (pairCLM (frameFreeH11TripletReadout period hPeriod metric 1) (frameFreeH11TripletReadout period hPeriod metric 0))

theorem frameFreeH11SectorReadout_smooth (selected : Sector) (state : State) :
    frameFreeH11SectorReadout period hPeriod metric selected (smooth state) =
      frameFreeDiffeomorphismFullL2Smooth period hPeriod metric
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod selected state) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    exact Prod.ext (frameFreeH11TensorReadout_smooth period hPeriod metric selected state)
      (frameFreeH11TripletReadout_smooth period hPeriod metric 2 state)
  · apply WithLp.ofLp_injective 2
    exact Prod.ext (frameFreeH11TripletReadout_smooth period hPeriod metric 1 state)
      (frameFreeH11TripletReadout_smooth period hPeriod metric 0 state)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismH11Readouts4D
