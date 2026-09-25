import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismH11Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Native diagonal BRST columns on the established H11 source L², at a common background. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeH11BRSTStrongSmooth4D
set_option autoImplicit false
noncomputable section
private def weightedSum {D E : Type*} [AddCommGroup D] [Module Real D]
    [AddCommGroup E] [Module Real E] (firstWeight secondWeight : Real)
    (first second : D →ₗ[Real] E) : D →ₗ[Real] E := firstWeight • first + secondWeight • second
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

open P0EFTJanusProgramPT12FrameFreeDiffeomorphismH11Readouts4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
local notation "sector" => globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod
local notation "readout" => frameFreeH11SectorReadout period hPeriod metric
variable (couplings : GlobalCandidateAActionCouplings)

/-- Adjoint sector readouts preserve the existing H11 norm and the single triplet. -/
def frameFreeH11BRSTStrongSmooth : State →ₗ[Real] Source :=
  weightedSum (candidateAPlusEinsteinKineticWeight couplings) (candidateAMinusEinsteinKineticWeight couplings)
    ((readout Sector.plus).adjoint.toLinearMap.comp
      ((frameFreeDiffeomorphismStrongSmooth period hPeriod metric).comp (sector .plus)))
    ((readout Sector.minus).adjoint.toLinearMap.comp
      ((frameFreeDiffeomorphismStrongSmooth period hPeriod metric).comp (sector .minus)))

theorem frameFreeH11BRSTStrongSmooth_pairing (first second : State) :
    inner Real (frameFreeH11BRSTStrongSmooth period hPeriod metric couplings first) (smooth second) =
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings (fun _ => metric)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) second) := by
  simp only [frameFreeH11BRSTStrongSmooth, weightedSum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, frameFreeH11SectorReadout_smooth,
    frameFreeDiffeomorphismStrongSmooth_pairing, globalCandidateADiagonalDiffeomorphismOffShellHessian_apply,
    globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]

theorem frameFreeH11BRSTStrongSmooth_symmetric (first second : State) :
    inner Real (frameFreeH11BRSTStrongSmooth period hPeriod metric couplings first) (smooth second) =
    inner Real (smooth first) (frameFreeH11BRSTStrongSmooth period hPeriod metric couplings second) :=
  (frameFreeH11BRSTStrongSmooth_pairing period hPeriod metric couplings first second).trans
    ((globalCandidateADiagonalDiffeomorphismOffShellHessian_comm period hPeriod couplings (fun _ => metric) _ _).trans
      ((frameFreeH11BRSTStrongSmooth_pairing period hPeriod metric couplings second first).symm.trans (real_inner_comm _ _)))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeH11BRSTStrongSmooth4D
