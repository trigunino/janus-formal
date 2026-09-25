import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Native weighted diagonal BRST Hessian on physical L² with a shared triplet. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongSmooth4D
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
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "Plus" => FrameFreeDiffeomorphismFullL2 period hPeriod (metric Sector.plus)
local notation "Minus" => FrameFreeDiffeomorphismFullL2 period hPeriod (metric Sector.minus)
local instance plusGroup : NormedAddCommGroup Plus := inferInstance
local instance : SeminormedAddCommGroup Plus := (plusGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Plus := inferInstance
local instance : InnerProductSpace Real Plus := inferInstance
local instance minusGroup : NormedAddCommGroup Minus := inferInstance
local instance : SeminormedAddCommGroup Minus := (minusGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Minus := inferInstance
local instance : InnerProductSpace Real Minus := inferInstance
local notation "Pair" => WithLp 2 (Plus × Minus)
local instance pairGroup : NormedAddCommGroup Pair := inferInstance
local instance : SeminormedAddCommGroup Pair := (pairGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Pair := inferInstance
local instance : InnerProductSpace Real Pair := inferInstance
local instance : ContinuousConstSMul Real Pair where
  continuous_const_smul scalar := (lipschitzWith_smul (β := Pair) scalar).continuous
local instance : CompleteSpace Pair := inferInstance
local notation "sector" => globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod

open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
local notation "Core" => FrameFreeDiagonalDiffeomorphismL2 period hPeriod metric
local instance coreGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (coreGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local notation "plus" => frameFreeDiagonalDiffeomorphismPlus period hPeriod metric
local notation "minus" => frameFreeDiagonalDiffeomorphismMinus period hPeriod metric
local notation "inc" => frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric
variable (couplings : GlobalCandidateAActionCouplings)

/-- Adjoint pullbacks sum the two native sector columns into the single shared triplet. -/
def frameFreeDiagonalDiffeomorphismStrongSmooth : State →ₗ[Real] Core :=
  weightedSum (candidateAPlusEinsteinKineticWeight couplings) (candidateAMinusEinsteinKineticWeight couplings)
    ((plus).adjoint.toLinearMap.comp
      ((frameFreeDiffeomorphismStrongSmooth period hPeriod (metric .plus)).comp (sector .plus)))
    ((minus).adjoint.toLinearMap.comp
      ((frameFreeDiffeomorphismStrongSmooth period hPeriod (metric .minus)).comp (sector .minus)))

theorem frameFreeDiagonalDiffeomorphismStrongSmooth_pairing (first second : State) :
    inner Real (frameFreeDiagonalDiffeomorphismStrongSmooth period hPeriod metric couplings first) (inc second) =
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric first)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric second) := by
  simp only [frameFreeDiagonalDiffeomorphismStrongSmooth, weightedSum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, frameFreeDiagonalDiffeomorphismPlus_smooth,
    frameFreeDiagonalDiffeomorphismMinus_smooth, frameFreeDiffeomorphismStrongSmooth_pairing,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_apply,
    globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]

theorem frameFreeDiagonalDiffeomorphismStrongSmooth_symmetric (first second : State) :
    inner Real (frameFreeDiagonalDiffeomorphismStrongSmooth period hPeriod metric couplings first) (inc second) =
    inner Real (inc first) (frameFreeDiagonalDiffeomorphismStrongSmooth period hPeriod metric couplings second) :=
  (frameFreeDiagonalDiffeomorphismStrongSmooth_pairing period hPeriod metric couplings first second).trans
    ((globalCandidateADiagonalDiffeomorphismOffShellHessian_comm period hPeriod couplings metric _ _).trans
      ((frameFreeDiagonalDiffeomorphismStrongSmooth_pairing period hPeriod metric couplings second first).symm.trans
        (real_inner_comm _ _)))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongSmooth4D
