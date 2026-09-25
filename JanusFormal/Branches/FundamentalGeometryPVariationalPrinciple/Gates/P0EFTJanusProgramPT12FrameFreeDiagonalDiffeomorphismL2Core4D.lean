import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Physical diagonal BRST completion with two tensor sectors and one shared triplet. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
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

private def rawSmooth : State →ₗ[Real] Pair :=
  (WithLp.prodContinuousLinearEquiv 2 Real Plus Minus).symm.toLinearMap.comp
    (((frameFreeDiffeomorphismFullL2Smooth period hPeriod (metric Sector.plus)).comp (sector .plus)).prod
      ((frameFreeDiffeomorphismFullL2Smooth period hPeriod (metric Sector.minus)).comp (sector .minus)))

/-- Closure preserves the shared triplet constraint; no independent ghost copies are added. -/
def frameFreeDiagonalDiffeomorphismL2Space : Submodule Real Pair :=
  (rawSmooth period hPeriod metric).range.topologicalClosure
abbrev FrameFreeDiagonalDiffeomorphismL2 := frameFreeDiagonalDiffeomorphismL2Space period hPeriod metric
local notation "Core" => FrameFreeDiagonalDiffeomorphismL2 period hPeriod metric
local instance coreGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (coreGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
instance frameFreeDiagonalDiffeomorphismL2_complete : CompleteSpace Core :=
  (rawSmooth period hPeriod metric).range.isClosed_topologicalClosure.completeSpace_coe

def frameFreeDiagonalDiffeomorphismL2Smooth : State →ₗ[Real] Core :=
  (rawSmooth period hPeriod metric).codRestrict (frameFreeDiagonalDiffeomorphismL2Space period hPeriod metric)
    (fun state => (rawSmooth period hPeriod metric).range.le_topologicalClosure ⟨state, rfl⟩)

def frameFreeDiagonalDiffeomorphismPlus : Core →L[Real] Plus :=
  ((ContinuousLinearMap.fst Real Plus Minus).comp
    (WithLp.prodContinuousLinearEquiv 2 Real Plus Minus).toContinuousLinearMap).comp
      (frameFreeDiagonalDiffeomorphismL2Space period hPeriod metric).subtypeL

def frameFreeDiagonalDiffeomorphismMinus : Core →L[Real] Minus :=
  ((ContinuousLinearMap.snd Real Plus Minus).comp
    (WithLp.prodContinuousLinearEquiv 2 Real Plus Minus).toContinuousLinearMap).comp
      (frameFreeDiagonalDiffeomorphismL2Space period hPeriod metric).subtypeL

theorem frameFreeDiagonalDiffeomorphismPlus_smooth (state : State) :
    frameFreeDiagonalDiffeomorphismPlus period hPeriod metric
      (frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric state) =
    frameFreeDiffeomorphismFullL2Smooth period hPeriod (metric Sector.plus) (sector .plus state) := rfl

theorem frameFreeDiagonalDiffeomorphismMinus_smooth (state : State) :
    frameFreeDiagonalDiffeomorphismMinus period hPeriod metric
      (frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric state) =
    frameFreeDiffeomorphismFullL2Smooth period hPeriod (metric Sector.minus) (sector .minus state) := rfl

theorem frameFreeDiagonalDiffeomorphismL2Smooth_injective :
    Function.Injective (frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric) := by
  intro first second hEqual
  have hPlus := frameFreeDiffeomorphismFullL2Smooth_injective period hPeriod (metric Sector.plus)
    (congrArg (frameFreeDiagonalDiffeomorphismPlus period hPeriod metric) hEqual)
  have hMinus := frameFreeDiffeomorphismFullL2Smooth_injective period hPeriod (metric Sector.minus)
    (congrArg (frameFreeDiagonalDiffeomorphismMinus period hPeriod metric) hEqual)
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · funext selected
    cases selected
    · exact congrArg (fun state => state.metricPerturbation) hPlus
    · exact congrArg (fun state => state.metricPerturbation) hMinus
  · exact congrArg (fun state => state.nonminimal) hPlus

theorem frameFreeDiagonalDiffeomorphismL2Smooth_denseRange :
    DenseRange (frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric) := by
  rw [DenseRange, Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric) =
      ((rawSmooth period hPeriod metric).range : Set Pair) := by
    ext value
    constructor
    · rintro ⟨_, ⟨state, rfl⟩, rfl⟩; exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact ⟨frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric state, ⟨state, rfl⟩, rfl⟩
  exact (congrArg closure hRange).symm.subset

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
