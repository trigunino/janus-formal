import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Bounded native metric-flat readout on physical vector L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMetricFlat4D
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
/-- Lowering a physical vector index is a bounded operation in the actual finite frame. -/
def frameFreeMetricFlatL2 : Core →L[Real] Ambient :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : N => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun row => ∑ column,
      (canonicalSmoothMultiplier period hPeriod (h metric.tensor column row)).comp (q column))

theorem frameFreeMetricFlatL2_smooth (vector : Ghost) :
    frameFreeMetricFlatL2 period hPeriod metric (inc vector) =
      globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric vector := by
  apply PiLp.ext
  intro row
  change (∑ column, (canonicalSmoothMultiplier period hPeriod (h metric.tensor column row)).comp (q column))
      (inc vector) = incl (globalSmoothCovectorFrameCoefficient period hPeriod
        (globalSmoothMetricFlat period hPeriod metric vector) row)
  simp only [sum_apply, ContinuousLinearMap.comp_apply, frameFreeGhostCoordinate_smooth,
    canonicalSmoothMultiplier_smooth, ← map_sum]
  congr 1
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  change (∑ column, h metric.tensor column row point *
    generalMetricFiniteFrameCoefficient period hPeriod frame metric vector column point) =
    metric.tensor.tensor point (vector point) ((frame).vectorAt point row)
  conv_rhs => rw [generalMetricFiniteFrame_reconstructs period hPeriod frame metric vector point]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro column _
  exact mul_comm _ _

/-- Physical Riesz representative of the native metric-flat pairing. -/
def frameFreeMetricFlatPhysical : Core →L[Real] Core :=
  (frameFreeGhostL2Space period hPeriod metric).subtypeL.adjoint.comp (frameFreeMetricFlatL2 period hPeriod metric)

theorem frameFreeMetricFlatPhysical_pairing (first second : Core) :
    inner Real (frameFreeMetricFlatPhysical period hPeriod metric first) second =
      inner Real (frameFreeMetricFlatL2 period hPeriod metric first) second.val :=
  ContinuousLinearMap.adjoint_inner_left
    (frameFreeGhostL2Space period hPeriod metric).subtypeL second
    (frameFreeMetricFlatL2 period hPeriod metric first)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMetricFlat4D
