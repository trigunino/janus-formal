import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL24D

/-! Smooth weighted curvature columns and their concrete transposes. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
open P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
open P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "Potential" => IntrinsicAbelianPotentialL2Core period hPeriod
local notation "Curvature" => IntrinsicAbelianCurvatureL2 period hPeriod
local instance potentialGroup : NormedAddCommGroup Potential := inferInstance
local instance : SeminormedAddCommGroup Potential := (potentialGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Potential := inferInstance
local instance curvatureGroup : NormedAddCommGroup Curvature := inferInstance
local instance : SeminormedAddCommGroup Curvature := (curvatureGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Index" => IntrinsicAbelianCurvatureIndex period hPeriod
local instance : InnerProductSpace Real Potential :=
  Submodule.innerProductSpace (𝕜 := Real) (intrinsicAbelianPotentialL2Submodule period hPeriod)
local instance : InnerProductSpace Real Curvature := inferInstance
local instance : CompleteSpace Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D

def intrinsicAbelianCurvatureWeightColumn (row column : Index) (weight : Scalar) : Curvature →L[Real] Curvature :=
  (intrinsicAbelianCurvatureCoordinate period hPeriod row).adjoint.comp
    ((canonicalSmoothMultiplier period hPeriod weight).comp
      (intrinsicAbelianCurvatureCoordinate period hPeriod column))

theorem intrinsicAbelianCurvatureWeightColumn_smooth (row column : Index) (weight : Scalar) (tests : Index → Scalar) :
    intrinsicAbelianCurvatureWeightColumn period hPeriod row column weight
      (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) =
    intrinsicAbelianCurvatureTest period hPeriod row (canonicalScalarMul period hPeriod weight (tests column)) := by
  change (intrinsicAbelianCurvatureCoordinate period hPeriod row).adjoint
    (canonicalSmoothMultiplier period hPeriod weight (smoothToCanonicalPhysicalBulkL2 period hPeriod (tests column))) = _
  rw [canonicalSmoothMultiplier_smooth]
  rfl

theorem intrinsicAbelianCurvatureWeightColumn_mem_adjoint
    (row column : Index) (weight : Scalar) (tests : Index → Scalar) :
    intrinsicAbelianCurvatureWeightColumn period hPeriod row column weight
      (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain := by
  rw [intrinsicAbelianCurvatureWeightColumn_smooth]
  exact intrinsicAbelianCurvatureTest_mem_adjoint period hPeriod row _

theorem intrinsicAbelianCurvatureWeightColumn_pairing
    (row column : Index) (weight : Scalar) (first second : Curvature) :
    inner Real (intrinsicAbelianCurvatureWeightColumn period hPeriod row column weight first) second =
      inner Real (canonicalSmoothMultiplier period hPeriod weight (first column)) (second row) := by
  simp only [intrinsicAbelianCurvatureWeightColumn, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem intrinsicAbelianCurvatureWeightColumn_transpose
    (row column : Index) (weight : Scalar) (first second : Curvature) :
    inner Real (intrinsicAbelianCurvatureWeightColumn period hPeriod row column weight first) second =
      inner Real first (intrinsicAbelianCurvatureWeightColumn period hPeriod column row weight second) := by
  simp only [intrinsicAbelianCurvatureWeightColumn, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact l2VolumeMultiplier_symmetric _ _ _ _

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
