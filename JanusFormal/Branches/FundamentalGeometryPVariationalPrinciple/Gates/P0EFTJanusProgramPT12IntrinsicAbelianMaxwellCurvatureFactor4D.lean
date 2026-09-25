import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D

/-! Exact curvature factorization of the native Maxwell Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D
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

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance : NormedAddCommGroup Graph := inferInstance
local instance : NormedSpace Real Graph := inferInstance
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod

private theorem bounded_weight (i j k l : N) :
    boundedSmoothScalar period hPeriod (intrinsicAbelianMaxwellWeight period hPeriod i j k l) =
    ContinuousMap.linearIsometryBoundedOfCompact (Q period hPeriod) Real Real
      (finiteFrameCanonicalVolumeC0 period hPeriod frame base 0 *
        ((-(1 / 4 : Real)) •
          (finiteFrameInverseMetricC0Coefficient period hPeriod frame base i k 0 *
            finiteFrameInverseMetricC0Coefficient period hPeriod frame base j l 0))) := by
  change ContinuousMap.linearIsometryBoundedOfCompact (Q period hPeriod) Real Real
    (smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (intrinsicAbelianMaxwellWeight period hPeriod i j k l)) = _
  exact congrArg (ContinuousMap.linearIsometryBoundedOfCompact (Q period hPeriod) Real Real)
    (intrinsicAbelianMaxwellWeight_continuous period hPeriod i j k l)

/-- Exact factorization of the existing native Maxwell sector form through curvature L². -/
theorem intrinsicAbelianMaxwellCurvatureSectorWeight_graph_pairing
    (sector : Sector) (first second : Graph) :
    inner Real (intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod false sector
      (intrinsicAbelianMaxwellLorenzCurvature period hPeriod first))
      (intrinsicAbelianMaxwellLorenzCurvature period hPeriod second) =
    intrinsicAbelianMaxwellGraphSectorPairing period hPeriod sector first second := by
  simp only [intrinsicAbelianMaxwellCurvatureSectorWeight, Bool.false_eq_true, ↓reduceIte,
    intrinsicAbelianMaxwellGraphSectorPairing, sum_apply, sum_inner, ContinuousLinearMap.bilinearComp_apply]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [intrinsicAbelianCurvatureWeightColumn_pairing]
  exact congrArg (fun weight => inner Real
    (l2VolumeMultiplier μ weight (intrinsicAbelianMaxwellLorenzCurvature period hPeriod first (sector, component, i, j)))
    (intrinsicAbelianMaxwellLorenzCurvature period hPeriod second (sector, component, k, l)))
    (bounded_weight period hPeriod i j k l)

/-- The symmetric curvature weight gives precisely the unchanged native Maxwell Hessian. -/
theorem intrinsicAbelianMaxwellCurvatureWeight_graph_pairing
    (couplings : GlobalCandidateAActionCouplings) (first second : Graph) :
    inner Real (intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzCurvature period hPeriod first))
      (intrinsicAbelianMaxwellLorenzCurvature period hPeriod second) =
      intrinsicAbelianMaxwellGraphHessian period hPeriod couplings first second := by
  let a := intrinsicAbelianMaxwellLorenzCurvature period hPeriod first
  let b := intrinsicAbelianMaxwellLorenzCurvature period hPeriod second
  have hReverse : inner Real (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings true a) b =
      inner Real (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings false b) a :=
    (real_inner_comm _ _).trans
      (intrinsicAbelianMaxwellCurvaturePairedWeight_transpose period hPeriod couplings b a).symm
  change inner Real
    (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings false a +
      intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings true a) b = _
  rw [inner_add_left, hReverse]
  change _ =
    (couplings.plusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .plus first second +
      couplings.minusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .minus first second) +
    (couplings.plusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .plus second first +
      couplings.minusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .minus second first)
  simp only [intrinsicAbelianMaxwellCurvaturePairedWeight, add_apply,
    smul_apply, inner_add_left, real_inner_smul_left, a, b,
    intrinsicAbelianMaxwellCurvatureSectorWeight_graph_pairing]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D
