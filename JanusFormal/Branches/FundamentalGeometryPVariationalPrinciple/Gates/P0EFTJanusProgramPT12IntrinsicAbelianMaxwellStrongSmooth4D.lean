import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D

/-! Native Maxwell Jacobi represented in physical potential L² on smooth fields. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
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
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D

/-- Native smooth curvature has smooth scalar coefficients in every coordinate. -/
theorem intrinsicAbelianCurvatureL2_eq_smooth (potential : Smooth) :
    intrinsicAbelianCurvatureL2 period hPeriod potential =
      intrinsicAbelianSmoothCurvatureL2 period hPeriod (fun index =>
        finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame (potential index.1)
          index.2.1 index.2.2.1 index.2.2.2) := by
  apply PiLp.ext
  intro index
  exact intrinsicAbelianCurvatureL2_native period hPeriod potential index

theorem intrinsicAbelianMaxwellWeightedCurvature_mem_adjoint
    (couplings : GlobalCandidateAActionCouplings) (potential : Smooth) :
    intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings
      (intrinsicAbelianCurvatureL2 period hPeriod potential) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain := by
  rw [intrinsicAbelianCurvatureL2_eq_smooth]
  exact intrinsicAbelianMaxwellCurvatureWeight_mem_adjoint period hPeriod couplings _

/-- The native strong Maxwell action is D* W D on smooth potentials, in physical L². -/
def intrinsicAbelianMaxwellStrongSmooth (couplings : GlobalCandidateAActionCouplings) :
    Smooth →ₗ[Real] Potential :=
  (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.toFun.comp
    (LinearMap.codRestrict (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain
      ((intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings).toLinearMap.comp
        (intrinsicAbelianCurvatureL2 period hPeriod))
      (intrinsicAbelianMaxwellWeightedCurvature_mem_adjoint period hPeriod couplings))

/-- Green identity against the full closed curvature domain. -/
theorem intrinsicAbelianMaxwellStrongSmooth_pairing
    (couplings : GlobalCandidateAActionCouplings) (potential : Smooth)
    (test : (intrinsicAbelianCurvatureMinimal period hPeriod).domain) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings potential) test.val =
      inner Real (intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings
        (intrinsicAbelianCurvatureL2 period hPeriod potential))
        (intrinsicAbelianCurvatureMinimal period hPeriod test) :=
  LinearPMap.adjoint_isFormalAdjoint (intrinsicAbelianCurvatureMinimal_dense_domain period hPeriod)
    ⟨_, intrinsicAbelianMaxwellWeightedCurvature_mem_adjoint period hPeriod couplings potential⟩ test

theorem intrinsicAbelianMaxwellStrongSmooth_smooth_pairing
    (couplings : GlobalCandidateAActionCouplings) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
      inner Real (intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings
        (intrinsicAbelianCurvatureL2 period hPeriod first))
        (intrinsicAbelianCurvatureL2 period hPeriod second) := by
  exact (intrinsicAbelianMaxwellStrongSmooth_pairing period hPeriod couplings first
    ⟨_, intrinsicAbelianCurvatureMinimal_smooth_mem period hPeriod second⟩).trans
      (congrArg (inner Real _) (intrinsicAbelianCurvatureMinimal_smooth_apply period hPeriod second))

/-- Exact equality with the already constructed native graph Hessian. -/
theorem intrinsicAbelianMaxwellStrongSmooth_eq_graphHessian
    (couplings : GlobalCandidateAActionCouplings) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
      intrinsicAbelianMaxwellGraphHessian period hPeriod couplings
        (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
        (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) := by
  rw [intrinsicAbelianMaxwellStrongSmooth_smooth_pairing]
  simpa only [intrinsicAbelianMaxwellLorenzCurvature_smooth] using
    intrinsicAbelianMaxwellCurvatureWeight_graph_pairing period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second)

theorem intrinsicAbelianMaxwellStrongSmooth_symmetric
    (couplings : GlobalCandidateAActionCouplings) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
      inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod first)
        (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings second) := by
  rw [intrinsicAbelianMaxwellStrongSmooth_smooth_pairing,
    intrinsicAbelianMaxwellCurvatureWeight_symmetric]
  exact (real_inner_comm _ _).trans
    ((intrinsicAbelianMaxwellStrongSmooth_smooth_pairing period hPeriod couplings second first).symm.trans
      (real_inner_comm _ _))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
