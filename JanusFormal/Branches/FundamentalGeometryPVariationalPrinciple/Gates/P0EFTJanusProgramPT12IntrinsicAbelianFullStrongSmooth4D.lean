import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D

/-! Native Maxwell–BRST strong Jacobi on the complete physical smooth state. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
local notation "GaugeSmooth" => GlobalPairedGaugeLieSmooth period hPeriod
local notation "GaugeL2" => GlobalPairedGaugeLieL2 period hPeriod
local instance : NormedSpace Real GaugeL2 := inferInstance

open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local instance gaugeGroup : NormedAddCommGroup GaugeL2 := inferInstance
local instance : SeminormedAddCommGroup GaugeL2 := (gaugeGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real GaugeL2 := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
local notation "Full" => IntrinsicAbelianFullL2 period hPeriod
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Maxwell := graphInnerProductSpace period hPeriod
local instance : NormedSpace Real Maxwell := inferInstance
local notation "FullGraph" => IntrinsicAbelianFullGraph period hPeriod
local instance graphGroup : NormedAddCommGroup FullGraph := inferInstance
local instance : SeminormedAddCommGroup FullGraph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real FullGraph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : CompleteSpace FullGraph := intrinsicAbelianFullGraph_complete period hPeriod
local instance : NormedSpace Real FullGraph := (intrinsicAbelianFullGraphInnerProductSpace period hPeriod).toNormedSpace

private def lpPair {S E F : Type*} [AddCommGroup S] [Module Real S]
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    (first : S →ₗ[Real] E) (second : S →ₗ[Real] F) : S →ₗ[Real] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toLinearMap.comp (first.prod second)

private def bProjection : State →ₗ[Real] GaugeSmooth where
  toFun state sector := (state.nonminimal sector).nakanishiLautrup.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def aProjection : State →ₗ[Real] GaugeSmooth where
  toFun state sector := (state.nonminimal sector).antighost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def cProjection : State →ₗ[Real] GaugeSmooth where
  toFun state sector := (state.nonminimal sector).ghost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (couplings : GlobalCandidateAActionCouplings)

/-- Columns are (Maxwell A + Lorenz* B, Lorenz A − B, FP c, FP* antighost). -/
def intrinsicAbelianFullStrongSmooth : State →ₗ[Real] Full :=
  lpPair
    (lpPair
      ((intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings).comp
          (globalPairedAbelianBRSTPotentialProjectionLinearMap period hPeriod) +
        (intrinsicAbelianLorenzAdjointSmooth period hPeriod).comp (bProjection period hPeriod))
      ((globalPairedAbelianLorenzL2LinearMap period hPeriod (fun _ => base)).comp
          (globalPairedAbelianBRSTPotentialProjectionLinearMap period hPeriod) -
        (globalPairedGaugeLieL2LinearMap period hPeriod).comp (bProjection period hPeriod)))
    (lpPair
      ((globalPairedAbelianFPL2LinearMap period hPeriod (fun _ => base)).comp (cProjection period hPeriod))
      ((pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base)).comp (aProjection period hPeriod)))

/-- All columns together represent the unchanged native Maxwell plus BRST Hessian. -/
theorem intrinsicAbelianFullStrongSmooth_pairing (first second : State) :
    inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianFullL2Smooth period hPeriod second) =
    intrinsicAbelianMaxwellGraphHessian period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first.potential)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second.potential) +
    globalPairedAbelianOffShellHessian period hPeriod (fun _ => base)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base) first)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base) second) := by
  have hLorenz := (real_inner_comm (intrinsicAbelianLorenzAdjointSmooth period hPeriod (bProjection period hPeriod first))
    (intrinsicAbelianPotentialL2Smooth period hPeriod second.potential)).symm.trans
      ((intrinsicAbelianLorenzAdjointSmooth_pairing period hPeriod second.potential (bProjection period hPeriod first)).symm.trans
        (real_inner_comm _ _))
  have hGhost := (real_inner_comm (pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base) (aProjection period hPeriod first))
    (globalPairedGaugeLieL2LinearMap period hPeriod (cProjection period hPeriod second))).symm.trans
      ((frameFreePairedFPCanonicalAdjoint_pairing period hPeriod (fun _ => base)
        (cProjection period hPeriod second) (aProjection period hPeriod first)).symm.trans (real_inner_comm _ _))
  simp only [WithLp.prod_inner_apply, globalPairedAbelianOffShellHessian_apply,
    globalPairedAbelianOffShellLorenzProjection_smooth, globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth, globalPairedAbelianOffShellFPProjection_smooth]
  change (inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first.potential +
      intrinsicAbelianLorenzAdjointSmooth period hPeriod (bProjection period hPeriod first))
      (intrinsicAbelianPotentialL2Smooth period hPeriod second.potential) +
    inner Real (globalPairedAbelianLorenzL2LinearMap period hPeriod (fun _ => base) first.potential -
      globalPairedGaugeLieL2LinearMap period hPeriod (bProjection period hPeriod first))
      (globalPairedGaugeLieL2LinearMap period hPeriod (bProjection period hPeriod second))) +
    (inner Real (globalPairedAbelianFPL2LinearMap period hPeriod (fun _ => base) (cProjection period hPeriod first))
      (globalPairedGaugeLieL2LinearMap period hPeriod (aProjection period hPeriod second)) +
    inner Real (pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base) (aProjection period hPeriod first))
      (globalPairedGaugeLieL2LinearMap period hPeriod (cProjection period hPeriod second))) = _
  refine (congrArg₂ (fun x y : Real => x + y)
    (congrArg₂ (fun x y : Real => x + y)
      ((inner_add_left _ _ _).trans (congrArg₂ (fun x y : Real => x + y)
        (intrinsicAbelianMaxwellStrongSmooth_eq_graphHessian period hPeriod couplings first.potential second.potential) hLorenz))
      (inner_sub_left _ _ _))
    (congrArg (fun value : Real => inner Real
      (globalPairedAbelianFPL2LinearMap period hPeriod (fun _ => base) (cProjection period hPeriod first))
      (globalPairedGaugeLieL2LinearMap period hPeriod (aProjection period hPeriod second)) + value) hGhost)).trans ?_
  simp only [bProjection, aProjection, cProjection, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- Exact agreement with the existing full native graph Hessian. -/
theorem intrinsicAbelianFullStrongSmooth_eq_graphHessian (first second : State) :
    inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianFullL2Smooth period hPeriod second) =
    intrinsicAbelianFullGraphHessian period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first) (intrinsicAbelianFullSmooth period hPeriod second) := by
  have hGraph : inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first)) (intrinsicAbelianFullSmooth period hPeriod second) =
      intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod first) (intrinsicAbelianFullSmooth period hPeriod second) :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
  have hRiesz := intrinsicAbelianFullGraphRiesz_pairing period hPeriod couplings
    (intrinsicAbelianFullSmooth period hPeriod first) (intrinsicAbelianFullSmooth period hPeriod second)
  simp only [intrinsicAbelianFullMaxwell_smooth, intrinsicAbelianFullBRST_smooth,
    intrinsicAbelianMaxwellGraphRiesz_pairing] at hRiesz
  exact (intrinsicAbelianFullStrongSmooth_pairing period hPeriod couplings first second).trans (hRiesz.symm.trans hGraph)

theorem intrinsicAbelianFullStrongSmooth_symmetric (first second : State) :
    inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianFullL2Smooth period hPeriod second) =
    inner Real (intrinsicAbelianFullL2Smooth period hPeriod first)
      (intrinsicAbelianFullStrongSmooth period hPeriod couplings second) :=
  (intrinsicAbelianFullStrongSmooth_eq_graphHessian period hPeriod couplings first second).trans
    ((intrinsicAbelianFullGraphHessian_comm period hPeriod couplings _ _).trans
      ((intrinsicAbelianFullStrongSmooth_eq_graphHessian period hPeriod couplings second first).symm.trans
        (real_inner_comm _ _)))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
