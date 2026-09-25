import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! Linear physical Lorenz adjoint on native paired smooth multipliers. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
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

private def lorenzAdjoint (test : GaugeSmooth) : Potential :=
  ∑ index : Sector × Fin 2, intrinsicAbelianLorenzAdjointColumn period hPeriod index.1 index.2
    (ghostComponent period hPeriod (test index.1) index.2)

private theorem lorenz_pairing (potential : Smooth) (test : GaugeSmooth) :
    inner Real (globalPairedAbelianLorenzL2LinearMap period hPeriod (fun _ => base) potential)
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod potential) (lorenzAdjoint period hPeriod test) := by
  rw [PiLp.inner_apply]
  simp only [lorenzAdjoint, inner_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact intrinsicAbelianLorenzAdjointColumn_pairing period hPeriod potential index.1 index.2 _

private theorem potential_ext {first second : Potential}
    (hPairing : ∀ potential : Smooth,
      inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod potential) first =
        inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod potential) second) : first = second := by
  have hAll : (fun test : Potential => inner Real test first) = (fun test : Potential => inner Real test second) := by
    apply (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod).equalizer
    · fun_prop
    · fun_prop
    · funext potential
      exact hPairing potential
  exact ext_inner_left Real (congrFun hAll)

/-- A concrete linear map into physical potential L², representing the canonical adjoint. -/
def intrinsicAbelianLorenzAdjointSmooth : GaugeSmooth →ₗ[Real] Potential where
  toFun := lorenzAdjoint period hPeriod
  map_add' first second := by
    apply potential_ext period hPeriod
    intro potential
    rw [inner_add_right, ← lorenz_pairing, ← lorenz_pairing, ← lorenz_pairing,
      map_add, inner_add_right]
  map_smul' scalar test := by
    apply potential_ext period hPeriod
    intro potential
    rw [real_inner_smul_right, ← lorenz_pairing, ← lorenz_pairing, map_smul, real_inner_smul_right]
    rfl

theorem intrinsicAbelianLorenzAdjointSmooth_pairing (potential : Smooth) (test : GaugeSmooth) :
    inner Real (globalPairedAbelianLorenzL2LinearMap period hPeriod (fun _ => base) potential)
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod potential)
      (intrinsicAbelianLorenzAdjointSmooth period hPeriod test) :=
  lorenz_pairing period hPeriod potential test

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
