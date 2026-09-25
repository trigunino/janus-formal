import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGeometry4D

/-! The genuine potential graph with both Lorenz and Maxwell curvature features.
The completion controls dA as well as A and the Lorenz divergence. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
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
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Old" => GlobalPairedAbelianLorenzGraphHilbert period hPeriod (fun _ => base)
local instance : NormedAddCommGroup Gauge := inferInstance
local instance : NormedSpace Real Gauge := inferInstance
local instance : CompleteSpace Old := globalPairedAbelianLorenzGraphCompleteSpace period hPeriod (fun _ => base)

private def smoothPotentialCoefficients : Smooth →ₗ[Real] (Sector → Gauge) where
  toFun potential sector := finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential sector)
  map_add' first second := by
    funext sector component index
    have hCoefficient : finiteFramePotentialCoefficient period hPeriod frame
        ((first + second) sector) component index =
      finiteFramePotentialCoefficient period hPeriod frame (first sector) component index +
        finiteFramePotentialCoefficient period hPeriod frame (second sector) component index := by
      apply SmoothQuotientField.ext period hPeriod Real
      intro point
      rfl
    exact (congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) hCoefficient).trans
      ((smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_add _ _)
  map_smul' scalar potential := by
    funext sector component index
    have hCoefficient : finiteFramePotentialCoefficient period hPeriod frame
        ((scalar • potential) sector) component index =
      scalar • finiteFramePotentialCoefficient period hPeriod frame (potential sector) component index := by
      apply SmoothQuotientField.ext period hPeriod Real
      intro point
      rfl
    exact (congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) hCoefficient).trans
      ((smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_smul scalar _)

abbrev IntrinsicAbelianCurvatureIndex :=
  Sector × Fin 2 × Fin (finiteSmoothTangentFrame period hPeriod).count ×
    Fin (finiteSmoothTangentFrame period hPeriod).count

abbrev IntrinsicAbelianCurvatureL2 :=
  PiLp 2 (fun _ : IntrinsicAbelianCurvatureIndex period hPeriod => CanonicalPhysicalBulkL2 period hPeriod)

private def curvatureCoordinate (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    Smooth →ₗ[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (ContinuousMap.toLp 2 μ Real).toLinearMap.comp
    ((frameFreeMaxwellCurvatureCLM period hPeriod frame base index.2.1 index.2.2.1 index.2.2.2).toLinearMap.comp
      ((LinearMap.proj index.1).comp (smoothPotentialCoefficients period hPeriod)))

def intrinsicAbelianCurvatureL2 : Smooth →ₗ[Real] IntrinsicAbelianCurvatureL2 period hPeriod where
  toFun potential := WithLp.toLp 2 fun index => curvatureCoordinate period hPeriod index potential
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (curvatureCoordinate period hPeriod index).map_add first second
  map_smul' scalar potential := by
    apply PiLp.ext
    intro index
    exact (curvatureCoordinate period hPeriod index).map_smul scalar potential

theorem intrinsicAbelianCurvatureL2_component (potential : Smooth)
    (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    intrinsicAbelianCurvatureL2 period hPeriod potential index =
      ContinuousMap.toLp 2 μ Real
        (finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame base
          (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential index.1))
          index.2.1 index.2.2.1 index.2.2.2) :=
  congrArg (ContinuousMap.toLp 2 μ Real)
    (frameFreeMaxwellCurvatureCLM_apply period hPeriod frame base index.2.1 index.2.2.1 index.2.2.2 _)

abbrev IntrinsicAbelianMaxwellLorenzAmbient := WithLp 2 (Old × IntrinsicAbelianCurvatureL2 period hPeriod)
local notation "Ambient" => IntrinsicAbelianMaxwellLorenzAmbient period hPeriod

def intrinsicAbelianMaxwellLorenzAmbientMap : Smooth →ₗ[Real] Ambient where
  toFun potential := WithLp.toLp 2
    (globalPairedAbelianLorenzSmoothEmbedding period hPeriod (fun _ => base) potential,
      intrinsicAbelianCurvatureL2 period hPeriod potential)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    exact Prod.ext
      ((globalPairedAbelianLorenzSmoothEmbedding period hPeriod (fun _ => base)).map_add first second)
      ((intrinsicAbelianCurvatureL2 period hPeriod).map_add first second)
  map_smul' scalar potential := by
    apply WithLp.ofLp_injective 2
    exact Prod.ext
      ((globalPairedAbelianLorenzSmoothEmbedding period hPeriod (fun _ => base)).map_smul scalar potential)
      ((intrinsicAbelianCurvatureL2 period hPeriod).map_smul scalar potential)

def intrinsicAbelianMaxwellLorenzSubmodule : Submodule Real Ambient :=
  (intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).range.topologicalClosure

abbrev IntrinsicAbelianMaxwellLorenzGraph := intrinsicAbelianMaxwellLorenzSubmodule period hPeriod
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod

instance intrinsicAbelianMaxwellLorenzGraph_complete : CompleteSpace Graph :=
  Submodule.topologicalClosure.completeSpace (intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).range

def intrinsicAbelianMaxwellLorenzSmooth : Smooth →ₗ[Real] Graph where
  toFun potential := ⟨intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod potential,
    (intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).range.le_topologicalClosure ⟨potential, rfl⟩⟩
  map_add' first second := Subtype.ext ((intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).map_add first second)
  map_smul' scalar potential := Subtype.ext ((intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).map_smul scalar potential)

theorem intrinsicAbelianMaxwellLorenzSmooth_denseRange :
    DenseRange (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) =
      ((intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).range : Set Ambient) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨potential, rfl⟩, rfl⟩
      exact ⟨potential, rfl⟩
    · rintro ⟨potential, rfl⟩
      exact ⟨intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential, ⟨potential, rfl⟩, rfl⟩
  change closure ((intrinsicAbelianMaxwellLorenzAmbientMap period hPeriod).range : Set Ambient) ⊆
    closure (Subtype.val '' Set.range (intrinsicAbelianMaxwellLorenzSmooth period hPeriod))
  rw [hRange]

theorem intrinsicAbelianMaxwellLorenzSmooth_injective :
    Function.Injective (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) := by
  intro first second hEqual
  exact globalPairedAbelianLorenzSmoothEmbedding_injective period hPeriod (fun _ => base)
    (congrArg (fun point : Graph => (point : Ambient).fst) hEqual)

def intrinsicAbelianMaxwellLorenzForget : Graph →L[Real] Old :=
  (WithLp.fstL 2 Real Old (IntrinsicAbelianCurvatureL2 period hPeriod)).comp
    (intrinsicAbelianMaxwellLorenzSubmodule period hPeriod).subtypeL

def intrinsicAbelianMaxwellLorenzCurvature : Graph →L[Real] IntrinsicAbelianCurvatureL2 period hPeriod :=
  (WithLp.sndL 2 Real Old (IntrinsicAbelianCurvatureL2 period hPeriod)).comp
    (intrinsicAbelianMaxwellLorenzSubmodule period hPeriod).subtypeL

theorem intrinsicAbelianMaxwellLorenzForget_smooth (potential : Smooth) :
    intrinsicAbelianMaxwellLorenzForget period hPeriod (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
      globalPairedAbelianLorenzSmoothEmbedding period hPeriod (fun _ => base) potential := rfl

theorem intrinsicAbelianMaxwellLorenzCurvature_smooth (potential : Smooth) :
    intrinsicAbelianMaxwellLorenzCurvature period hPeriod (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
      intrinsicAbelianCurvatureL2 period hPeriod potential := rfl

theorem intrinsicAbelianMaxwellLorenzCurvature_norm_le (point : Graph) :
    ‖intrinsicAbelianMaxwellLorenzCurvature period hPeriod point‖ ≤ ‖point‖ :=
  WithLp.norm_snd_le Old (point : Ambient)

theorem intrinsicAbelianMaxwellLorenzForget_norm_le (point : Graph) :
    ‖intrinsicAbelianMaxwellLorenzForget period hPeriod point‖ ≤ ‖point‖ :=
  WithLp.norm_fst_le Old (point : Ambient)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
