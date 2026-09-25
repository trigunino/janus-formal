import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! The joint Maxwell and off-shell BRST completion of the same smooth states.
The two potential copies are linked by the closure of their common smooth image. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local notation "BRST" => GlobalPairedAbelianOffShellGraphHilbert period hPeriod (fun _ => base)
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Maxwell :=
  P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D.graphInnerProductSpace period hPeriod
local instance : NormedSpace Real Maxwell := (inferInstance : InnerProductSpace Real Maxwell).toNormedSpace
local instance brstGroup : NormedAddCommGroup BRST := inferInstance
local instance : SeminormedAddCommGroup BRST := (brstGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real BRST := inferInstance
local instance : NormedSpace Real BRST := (inferInstance : InnerProductSpace Real BRST).toNormedSpace
local instance : CompleteSpace BRST := globalPairedAbelianOffShellGraphCompleteSpace period hPeriod (fun _ => base)

abbrev IntrinsicAbelianFullAmbient := WithLp 2 (Maxwell × BRST)
local notation "Ambient" => IntrinsicAbelianFullAmbient period hPeriod
local instance ambientGroup : NormedAddCommGroup Ambient := inferInstance
local instance : SeminormedAddCommGroup Ambient := (ambientGroup period hPeriod).toSeminormedAddCommGroup
local instance : IsTopologicalAddGroup Ambient := SeminormedAddCommGroup.toIsTopologicalAddGroup
local instance : InnerProductSpace Real Ambient := inferInstance
local instance ambientNormedSpace : NormedSpace Real Ambient := (inferInstance : InnerProductSpace Real Ambient).toNormedSpace
local instance : Module Real Ambient := (ambientNormedSpace period hPeriod).toModule

def intrinsicAbelianFullAmbientMap : State →ₗ[Real] Ambient :=
  (WithLp.linearEquiv 2 Real (Maxwell × BRST)).symm.toLinearMap.comp
    (((intrinsicAbelianMaxwellLorenzSmooth period hPeriod).comp
      (globalPairedAbelianBRSTPotentialProjectionLinearMap period hPeriod)).prod
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base)))

def intrinsicAbelianFullSubmodule : Submodule Real Ambient :=
  (intrinsicAbelianFullAmbientMap period hPeriod).range.topologicalClosure

abbrev IntrinsicAbelianFullGraph := intrinsicAbelianFullSubmodule period hPeriod
local notation "Graph" => IntrinsicAbelianFullGraph period hPeriod
local instance graphGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphGroup period hPeriod).toSeminormedAddCommGroup

@[implicit_reducible]
def intrinsicAbelianFullGraphInnerProductSpace : InnerProductSpace Real Graph :=
  Submodule.innerProductSpace (𝕜 := Real) (E := Ambient) (intrinsicAbelianFullSubmodule period hPeriod)
local instance : InnerProductSpace Real Graph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : NormedSpace Real Graph := (intrinsicAbelianFullGraphInnerProductSpace period hPeriod).toNormedSpace

instance intrinsicAbelianFullGraph_complete : CompleteSpace Graph :=
  Submodule.topologicalClosure.completeSpace (intrinsicAbelianFullAmbientMap period hPeriod).range

def intrinsicAbelianFullSmooth : State →ₗ[Real] Graph where
  toFun state := ⟨intrinsicAbelianFullAmbientMap period hPeriod state,
    (intrinsicAbelianFullAmbientMap period hPeriod).range.le_topologicalClosure ⟨state, rfl⟩⟩
  map_add' first second := Subtype.ext ((intrinsicAbelianFullAmbientMap period hPeriod).map_add first second)
  map_smul' scalar state := Subtype.ext ((intrinsicAbelianFullAmbientMap period hPeriod).map_smul scalar state)

theorem intrinsicAbelianFullSmooth_injective : Function.Injective (intrinsicAbelianFullSmooth period hPeriod) := by
  intro first second hEqual
  exact globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod (fun _ => base)
    (congrArg (fun point : Graph => (point : Ambient).snd) hEqual)

theorem intrinsicAbelianFullSmooth_denseRange : DenseRange (intrinsicAbelianFullSmooth period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (intrinsicAbelianFullSmooth period hPeriod) =
      ((intrinsicAbelianFullAmbientMap period hPeriod).range : Set Ambient) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨state, rfl⟩, rfl⟩
      exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact ⟨intrinsicAbelianFullSmooth period hPeriod state, ⟨state, rfl⟩, rfl⟩
  change closure ((intrinsicAbelianFullAmbientMap period hPeriod).range : Set Ambient) ⊆
    closure (Subtype.val '' Set.range (intrinsicAbelianFullSmooth period hPeriod))
  rw [hRange]

def intrinsicAbelianFullMaxwell : Graph →L[Real] Maxwell :=
  (WithLp.fstL 2 Real Maxwell BRST).comp (intrinsicAbelianFullSubmodule period hPeriod).subtypeL

def intrinsicAbelianFullBRST : Graph →L[Real] BRST :=
  (WithLp.sndL 2 Real Maxwell BRST).comp (intrinsicAbelianFullSubmodule period hPeriod).subtypeL

theorem intrinsicAbelianFullMaxwell_smooth (state : State) :
    intrinsicAbelianFullMaxwell period hPeriod (intrinsicAbelianFullSmooth period hPeriod state) =
      intrinsicAbelianMaxwellLorenzSmooth period hPeriod state.potential := rfl

theorem intrinsicAbelianFullBRST_smooth (state : State) :
    intrinsicAbelianFullBRST period hPeriod (intrinsicAbelianFullSmooth period hPeriod state) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base) state := rfl

theorem intrinsicAbelianFullMaxwell_norm_le (point : Graph) :
    ‖intrinsicAbelianFullMaxwell period hPeriod point‖ ≤ ‖point‖ :=
  WithLp.norm_fst_le Maxwell (point : Ambient)

theorem intrinsicAbelianFullBRST_norm_le (point : Graph) :
    ‖intrinsicAbelianFullBRST period hPeriod point‖ ≤ ‖point‖ :=
  WithLp.norm_snd_le Maxwell (point : Ambient)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
