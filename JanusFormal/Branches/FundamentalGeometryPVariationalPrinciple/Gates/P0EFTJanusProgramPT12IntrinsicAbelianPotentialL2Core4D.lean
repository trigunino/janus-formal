import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D

/-! The native paired potential space completed in its physical L² norm. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
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
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Ambient" => GlobalPairedAbelianPotentialL2 period hPeriod

/-- The physical L² space retains the relations among redundant potential coordinates. -/
def intrinsicAbelianPotentialL2Submodule : Submodule Real Ambient :=
  (globalPairedAbelianPotentialL2LinearMap period hPeriod).range.topologicalClosure

abbrev IntrinsicAbelianPotentialL2Core := intrinsicAbelianPotentialL2Submodule period hPeriod
local notation "Core" => IntrinsicAbelianPotentialL2Core period hPeriod

instance intrinsicAbelianPotentialL2Core_complete : CompleteSpace Core :=
  Submodule.topologicalClosure.completeSpace (globalPairedAbelianPotentialL2LinearMap period hPeriod).range

def intrinsicAbelianPotentialL2Smooth : Smooth →ₗ[Real] Core where
  toFun potential := ⟨globalPairedAbelianPotentialL2LinearMap period hPeriod potential,
    (globalPairedAbelianPotentialL2LinearMap period hPeriod).range.le_topologicalClosure ⟨potential, rfl⟩⟩
  map_add' first second := Subtype.ext ((globalPairedAbelianPotentialL2LinearMap period hPeriod).map_add first second)
  map_smul' scalar potential := Subtype.ext ((globalPairedAbelianPotentialL2LinearMap period hPeriod).map_smul scalar potential)

theorem intrinsicAbelianPotentialL2Smooth_injective :
    Function.Injective (intrinsicAbelianPotentialL2Smooth period hPeriod) := by
  intro first second hEqual
  funext sector
  apply P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D.gaugePotentialL2Coordinates_injective period hPeriod
  funext component index
  exact congrArg (fun point : Core => point.val (sector, component, index)) hEqual

theorem intrinsicAbelianPotentialL2Smooth_denseRange :
    DenseRange (intrinsicAbelianPotentialL2Smooth period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (intrinsicAbelianPotentialL2Smooth period hPeriod) =
      ((globalPairedAbelianPotentialL2LinearMap period hPeriod).range : Set Ambient) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨potential, rfl⟩, rfl⟩
      exact ⟨potential, rfl⟩
    · rintro ⟨potential, rfl⟩
      exact ⟨intrinsicAbelianPotentialL2Smooth period hPeriod potential, ⟨potential, rfl⟩, rfl⟩
  change closure ((globalPairedAbelianPotentialL2LinearMap period hPeriod).range : Set Ambient) ⊆
    closure (Subtype.val '' Set.range (intrinsicAbelianPotentialL2Smooth period hPeriod))
  rw [hRange]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
