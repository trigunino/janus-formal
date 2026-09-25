import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D

/-! The previous Maxwell--BRST completion is realized in the native closed curvature graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureGraphBridge4D
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
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Maxwell := inferInstance

/-- The completed Maxwell potential still belongs to the physical L² closure. -/
theorem intrinsicAbelianMaxwellPotential_mem (point : Maxwell) :
    intrinsicAbelianMaxwellPotential period hPeriod point ∈
      intrinsicAbelianPotentialL2Submodule period hPeriod := by
  have hClosed : IsClosed {point : Maxwell |
      intrinsicAbelianMaxwellPotential period hPeriod point ∈
        intrinsicAbelianPotentialL2Submodule period hPeriod} :=
    ((globalPairedAbelianPotentialL2LinearMap period hPeriod).range.isClosed_topologicalClosure).preimage
      (intrinsicAbelianMaxwellPotential period hPeriod).continuous
  have hRange : Set.range (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) ⊆
      {point : Maxwell | intrinsicAbelianMaxwellPotential period hPeriod point ∈
        intrinsicAbelianPotentialL2Submodule period hPeriod} := by
    rintro _ ⟨potential, rfl⟩
    exact (globalPairedAbelianPotentialL2LinearMap period hPeriod).range.le_topologicalClosure ⟨potential, rfl⟩
  exact closure_minimal hRange hClosed
    (by rw [(intrinsicAbelianMaxwellLorenzSmooth_denseRange period hPeriod).closure_range]; trivial)

def intrinsicAbelianMaxwellToPotentialL2 : Maxwell →L[Real] Potential :=
  (intrinsicAbelianMaxwellPotential period hPeriod).codRestrict
    (intrinsicAbelianPotentialL2Submodule period hPeriod) (intrinsicAbelianMaxwellPotential_mem period hPeriod)

theorem intrinsicAbelianMaxwellToPotentialL2_smooth (potential : Smooth) :
    intrinsicAbelianMaxwellToPotentialL2 period hPeriod
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
      intrinsicAbelianPotentialL2Smooth period hPeriod potential := rfl

/-- The curvature feature of every Maxwell graph vector is the value of the closed L² operator. -/
theorem intrinsicAbelianMaxwell_curvature_graph (point : Maxwell) :
    (intrinsicAbelianMaxwellToPotentialL2 period hPeriod point,
      intrinsicAbelianMaxwellLorenzCurvature period hPeriod point) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).graph := by
  let pair := (intrinsicAbelianMaxwellToPotentialL2 period hPeriod).prod
    (intrinsicAbelianMaxwellLorenzCurvature period hPeriod)
  have hClosed : IsClosed {point : Maxwell |
      pair point ∈ (intrinsicAbelianCurvatureMinimal period hPeriod).graph} :=
    (intrinsicAbelianCurvatureMinimal_isClosed period hPeriod).preimage pair.continuous
  have hRange : Set.range (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) ⊆
      {point : Maxwell | pair point ∈ (intrinsicAbelianCurvatureMinimal period hPeriod).graph} := by
    rintro _ ⟨potential, rfl⟩
    rw [intrinsicAbelianCurvatureMinimal_graph]
    exact Submodule.le_topologicalClosure _ ⟨potential, rfl⟩
  exact closure_minimal hRange hClosed
    (by rw [(intrinsicAbelianMaxwellLorenzSmooth_denseRange period hPeriod).closure_range]; trivial)

theorem intrinsicAbelianMaxwellToPotentialL2_mem_domain (point : Maxwell) :
    intrinsicAbelianMaxwellToPotentialL2 period hPeriod point ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).domain :=
  LinearPMap.mem_domain_of_mem_graph (intrinsicAbelianMaxwell_curvature_graph period hPeriod point)

theorem intrinsicAbelianCurvatureMinimal_maxwell_apply (point : Maxwell) :
    intrinsicAbelianCurvatureMinimal period hPeriod
      ⟨intrinsicAbelianMaxwellToPotentialL2 period hPeriod point,
        intrinsicAbelianMaxwellToPotentialL2_mem_domain period hPeriod point⟩ =
    intrinsicAbelianMaxwellLorenzCurvature period hPeriod point :=
  ((LinearPMap.image_iff (intrinsicAbelianMaxwellToPotentialL2_mem_domain period hPeriod point)).mpr
    (intrinsicAbelianMaxwell_curvature_graph period hPeriod point)).symm

/-- The joint Maxwell--BRST realization carries the same closed native curvature. -/
theorem intrinsicAbelianFull_curvature_graph (point : IntrinsicAbelianFullGraph period hPeriod) :
    (intrinsicAbelianMaxwellToPotentialL2 period hPeriod (intrinsicAbelianFullMaxwell period hPeriod point),
      intrinsicAbelianMaxwellLorenzCurvature period hPeriod (intrinsicAbelianFullMaxwell period hPeriod point)) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).graph :=
  intrinsicAbelianMaxwell_curvature_graph period hPeriod (intrinsicAbelianFullMaxwell period hPeriod point)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureGraphBridge4D
