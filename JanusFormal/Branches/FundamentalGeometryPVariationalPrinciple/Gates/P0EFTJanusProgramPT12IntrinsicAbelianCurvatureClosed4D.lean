import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The concrete closed Maxwell curvature operator in physical L². -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
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

/-- The minimal native curvature operator, from physical potential L² to curvature L². -/
def intrinsicAbelianCurvatureMinimal : Potential →ₗ.[Real] Curvature :=
  (intrinsicAbelianCurvatureL2Graph period hPeriod).toLinearPMap

theorem intrinsicAbelianCurvatureMinimal_graph :
    (intrinsicAbelianCurvatureMinimal period hPeriod).graph =
      intrinsicAbelianCurvatureL2Graph period hPeriod := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun point => point.val.2)
    (intrinsicAbelianCurvatureL2Graph_input_injective period hPeriod
      (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem intrinsicAbelianCurvatureMinimal_isClosed :
    (intrinsicAbelianCurvatureMinimal period hPeriod).IsClosed := by
  rw [LinearPMap.IsClosed, intrinsicAbelianCurvatureMinimal_graph]
  exact ((intrinsicAbelianPotentialL2Smooth period hPeriod).prod
    (intrinsicAbelianCurvatureL2 period hPeriod)).range.isClosed_topologicalClosure

theorem intrinsicAbelianCurvatureMinimal_smooth_mem (potential : Smooth) :
    intrinsicAbelianPotentialL2Smooth period hPeriod potential ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).domain :=
  ⟨(intrinsicAbelianPotentialL2Smooth period hPeriod potential,
    intrinsicAbelianCurvatureL2 period hPeriod potential),
    Submodule.le_topologicalClosure _ ⟨potential, rfl⟩, rfl⟩

theorem intrinsicAbelianCurvatureMinimal_smooth_apply (potential : Smooth) :
    intrinsicAbelianCurvatureMinimal period hPeriod
      ⟨intrinsicAbelianPotentialL2Smooth period hPeriod potential,
        intrinsicAbelianCurvatureMinimal_smooth_mem period hPeriod potential⟩ =
      intrinsicAbelianCurvatureL2 period hPeriod potential := by
  have hGraph := (intrinsicAbelianCurvatureMinimal period hPeriod).mem_graph
    ⟨intrinsicAbelianPotentialL2Smooth period hPeriod potential,
      intrinsicAbelianCurvatureMinimal_smooth_mem period hPeriod potential⟩
  rw [intrinsicAbelianCurvatureMinimal_graph] at hGraph
  exact congrArg (fun point => point.val.2)
    (intrinsicAbelianCurvatureL2Graph_input_injective period hPeriod
      (a₁ := ⟨_, hGraph⟩) (a₂ := ⟨_, Submodule.le_topologicalClosure _ ⟨potential, rfl⟩⟩) rfl)

theorem intrinsicAbelianCurvatureMinimal_dense_domain :
    Dense ((intrinsicAbelianCurvatureMinimal period hPeriod).domain : Set Potential) :=
  (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod).mono
    (by rintro _ ⟨potential, rfl⟩; exact intrinsicAbelianCurvatureMinimal_smooth_mem period hPeriod potential)

/-- Every closed L² realization of the same native smooth curvature extends this one. -/
theorem intrinsicAbelianCurvatureMinimal_le
    (extension : Potential →ₗ.[Real] Curvature) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : Smooth,
      (intrinsicAbelianPotentialL2Smooth period hPeriod potential,
        intrinsicAbelianCurvatureL2 period hPeriod potential) ∈ extension.graph) :
    intrinsicAbelianCurvatureMinimal period hPeriod ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [intrinsicAbelianCurvatureMinimal_graph]
  exact closure_minimal (by rintro pair ⟨potential, rfl⟩; exact hExtends potential) hClosed

/-- The native smooth potentials are a graph core of the closed curvature operator. -/
theorem intrinsicAbelianCurvatureMinimal_hasCore :
    (intrinsicAbelianCurvatureMinimal period hPeriod).HasCore
      (intrinsicAbelianPotentialL2Smooth period hPeriod).range := by
  let operator := intrinsicAbelianCurvatureMinimal period hPeriod
  let inclusion := intrinsicAbelianPotentialL2Smooth period hPeriod
  let curvature := intrinsicAbelianCurvatureL2 period hPeriod
  have hMem := intrinsicAbelianCurvatureMinimal_smooth_mem period hPeriod
  have hApply := intrinsicAbelianCurvatureMinimal_smooth_apply period hPeriod
  have hGraph : (operator.domRestrict inclusion.range).graph = (inclusion.prod curvature).range := by
    ext pair
    constructor
    · intro hPair
      obtain ⟨vector, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hPair
      obtain ⟨potential, hPotential⟩ := vector.property.1
      have hRestricted : operator.domRestrict inclusion.range vector = curvature potential :=
        (LinearPMap.domRestrict_apply (y := ⟨inclusion potential, hMem potential⟩) hPotential.symm).trans
          (hApply potential)
      exact ⟨potential, Prod.ext (hPotential.trans hInput) (hRestricted.symm.trans hOutput)⟩
    · rintro ⟨potential, rfl⟩
      apply (LinearPMap.mem_graph_iff _).mpr
      refine ⟨⟨inclusion potential, ⟨⟨potential, rfl⟩, hMem potential⟩⟩, rfl, ?_⟩
      exact (LinearPMap.domRestrict_apply (y := ⟨inclusion potential, hMem potential⟩) rfl).trans
        (hApply potential)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨potential, rfl⟩
    exact hMem potential
  · have hRestrict : operator.domRestrict inclusion.range ≤ operator := LinearPMap.domRestrict_le
    have hClosable := (intrinsicAbelianCurvatureMinimal_isClosed period hPeriod).isClosable.leIsClosable hRestrict
    apply LinearPMap.eq_of_eq_graph
    rw [← hClosable.graph_closure_eq_closure_graph, hGraph, intrinsicAbelianCurvatureMinimal_graph]
    rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
