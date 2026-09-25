import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D

/-! No residual Maxwell curvature survives above a zero potential in the completed graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D
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

open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
open P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Potential" => GlobalPairedAbelianPotentialL2 period hPeriod
local notation "Curvature" => IntrinsicAbelianCurvatureL2 period hPeriod

/-- The original undifferentiated potential coordinates retained by the graph. -/
def intrinsicAbelianMaxwellPotential : Graph →L[Real] Potential :=
  ((WithLp.fstL 2 Real Potential (GlobalPairedAbelianLorenzL2 period hPeriod)).comp
    (globalPairedAbelianLorenzGraphSubmodule period hPeriod (fun _ => base)).subtypeL).comp
      (intrinsicAbelianMaxwellLorenzForget period hPeriod)

private def potentialFeature (sector : Sector) (component : Fin 2) (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    Graph →L[Real] H :=
  (PiLp.proj 2 (fun _ : GlobalPairedAbelianPotentialCoordinateIndex period hPeriod => H)
    (sector, component, index)).comp (intrinsicAbelianMaxwellPotential period hPeriod)

private theorem potentialFeature_smooth (potential : Smooth) (sector : Sector)
    (component : Fin 2) (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    potentialFeature period hPeriod sector component index
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame (potential sector) component index) := rfl

private def curvatureFeature (index : IntrinsicAbelianCurvatureIndex period hPeriod) : Graph →L[Real] H :=
  (PiLp.proj 2 (fun _ : IntrinsicAbelianCurvatureIndex period hPeriod => H) index).comp
    (intrinsicAbelianMaxwellLorenzCurvature period hPeriod)

private theorem curvatureFeature_smooth (potential : Smooth)
    (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    curvatureFeature period hPeriod index (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame (potential index.1)
        index.2.1 index.2.2.1 index.2.2.2) := by
  change intrinsicAbelianCurvatureL2 period hPeriod potential index = _
  rw [intrinsicAbelianCurvatureL2_component, finiteFrameProjectedGaugeCurvatureC0Coefficient_smooth]
  rfl

/-- The native weak curvature identity extends to the full completed graph. -/
theorem intrinsicAbelianMaxwellGraph_weak_curvature (point : Graph)
    (sector : Sector) (component : Fin 2) (first second : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : Scalar) :
    inner Real (curvatureFeature period hPeriod (sector, component, first, second) point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (potentialFeature period hPeriod sector component second point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame first test)) -
    inner Real (potentialFeature period hPeriod sector component first point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame second test)) -
    ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count, inner Real (potentialFeature period hPeriod sector component upper point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalScalarMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame base first second upper) test)) := by
  let lhs (point : Graph) := inner Real
    (curvatureFeature period hPeriod (sector, component, first, second) point)
    (smoothToCanonicalPhysicalBulkL2 period hPeriod test)
  let rhs (point : Graph) :=
    inner Real (potentialFeature period hPeriod sector component second point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame first test)) -
    inner Real (potentialFeature period hPeriod sector component first point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame second test)) -
    ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count, inner Real (potentialFeature period hPeriod sector component upper point)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalScalarMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame base first second upper) test))
  have hClosed : IsClosed {point : Graph | lhs point = rhs point} := by
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (intrinsicAbelianMaxwellLorenzSmooth period hPeriod) ⊆
      {point : Graph | lhs point = rhs point} := by
    rintro _ ⟨potential, rfl⟩
    dsimp only [Set.mem_setOf_eq, lhs, rhs]
    simp only [curvatureFeature_smooth, potentialFeature_smooth]
    exact frameFreeMaxwellCurvature_pairing period hPeriod frame base (potential sector)
      component first second test
  exact closure_minimal hRange hClosed
    (by rw [(intrinsicAbelianMaxwellLorenzSmooth_denseRange period hPeriod).closure_range]; trivial)

/-- Equal potential values force equal completed curvature, without controlling derivatives individually. -/
theorem intrinsicAbelianMaxwellCurvature_eq_of_potential_eq (first second : Graph)
    (hPotential : intrinsicAbelianMaxwellPotential period hPeriod first =
      intrinsicAbelianMaxwellPotential period hPeriod second) :
    intrinsicAbelianMaxwellLorenzCurvature period hPeriod first =
      intrinsicAbelianMaxwellLorenzCurvature period hPeriod second := by
  have hFeature (sector : Sector) (component : Fin 2) (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
      potentialFeature period hPeriod sector component index first =
        potentialFeature period hPeriod sector component index second :=
    congrArg (fun value : Potential => value (sector, component, index)) hPotential
  apply PiLp.ext
  rintro ⟨sector, component, i, j⟩
  apply sub_eq_zero.mp
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  change inner Real (curvatureFeature period hPeriod (sector, component, i, j) first -
    curvatureFeature period hPeriod (sector, component, i, j) second) _ = 0
  rw [inner_sub_left, intrinsicAbelianMaxwellGraph_weak_curvature,
    intrinsicAbelianMaxwellGraph_weak_curvature]
  simp only [hFeature, sub_self]

/-- The Maxwell completion embeds faithfully into the existing Lorenz graph. -/
theorem intrinsicAbelianMaxwellLorenzForget_injective :
    Function.Injective (intrinsicAbelianMaxwellLorenzForget period hPeriod) := by
  intro first second hForget
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  refine Prod.ext hForget ?_
  apply intrinsicAbelianMaxwellCurvature_eq_of_potential_eq
  exact congrArg (fun point : Old => (point.val).fst) hForget

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D
