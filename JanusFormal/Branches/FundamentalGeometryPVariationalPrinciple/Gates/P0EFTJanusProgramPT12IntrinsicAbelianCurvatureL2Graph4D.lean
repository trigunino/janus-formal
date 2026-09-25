import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D

/-! Native Maxwell curvature is closable in the physical potential L² space. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D
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

def intrinsicAbelianCurvatureL2Graph : Submodule Real (Potential × Curvature) :=
  ((intrinsicAbelianPotentialL2Smooth period hPeriod).prod
    (intrinsicAbelianCurvatureL2 period hPeriod)).range.topologicalClosure

theorem intrinsicAbelianCurvatureL2_native (potential : Smooth)
    (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    intrinsicAbelianCurvatureL2 period hPeriod potential index =
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame (potential index.1)
        index.2.1 index.2.2.1 index.2.2.2) := by
  rw [intrinsicAbelianCurvatureL2_component, finiteFrameProjectedGaugeCurvatureC0Coefficient_smooth]
  rfl

/-- The L² graph closure satisfies the native weak Cartan identity. -/
theorem intrinsicAbelianCurvatureL2Graph_pairing
    (point : intrinsicAbelianCurvatureL2Graph period hPeriod)
    (sector : Sector) (component : Fin 2)
    (first second : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : Scalar) :
    inner Real (point.val.2 (sector, component, first, second))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (point.val.1.val (sector, component, second))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame first test)) -
    inner Real (point.val.1.val (sector, component, first))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame second test)) -
    ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count,
      inner Real (point.val.1.val (sector, component, upper))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (canonicalScalarMul period hPeriod
            (finiteFrameStructureCoefficient period hPeriod frame base first second upper) test)) := by
  have hClosed : IsClosed {pair : Potential × Curvature |
      inner Real (pair.2 (sector, component, first, second))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (pair.1.val (sector, component, second))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (frameFreeFrameDerivativeAdjoint period hPeriod base frame first test)) -
      inner Real (pair.1.val (sector, component, first))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (frameFreeFrameDerivativeAdjoint period hPeriod base frame second test)) -
      ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count,
        inner Real (pair.1.val (sector, component, upper))
          (smoothToCanonicalPhysicalBulkL2 period hPeriod
            (canonicalScalarMul period hPeriod
              (finiteFrameStructureCoefficient period hPeriod frame base first second upper) test))} := by
    apply isClosed_eq <;> fun_prop
  apply closure_minimal (s := (((intrinsicAbelianPotentialL2Smooth period hPeriod).prod
    (intrinsicAbelianCurvatureL2 period hPeriod)).range : Set _)) ?_ hClosed point.property
  rintro _ ⟨potential, rfl⟩
  change inner Real (intrinsicAbelianCurvatureL2 period hPeriod potential (sector, component, first, second)) _ = _
  rw [intrinsicAbelianCurvatureL2_native]
  exact frameFreeMaxwellCurvature_pairing period hPeriod frame base (potential sector) component first second test

/-- The closure contains no curvature above a zero potential. -/
theorem intrinsicAbelianCurvatureL2Graph_input_injective :
    Function.Injective (fun point : intrinsicAbelianCurvatureL2Graph period hPeriod => point.val.1) := by
  intro first second hInput
  apply Subtype.ext
  refine Prod.ext hInput ?_
  apply PiLp.ext
  rintro ⟨sector, component, i, j⟩
  apply sub_eq_zero.mp
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  rw [inner_sub_left, intrinsicAbelianCurvatureL2Graph_pairing, intrinsicAbelianCurvatureL2Graph_pairing]
  simp only [hInput, sub_self]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D
