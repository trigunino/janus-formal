import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D

/-! Native smooth curvature tensors form a concrete dense domain for the L² adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
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

def intrinsicAbelianSmoothCurvatureL2 : (Index → Scalar) →ₗ[Real] Curvature where
  toFun tests := WithLp.toLp 2 fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod (tests index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add _ _
  map_smul' scalar tests := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul scalar _

theorem intrinsicAbelianSmoothCurvatureL2_eq_sum (tests : Index → Scalar) :
    intrinsicAbelianSmoothCurvatureL2 period hPeriod tests =
      ∑ index, intrinsicAbelianCurvatureTest period hPeriod index (tests index) := by
  apply ext_inner_left Real
  intro value
  simp only [inner_sum, intrinsicAbelianCurvatureTest, ContinuousLinearMap.adjoint_inner_right]
  exact PiLp.inner_apply value (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests)

theorem intrinsicAbelianSmoothCurvatureL2_denseRange :
    DenseRange (intrinsicAbelianSmoothCurvatureL2 period hPeriod) := by
  let coordinates := PiLp.continuousLinearEquiv 2 Real (fun _ : Index => H)
  have hPi : DenseRange (Pi.map fun _ : Index => smoothToCanonicalPhysicalBulkL2 period hPeriod) :=
    DenseRange.piMap fun _ => smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod
  exact coordinates.symm.surjective.denseRange.comp hPi coordinates.symm.continuous

def intrinsicAbelianCurvatureSmoothAdjoint (tests : Index → Scalar) : Potential :=
  ∑ index, intrinsicAbelianCurvatureAdjointColumn period hPeriod index (tests index)

theorem intrinsicAbelianCurvatureSmoothAdjoint_pairing
    (input : (intrinsicAbelianCurvatureMinimal period hPeriod).domain) (tests : Index → Scalar) :
    inner Real (intrinsicAbelianCurvatureMinimal period hPeriod input)
      (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) =
    inner Real input.val (intrinsicAbelianCurvatureSmoothAdjoint period hPeriod tests) := by
  rw [intrinsicAbelianSmoothCurvatureL2_eq_sum]
  simp only [intrinsicAbelianCurvatureSmoothAdjoint, inner_sum,
    intrinsicAbelianCurvatureAdjointColumn_pairing]

private theorem reverse_pairing (tests : Index → Scalar)
    (input : (intrinsicAbelianCurvatureMinimal period hPeriod).domain) :
    inner Real (intrinsicAbelianCurvatureSmoothAdjoint period hPeriod tests) input.val =
      inner Real (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests)
        (intrinsicAbelianCurvatureMinimal period hPeriod input) :=
  (real_inner_comm _ _).trans
    ((intrinsicAbelianCurvatureSmoothAdjoint_pairing period hPeriod input tests).symm.trans (real_inner_comm _ _))

theorem intrinsicAbelianSmoothCurvatureL2_mem_adjoint (tests : Index → Scalar) :
    intrinsicAbelianSmoothCurvatureL2 period hPeriod tests ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨intrinsicAbelianCurvatureSmoothAdjoint period hPeriod tests, reverse_pairing period hPeriod tests⟩

theorem intrinsicAbelianCurvatureAdjoint_smooth_apply (tests : Index → Scalar) :
    (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint
      ⟨intrinsicAbelianSmoothCurvatureL2 period hPeriod tests,
        intrinsicAbelianSmoothCurvatureL2_mem_adjoint period hPeriod tests⟩ =
      intrinsicAbelianCurvatureSmoothAdjoint period hPeriod tests :=
  LinearPMap.adjoint_apply_eq (intrinsicAbelianCurvatureMinimal_dense_domain period hPeriod) _
    (reverse_pairing period hPeriod tests)

theorem intrinsicAbelianCurvatureAdjoint_dense_domain :
    Dense ((intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain : Set Curvature) :=
  (intrinsicAbelianSmoothCurvatureL2_denseRange period hPeriod).mono
    (by rintro _ ⟨tests, rfl⟩; exact intrinsicAbelianSmoothCurvatureL2_mem_adjoint period hPeriod tests)

theorem intrinsicAbelianCurvatureAdjoint_isClosed :
    (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (intrinsicAbelianCurvatureMinimal_dense_domain period hPeriod)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
