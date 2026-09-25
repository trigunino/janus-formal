import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D

/-! The completed Abelian gauge sector lies in the kernel of native closed curvature. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureExactComplex4D
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
open P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
local notation "Parameters" => Sector → SmoothQuotientField period hPeriod GaugeLieAlgebra

/-- d²=0 for the actual Cartan curvature of an exact gauge potential. -/
theorem intrinsicAbelianSmoothCurvature_exact
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (first second : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame
      (exactGaugePotential period hPeriod parameter) component first second = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  change _ = (0 : Real)
  rw [← witness.coordinate_eq, finiteFrameSmoothGaugeCurvatureCoefficient_eq_local]
  have hLocal : localGaugeCurvature period hPeriod (exactGaugePotential period hPeriod parameter)
      component witness.patch witness.coordinate = 0 := by
    have hZero : localGaugeOneForm period hPeriod 0 component witness.patch = 0 := by
      funext coordinate
      simp only [localGaugeOneForm]
      change (∑ index : Fin 4, (0 : Real) • _) = 0
      simp
    have hExact : localGaugeCurvature period hPeriod (exactGaugePotential period hPeriod parameter)
        component witness.patch = localGaugeCurvature period hPeriod 0 component witness.patch := by
      simpa only [gaugeTransform, zero_add] using
        localGaugeCurvature_gaugeTransform period hPeriod parameter 0 component witness.patch
    rw [hExact, localGaugeCurvature, hZero]
    simp only [extDeriv, fderiv_zero, Pi.zero_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin, map_zero]
  rw [hLocal]
  rfl

theorem intrinsicAbelianCurvatureL2_exact (parameters : Parameters) :
    intrinsicAbelianCurvatureL2 period hPeriod
      (fun sector => exactGaugePotential period hPeriod (parameters sector)) = 0 := by
  apply PiLp.ext
  rintro ⟨sector, component, first, second⟩
  rw [intrinsicAbelianCurvatureL2_native, intrinsicAbelianSmoothCurvature_exact, map_zero]
  rfl

/-- The actual closed curvature kernel, regarded as a subspace of physical potential L². -/
def intrinsicAbelianCurvatureZeroL2 : Submodule Real Potential :=
  (intrinsicAbelianCurvatureMinimal period hPeriod).graph.comap
    ((LinearMap.id : Potential →ₗ[Real] Potential).prod (0 : Potential →ₗ[Real] Curvature))

theorem intrinsicAbelianCurvatureZeroL2_isClosed :
    IsClosed (intrinsicAbelianCurvatureZeroL2 period hPeriod : Set Potential) :=
  (intrinsicAbelianCurvatureMinimal_isClosed period hPeriod).preimage
    (continuous_id.prodMk continuous_const)

/-- Closed span of genuine smooth Abelian gauge directions in the physical L² space. -/
def intrinsicAbelianExactPotentialL2 : Submodule Real Potential :=
  (Submodule.span Real (Set.range (fun parameters : Parameters =>
    intrinsicAbelianPotentialL2Smooth period hPeriod
      (fun sector => exactGaugePotential period hPeriod (parameters sector))))).topologicalClosure

/-- The completed exact sector still has zero native curvature. -/
theorem intrinsicAbelianExactPotentialL2_le_zero :
    intrinsicAbelianExactPotentialL2 period hPeriod ≤ intrinsicAbelianCurvatureZeroL2 period hPeriod := by
  apply closure_minimal ?_ (intrinsicAbelianCurvatureZeroL2_isClosed period hPeriod)
  apply Submodule.span_le.mpr
  rintro _ ⟨parameters, rfl⟩
  change (intrinsicAbelianPotentialL2Smooth period hPeriod
      (fun sector => exactGaugePotential period hPeriod (parameters sector)), 0) ∈
    (intrinsicAbelianCurvatureMinimal period hPeriod).graph
  rw [intrinsicAbelianCurvatureMinimal_graph]
  have hRaw := ((intrinsicAbelianPotentialL2Smooth period hPeriod).prod
    (intrinsicAbelianCurvatureL2 period hPeriod)).range.le_topologicalClosure
    ⟨(fun sector => exactGaugePotential period hPeriod (parameters sector)), rfl⟩
  change (intrinsicAbelianPotentialL2Smooth period hPeriod
      (fun sector => exactGaugePotential period hPeriod (parameters sector)),
    intrinsicAbelianCurvatureL2 period hPeriod
      (fun sector => exactGaugePotential period hPeriod (parameters sector))) ∈
      intrinsicAbelianCurvatureL2Graph period hPeriod at hRaw
  rw [intrinsicAbelianCurvatureL2_exact] at hRaw
  exact hRaw

theorem intrinsicAbelianExactPotentialL2_graph
    (potential : intrinsicAbelianExactPotentialL2 period hPeriod) :
    (potential.val, 0) ∈ (intrinsicAbelianCurvatureMinimal period hPeriod).graph :=
  intrinsicAbelianExactPotentialL2_le_zero period hPeriod potential.property

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureExactComplex4D
