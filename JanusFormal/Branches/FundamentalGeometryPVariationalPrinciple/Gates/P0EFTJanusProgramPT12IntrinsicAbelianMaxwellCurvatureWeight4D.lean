import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-! The symmetric native Maxwell weight acts in curvature L² and preserves smooth adjoint tests. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
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
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
open P0EFTJanusProgramPGlobalCovariantAction4D
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod

def intrinsicAbelianMaxwellCurvatureSectorWeight (transpose : Bool) (sector : Sector) : Curvature →L[Real] Curvature :=
  ∑ component : Fin 2, ∑ first : N, ∑ second : N, ∑ raisedFirst : N, ∑ raisedSecond : N,
    if transpose then
      intrinsicAbelianCurvatureWeightColumn period hPeriod
        (sector, component, first, second) (sector, component, raisedFirst, raisedSecond)
        (intrinsicAbelianMaxwellWeight period hPeriod first second raisedFirst raisedSecond)
    else
      intrinsicAbelianCurvatureWeightColumn period hPeriod
        (sector, component, raisedFirst, raisedSecond) (sector, component, first, second)
        (intrinsicAbelianMaxwellWeight period hPeriod first second raisedFirst raisedSecond)

theorem intrinsicAbelianMaxwellCurvatureSectorWeight_transpose (sector : Sector) (first second : Curvature) :
    inner Real (intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod false sector first) second =
    inner Real first (intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod true sector second) := by
  simp only [intrinsicAbelianMaxwellCurvatureSectorWeight, Bool.false_eq_true, ↓reduceIte,
    sum_apply, sum_inner, inner_sum]
  iterate 5 (apply Finset.sum_congr rfl; intro index hIndex)
  exact intrinsicAbelianCurvatureWeightColumn_transpose period hPeriod _ _ _ first second

theorem intrinsicAbelianMaxwellCurvatureSectorWeight_mem_adjoint
    (transpose : Bool) (sector : Sector) (tests : Index → Scalar) :
    intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod transpose sector
      (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain := by
  classical
  simp only [intrinsicAbelianMaxwellCurvatureSectorWeight, sum_apply]
  apply Submodule.sum_mem
  intro component _
  apply Submodule.sum_mem
  intro first _
  apply Submodule.sum_mem
  intro second _
  apply Submodule.sum_mem
  intro raisedFirst _
  apply Submodule.sum_mem
  intro raisedSecond _
  cases transpose <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact intrinsicAbelianCurvatureWeightColumn_mem_adjoint period hPeriod _ _ _ tests

def intrinsicAbelianMaxwellCurvaturePairedWeight (couplings : GlobalCandidateAActionCouplings)
    (transpose : Bool) : Curvature →L[Real] Curvature :=
  couplings.plusMaxwellScale • intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod transpose .plus +
    couplings.minusMaxwellScale • intrinsicAbelianMaxwellCurvatureSectorWeight period hPeriod transpose .minus

theorem intrinsicAbelianMaxwellCurvaturePairedWeight_transpose (couplings : GlobalCandidateAActionCouplings)
    (first second : Curvature) :
    inner Real (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings false first) second =
      inner Real first (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings true second) := by
  simp only [intrinsicAbelianMaxwellCurvaturePairedWeight, add_apply,
    smul_apply, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    intrinsicAbelianMaxwellCurvatureSectorWeight_transpose]

def intrinsicAbelianMaxwellCurvatureWeight (couplings : GlobalCandidateAActionCouplings) : Curvature →L[Real] Curvature :=
  intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings false +
    intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings true

theorem intrinsicAbelianMaxwellCurvatureWeight_symmetric (couplings : GlobalCandidateAActionCouplings)
    (first second : Curvature) :
    inner Real (intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings first) second =
      inner Real first (intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings second) := by
  have hTranspose := intrinsicAbelianMaxwellCurvaturePairedWeight_transpose period hPeriod couplings first second
  have hReverse : inner Real (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings true first) second =
      inner Real first (intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings false second) :=
    (real_inner_comm _ _).trans
      ((intrinsicAbelianMaxwellCurvaturePairedWeight_transpose period hPeriod couplings second first).symm.trans
        (real_inner_comm _ _))
  simp only [intrinsicAbelianMaxwellCurvatureWeight, add_apply, inner_add_left, inner_add_right]
  rw [hTranspose, hReverse, add_comm]

theorem intrinsicAbelianMaxwellCurvatureWeight_mem_adjoint (couplings : GlobalCandidateAActionCouplings)
    (tests : Index → Scalar) :
    intrinsicAbelianMaxwellCurvatureWeight period hPeriod couplings
      (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain := by
  have hPaired (transpose : Bool) :
      intrinsicAbelianMaxwellCurvaturePairedWeight period hPeriod couplings transpose
        (intrinsicAbelianSmoothCurvatureL2 period hPeriod tests) ∈
        (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain :=
    Submodule.add_mem _
      (Submodule.smul_mem _ _ (intrinsicAbelianMaxwellCurvatureSectorWeight_mem_adjoint period hPeriod transpose .plus tests))
      (Submodule.smul_mem _ _ (intrinsicAbelianMaxwellCurvatureSectorWeight_mem_adjoint period hPeriod transpose .minus tests))
  exact Submodule.add_mem _ (hPaired false) (hPaired true)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
