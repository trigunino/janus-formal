import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CartanFirstJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D

/-! Native Cartan as first-order columns of recovered physical ghost coefficients. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeCartanScalar4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Ghost" => CInfinityDiffeomorphismGhost period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Ambient" => GlobalDiffeomorphismVectorL2 period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusH1GraphTrace4D
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
local notation "h" => generalMetricFrameCoefficient period hPeriod frame
local notation "bracket" => finiteFrameStructureCoefficient period hPeriod frame metric
local notation "deriv" => canonicalFrameDerivativeSmooth period hPeriod frame
local notation "mul" => canonicalScalarMul period hPeriod

def frameFreeCartanZeroth (tensor : Tensor) (direction first second : N) : Scalar :=
  deriv direction (h tensor first second) -
    ∑ other : N, (mul (bracket direction first other) (h tensor other second) +
      mul (bracket direction second other) (h tensor first other))

/-- Full metric Lie derivative, including finite-frame bracket corrections. -/
theorem frameFreeCartan_scalar_expression (tensor : Tensor) (ghost : Ghost) (first second : N) :
    h (smoothMetricCartanAction period hPeriod ghost tensor) first second =
      ∑ direction : N, canonicalFirstOrderColumn period hPeriod frame first second
        (frameFreeCartanZeroth period hPeriod metric tensor direction first second)
        (h tensor direction second) (h tensor first direction)
        (generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost direction) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hNative := smoothMetricCartanAction_finiteFrameCoefficient period hPeriod frame metric
    (generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost) tensor point first second
  rw [finiteFrameVectorFromSmoothCoefficients_reconstructs] at hNative
  refine hNative.trans ?_
  rw [canonicalScalar_sum_apply]
  apply Finset.sum_congr rfl
  intro direction _
  change _ = ((deriv direction (h tensor first second) -
    ∑ other : N, (mul (bracket direction first other) (h tensor other second) +
      mul (bracket direction second other) (h tensor first other))) point *
      generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost direction point +
    h tensor direction second point *
      frameDerivative period hPeriod Real frame
        (generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost direction) point first) +
    h tensor first direction point * frameDerivative period hPeriod Real frame
      (generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost direction) point second
  change _ = ((_ - (∑ other : N, (mul (bracket direction first other) (h tensor other second) +
      mul (bracket direction second other) (h tensor first other))) point) * _ + _) + _
  rw [canonicalScalar_sum_apply]
  change _ = ((_ - ∑ other : N, (bracket direction first other point * h tensor other second point +
    bracket direction second other point * h tensor first other point)) * _ + _) + _
  simp only [mul_assoc, ← mul_add, ← Finset.mul_sum]
  simp only [canonicalFrameDerivativeSmooth, LinearMap.coe_mk, AddHom.coe_mk,
    P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D.frameDerivativeComponentField]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeCartanScalar4D
