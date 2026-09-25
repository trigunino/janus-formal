import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeSecondJetAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D

/-! Physical L² representatives of native finite-frame tensor second-jet functionals.
Coordinate adjoints land in the actual tensor completion, retaining all relations. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeTensorSecondJetL24D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
open MeasureTheory
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "TensorL2" => FrameTensorL2Completion period hPeriod frame
local instance tensorGroup : NormedAddCommGroup TensorL2 := inferInstance
local instance : SeminormedAddCommGroup TensorL2 := (tensorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real TensorL2 := inferInstance
local instance : InnerProductSpace Real TensorL2 := Submodule.innerProductSpace (𝕜 := Real) _
local notation "inc" => frameTensorL2Smooth period hPeriod frame

open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeSecondJetAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
local notation "q" => frameFreeTensorCoordinate period hPeriod
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod
local notation "integral" => canonicalSmoothScalarIntegral period hPeriod
variable
  (value : FrameIndex period hPeriod → FrameIndex period hPeriod → SmoothQuotientField period hPeriod Real)
  (first : FrameIndex period hPeriod → FrameIndex period hPeriod → FrameIndex period hPeriod →
    SmoothQuotientField period hPeriod Real)
  (second : FrameIndex period hPeriod → FrameIndex period hPeriod → FrameIndex period hPeriod →
    FrameIndex period hPeriod → SmoothQuotientField period hPeriod Real)

def frameFreeTensorSecondJetFunctional (tensor : Tensor) : Real :=
  ∑ row, ∑ column, integral (frameFreeSecondJetDensity period hPeriod frame (value row column)
    (fun direction => first direction row column) (fun outer innerIndex => second outer innerIndex row column)
    (generalMetricFrameCoefficient period hPeriod frame tensor row column))

variable (metric : SmoothGeneralLorentzMetric period hPeriod)

/-- Orthogonal coordinate adjoints enforce the relations of the physical tensor completion. -/
def frameFreeTensorSecondJetL2 : TensorL2 :=
  ∑ row, ∑ column, (q row column).adjoint
    (incl (frameFreeSecondJetAdjoint period hPeriod metric frame (value row column)
      (fun direction => first direction row column) (fun outer innerIndex => second outer innerIndex row column)))

theorem frameFreeTensorSecondJetL2_pairing (tensor : Tensor) :
    inner Real (frameFreeTensorSecondJetL2 period hPeriod value first second metric) (inc tensor) =
      frameFreeTensorSecondJetFunctional period hPeriod value first second tensor := by
  simp only [frameFreeTensorSecondJetL2, frameFreeTensorSecondJetFunctional,
    sum_inner, ContinuousLinearMap.adjoint_inner_left]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  exact frameFreeSecondJetAdjoint_pairing period hPeriod metric frame (value row column)
    (fun direction => first direction row column) (fun outer innerIndex => second outer innerIndex row column)
    (generalMetricFrameCoefficient period hPeriod frame tensor row column)

def frameFreeTensorSecondJetCovector : TensorL2 →L[Real] Real :=
  innerSL Real (frameFreeTensorSecondJetL2 period hPeriod value first second metric)

theorem frameFreeTensorSecondJetCovector_smooth (tensor : Tensor) :
    frameFreeTensorSecondJetCovector period hPeriod value first second metric (inc tensor) =
      frameFreeTensorSecondJetFunctional period hPeriod value first second tensor :=
  frameFreeTensorSecondJetL2_pairing period hPeriod value first second metric tensor

theorem frameFreeTensorSecondJetFunctional_bound (tensor : Tensor) :
    ‖frameFreeTensorSecondJetFunctional period hPeriod value first second tensor‖ ≤
      ‖frameFreeTensorSecondJetL2 period hPeriod value first second metric‖ * ‖inc tensor‖ := by
  rw [← frameFreeTensorSecondJetL2_pairing period hPeriod value first second metric tensor]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeTensorSecondJetL24D
