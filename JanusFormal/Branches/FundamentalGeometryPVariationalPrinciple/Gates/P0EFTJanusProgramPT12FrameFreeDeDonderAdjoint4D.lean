import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Equiv4D

/-! Physical tensor L2 representatives of native de Donder adjoint columns. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
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

/-- The evaluation maps retain the relations among redundant tensor coordinates. -/
def frameFreeTensorCoordinate (row column : N) : TensorL2 →L[Real] H :=
  (PiLp.proj 2 (fun _ : N × N => H) (row, column)).comp (frameTensorL2Space period hPeriod frame).subtypeL

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "g" => finiteFrameInverseMetricCoefficient period hPeriod frame metric metric
local notation "Γ" => finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric
local notation "q" => frameFreeTensorCoordinate period hPeriod
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod
local notation "mul" => canonicalScalarMul period hPeriod
local notation "derivAdj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame

/-- The differentiated trace is transposed before multiplying by the inverse metric. -/
def frameFreeDeDonderTraceAdjointColumn (last : N) (test : Scalar) : TensorL2 :=
  ∑ i : N, ∑ j : N, (q i j).adjoint (incl (mul (g i j) (derivAdj last test)))

theorem frameFreeDeDonderTraceAdjointColumn_pairing (tensor : Tensor) (last : N) (test : Scalar) :
    inner Real (incl (canonicalFrameDerivativeSmooth period hPeriod frame last
      (∑ i : N, ∑ j : N, mul (g i j) (generalMetricFrameCoefficient period hPeriod frame tensor i j))))
      (incl test) = inner Real (inc tensor) (frameFreeDeDonderTraceAdjointColumn period hPeriod metric last test) := by
  refine (frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame last _ test).trans ?_
  simp only [map_sum, sum_inner, frameFreeDeDonderTraceAdjointColumn, inner_sum,
    ContinuousLinearMap.adjoint_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact canonicalScalarMul_pairing period hPeriod _ _ _

/-- Concrete canonical-volume adjoint, including both connection terms and the trace. -/
def frameFreeDeDonderAdjointColumn (last : N) (test : Scalar) : TensorL2 :=
  (∑ i : N, ∑ j : N, ((q j last).adjoint (incl (derivAdj i (mul (g i j) test))) -
    ∑ k : N, (q k last).adjoint (incl (mul (Γ k i j) (mul (g i j) test))) -
    ∑ k : N, (q j k).adjoint (incl (mul (Γ k i last) (mul (g i j) test))))) -
    (1 / 2 : Real) • frameFreeDeDonderTraceAdjointColumn period hPeriod metric last test

theorem frameFreeDeDonderAdjointColumn_pairing (tensor : Tensor) (last : N) (test : Scalar) :
    inner Real (incl (globalSmoothCovectorFrameCoefficient period hPeriod
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor) last)) (incl test) =
      inner Real (inc tensor) (frameFreeDeDonderAdjointColumn period hPeriod metric last test) := by
  rw [frameFreeDeDonder_scalar_expression]
  unfold frameFreeDeDonderAdjointColumn
  rw [map_sub, map_smul, inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right]
  apply congrArg₂ (fun x y : Real => x - y)
  · simp only [map_sum, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [canonicalScalarMul_pairing]
    simp only [map_sub, inner_sub_left, map_sum, sum_inner, inner_sub_right, inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
    apply congrArg₂ (fun x y : Real => x - y)
    · apply congrArg₂ (fun x y : Real => x - y)
      · exact frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame i _ _
      · apply Finset.sum_congr rfl
        intro k _
        exact canonicalScalarMul_pairing period hPeriod _ _ _
    · apply Finset.sum_congr rfl
      intro k _
      exact canonicalScalarMul_pairing period hPeriod _ _ _
  · exact congrArg (fun v : Real => (1 / 2 : Real) * v)
      (frameFreeDeDonderTraceAdjointColumn_pairing period hPeriod metric tensor last test)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
