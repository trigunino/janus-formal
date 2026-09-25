import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D

/-! Concrete physical adjoint of native diffeomorphism FP, by two scalar transpositions. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
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

open P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
open P0EFTJanusProgramPT12FrameFreeCartanScalar4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
local notation "Core" => FrameFreeGhostL2 period hPeriod metric
local instance ghostGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (ghostGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local notation "q" => frameFreeGhostCoordinate period hPeriod metric
local notation "inc" => frameFreeGhostL2Smooth period hPeriod metric
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod

open P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusFiniteFrameMetricContraction4D
local notation "g" => finiteFrameInverseMetricCoefficient period hPeriod frame metric metric
local notation "Γ" => finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric
local notation "derivAdj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame
local notation "cartanAdj" => frameFreeCartanAdjointColumn period hPeriod metric metric.tensor

private theorem weighted_cartan_pairing (ghost : Ghost) (first second : N) (weight test : Scalar) :
    inner Real (incl (mul weight (h (smoothMetricCartanAction period hPeriod ghost metric.tensor) first second)))
      (incl test) = inner Real (inc ghost) (cartanAdj first second (mul weight test)) :=
  (canonicalScalarMul_pairing period hPeriod weight _ test).trans
    (frameFreeCartanAdjointColumn_pairing period hPeriod metric metric.tensor ghost first second _)

private def fpTraceAdjoint (last : N) (test : Scalar) : Core :=
  ∑ i : N, ∑ j : N, cartanAdj i j (mul (g i j) (derivAdj last test))

private theorem fpTrace_pairing (ghost : Ghost) (last : N) (test : Scalar) :
    inner Real (incl (deriv last (∑ i : N, ∑ j : N,
      mul (g i j) (h (smoothMetricCartanAction period hPeriod ghost metric.tensor) i j)))) (incl test) =
      inner Real (inc ghost) (fpTraceAdjoint period hPeriod metric last test) := by
  refine (frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame last _ test).trans ?_
  simp only [map_sum, sum_inner, fpTraceAdjoint, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact weighted_cartan_pairing period hPeriod metric ghost i j _ _

/-- Actual FP adjoint column in physical ghost L²; no regular frame or terminal intertwiner. -/
def frameFreeDiffeomorphismFPAdjointColumn (last : N) (test : Scalar) : Core :=
  (∑ i : N, ∑ j : N, (cartanAdj j last (derivAdj i (mul (g i j) test)) -
    ∑ k : N, cartanAdj k last (mul (Γ k i j) (mul (g i j) test)) -
    ∑ k : N, cartanAdj j k (mul (Γ k i last) (mul (g i j) test)))) -
    (1 / 2 : Real) • fpTraceAdjoint period hPeriod metric last test

/-- Canonical-volume Green identity for the original diffeomorphism Faddeev–Popov operator. -/
theorem frameFreeDiffeomorphismFPAdjointColumn_pairing (ghost : Ghost) (last : N) (test : Scalar) :
    inner Real (globalDiffeomorphismFPL2LinearMap period hPeriod metric ⟨ghost⟩ last) (incl test) =
      inner Real (inc ghost) (frameFreeDiffeomorphismFPAdjointColumn period hPeriod metric last test) := by
  change inner Real (incl (globalSmoothCovectorFrameCoefficient period hPeriod
    (globalGeneralMetricDeDonderLinearMap period hPeriod metric
      (smoothMetricCartanAction period hPeriod ghost metric.tensor)) last)) (incl test) = _
  rw [frameFreeDeDonder_scalar_expression]
  unfold frameFreeDiffeomorphismFPAdjointColumn
  rw [map_sub, map_smul, inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right]
  apply congrArg₂ (fun x y : Real => x - y)
  · simp only [map_sum, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [canonicalScalarMul_pairing]
    simp only [map_sub, inner_sub_left, map_sum, sum_inner, inner_sub_right, inner_sum]
    apply congrArg₂ (fun x y : Real => x - y)
    · apply congrArg₂ (fun x y : Real => x - y)
      · exact (frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame i _ _).trans
          (frameFreeCartanAdjointColumn_pairing period hPeriod metric metric.tensor ghost j last _)
      · apply Finset.sum_congr rfl
        intro k _
        exact weighted_cartan_pairing period hPeriod metric ghost k last _ _
    · apply Finset.sum_congr rfl
      intro k _
      exact weighted_cartan_pairing period hPeriod metric ghost j k _ _
  · exact congrArg (fun v : Real => (1 / 2 : Real) * v)
      (fpTrace_pairing period hPeriod metric ghost last test)

def frameFreeDiffeomorphismFPSmoothL2 : Ghost →ₗ[Real] Ambient where
  toFun ghost := globalDiffeomorphismFPL2LinearMap period hPeriod metric ⟨ghost⟩
  map_add' first second := (globalDiffeomorphismFPL2LinearMap period hPeriod metric).map_add ⟨first⟩ ⟨second⟩
  map_smul' scalar ghost := (globalDiffeomorphismFPL2LinearMap period hPeriod metric).map_smul scalar ⟨ghost⟩

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
