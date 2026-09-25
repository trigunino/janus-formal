import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D

/-! Native Lorenz formal adjoint in the physical potential L² space. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod

/-- The native Lorenz operator is a finite sum of smooth first-order columns. -/
theorem intrinsicAbelianLorenz_scalar_expression
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    ghostComponent period hPeriod (globalGeneralMetricAbelianLorenzCodifferential period hPeriod base potential) component =
      ∑ i : N, ∑ j : N, canonicalScalarMul period hPeriod
        (finiteFrameInverseMetricCoefficient period hPeriod frame base base i j)
        (canonicalFrameDerivativeSmooth period hPeriod frame i
          (finiteFramePotentialCoefficient period hPeriod frame potential component j) -
          ∑ k : N, canonicalScalarMul period hPeriod
            (finiteFrameKoszulChristoffelCoefficient period hPeriod frame base base k i j)
            (finiteFramePotentialCoefficient period hPeriod frame potential component k)) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [canonicalScalar_sum_apply]
  change globalGeneralMetricAbelianLorenzCodifferential period hPeriod base potential point component = _
  rw [globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace period hPeriod frame base base]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _ = _ * (_ - (∑ k : N, canonicalScalarMul period hPeriod
    (finiteFrameKoszulChristoffelCoefficient period hPeriod frame base base k i j)
    (finiteFramePotentialCoefficient period hPeriod frame potential component k)) point)
  rw [canonicalScalar_sum_apply]
  rfl

/-- Explicit canonical-volume adjoint column, with no supplied regular-metric witness. -/
def intrinsicAbelianLorenzAdjointColumn (sector : Sector) (component : Fin 2) (test : Scalar) : Potential :=
  ∑ i : N, ∑ j : N, (
    (intrinsicAbelianPotentialCoordinate period hPeriod (sector, component, j)).adjoint
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod base frame i
          (canonicalScalarMul period hPeriod
            (finiteFrameInverseMetricCoefficient period hPeriod frame base base i j) test))) -
    ∑ k : N, (intrinsicAbelianPotentialCoordinate period hPeriod (sector, component, k)).adjoint
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalScalarMul period hPeriod
          (finiteFrameKoszulChristoffelCoefficient period hPeriod frame base base k i j)
          (canonicalScalarMul period hPeriod
            (finiteFrameInverseMetricCoefficient period hPeriod frame base base i j) test))))

/-- The constructed column represents the actual Lorenz pairing in physical L². -/
theorem intrinsicAbelianLorenzAdjointColumn_pairing
    (potential : Smooth) (sector : Sector) (component : Fin 2) (test : Scalar) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (ghostComponent period hPeriod
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod base (potential sector)) component))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (intrinsicAbelianPotentialL2Smooth period hPeriod potential)
      (intrinsicAbelianLorenzAdjointColumn period hPeriod sector component test) := by
  rw [intrinsicAbelianLorenz_scalar_expression]
  simp only [map_sum, sum_inner, intrinsicAbelianLorenzAdjointColumn, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [canonicalScalarMul_pairing]
  simp only [map_sub, inner_sub_left, map_sum, sum_inner, inner_sub_right, inner_sum,
    ContinuousLinearMap.adjoint_inner_right]
  apply congrArg₂ (fun x y : Real => x - y)
  · exact frameFreeFrameDerivativeAdjoint_pairing period hPeriod base frame i _ _
  · apply Finset.sum_congr rfl
    intro k _
    exact canonicalScalarMul_pairing period hPeriod _ _ _

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
