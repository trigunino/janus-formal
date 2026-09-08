import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D

/-! # Intrinsic scalar contraction in a redundant finite frame -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod)

/-- Inverse metric coefficients in the transported canonical redundant dual family. -/
def finiteFrameLocalInverseMetricCoefficientAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) : Real :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ row column *
      finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate first
        (Pi.single row 1) *
      finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate second
        (Pi.single column 1)

/-- Scalar curvature formed from the projected Ricci coefficients and transported inverse metric. -/
def finiteFrameProjectedScalarCurvatureAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) : Real :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameLocalInverseMetricCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second *
      finiteFrameProjectedRicciCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second

private theorem four_sum_swap
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    (term : ι → ι → κ → κ → Real) :
    (∑ first : ι, ∑ second : ι, ∑ row : κ, ∑ column : κ,
      term first second row column) =
      ∑ row : κ, ∑ column : κ, ∑ first : ι, ∑ second : ι,
        term first second row column := by
  calc
    _ = ∑ first : ι, ∑ row : κ, ∑ second : ι, ∑ column : κ,
        term first second row column := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = ∑ row : κ, ∑ first : ι, ∑ second : ι, ∑ column : κ,
        term first second row column := by rw [Finset.sum_comm]
    _ = ∑ row : κ, ∑ first : ι, ∑ column : κ, ∑ second : ι,
        term first second row column := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_comm]

private theorem localRicci_redundant_expansion
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (row column : Fin 4) :
    localRicciCurvatureVector period hPeriod metric patch coordinate
        (Pi.single row 1) (Pi.single column 1) =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate first
              (Pi.single row 1) *
          finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate second
              (Pi.single column 1) *
          localRicciCurvatureVector period hPeriod metric patch coordinate
            (finiteFramePulledVector period hPeriod frame patch first coordinate)
            (finiteFramePulledVector period hPeriod frame patch second coordinate) := by
  let ricci := localRicciCurvatureBilinearMap period hPeriod metric patch coordinate
  have hFirst := finiteFramePulledVector_reconstructs period hPeriod frame baseMetric patch coordinate
    (Pi.single row 1)
  have hSecond := finiteFramePulledVector_reconstructs period hPeriod frame baseMetric patch coordinate
    (Pi.single column 1)
  change ricci (Pi.single row 1) (Pi.single column 1) = _
  conv_lhs => rw [hFirst, hSecond]
  simp only [map_smul, LinearMap.sum_apply, map_sum, ricci,
    localRicciCurvatureBilinearMap, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [LinearMap.smul_apply, smul_eq_mul]
  change _ * (_ * localRicciCurvatureVector period hPeriod metric patch coordinate
    (finiteFramePulledVector period hPeriod frame patch first coordinate)
    (finiteFramePulledVector period hPeriod frame patch second coordinate)) = _
  ring

/-- The canonically projected redundant contraction is intrinsic scalar curvature. -/
theorem finiteFrameProjectedScalarCurvatureAt_eq_intrinsic
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameProjectedScalarCurvatureAt period hPeriod frame baseMetric metric patch coordinate =
      localScalarCurvature period hPeriod metric patch coordinate := by
  classical
  unfold finiteFrameProjectedScalarCurvatureAt finiteFrameLocalInverseMetricCoefficientAt
    localScalarCurvature
  simp_rw [finiteFrameProjectedRicciCoefficientAt_eq_intrinsic period hPeriod frame baseMetric metric]
  simp_rw [Finset.sum_mul]
  rw [four_sum_swap]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  rw [← localRicciCurvatureVector_basis period hPeriod metric patch coordinate row column]
  rw [localRicci_redundant_expansion period hPeriod frame baseMetric metric patch coordinate row column]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

end
end P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D
end JanusFormal
