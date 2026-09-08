import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MaxwellPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

/-! # Intrinsic bridge for the redundant finite-frame Maxwell pairing -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D
open P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D
open P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusFiniteFrameC2MaxwellPairing4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem smoothScalarSum_apply
    {ι : Type*} [Fintype ι]
    (fields : ι → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ index, fields index) point = ∑ index, fields index point := by
  let evaluation : SmoothScalarField period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

private theorem extDeriv_oneForm_apply_twoVectorFields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (oneForm : E → E [⋀^Fin 1]→L[Real] Real)
    (first second : E → E) (point : E)
    (hForm : DifferentiableAt Real oneForm point)
    (hFirst : DifferentiableAt Real first point)
    (hSecond : DifferentiableAt Real second point) :
    extDeriv oneForm point ![first point, second point] =
      fderiv Real (fun current => oneForm current (fun _ => second current))
          point (first point) -
        fderiv Real (fun current => oneForm current (fun _ => first current))
          point (second point) -
        oneForm point
          (fun _ => VectorField.lieBracket Real first second point) := by
  let fields : Fin 2 → E → E := ![first, second]
  have hVectors :
      (![first point, second point] : Fin 2 → E) = (fields · point) := by
    funext index
    fin_cases index <;> rfl
  rw [hVectors]
  rw [extDeriv_apply_vectorField
      (n := 0) (x := point) (F := Real)
      (V := fields) hForm (by
        intro index
        fin_cases index
        · exact hFirst
        · exact hSecond)]
  simp [fields, Fin.sum_univ_two]
  have hIci : Finset.Ici (0 : Fin 1) = Finset.univ := by
    ext index
    fin_cases index
    simp
  rw [hIci]
  simp only [Fin.sum_univ_one]
  have hRemoved (current : E) :
      Fin.removeNth (1 : Fin 2)
          (Matrix.vecCons (first current)
            (fun _ : Fin 1 => second current)) =
        (fun _ : Fin 1 => first current) := by
    funext index
    fin_cases index
    rfl
  simp_rw [hRemoved]
  have hBracket :
      Matrix.vecCons (VectorField.lieBracket Real first second point)
          (Fin.removeNth (0 : Fin 1)
            (fun _ : Fin 1 => second point)) =
        (fun _ : Fin 1 =>
          VectorField.lieBracket Real first second point) := by
    funext index
    fin_cases index
    rfl
  rw [hBracket]
  ring

private theorem localGaugeOneForm_finiteFramePulledVector
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin frame.count) :
    localGaugeOneForm period hPeriod potential component patch coordinate
        (fun _ => finiteFramePulledVector period hPeriod frame patch index coordinate) =
      finiteFramePotentialCoefficient period hPeriod frame potential component index
        (patch.coordinateMap coordinate) := by
  rw [localGaugeOneForm_apply,
    coordinateMap_mfderiv_finiteFramePulledVector]
  rfl

private theorem localGaugeOneForm_finiteFramePulled_derivative
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction index : Fin frame.count) :
    fderiv Real
        (fun current =>
          localGaugeOneForm period hPeriod potential component patch current
            (fun _ => finiteFramePulledVector period hPeriod frame patch index current))
        coordinate
        (finiteFramePulledVector period hPeriod frame patch direction coordinate) =
      frameDerivative period hPeriod Real frame
        (finiteFramePotentialCoefficient period hPeriod frame potential component index)
        (patch.coordinateMap coordinate) direction := by
  have hFunction :
      (fun current =>
        localGaugeOneForm period hPeriod potential component patch current
          (fun _ => finiteFramePulledVector period hPeriod frame patch index current)) =
        (finiteFramePotentialCoefficient period hPeriod frame potential component index).toFun ∘
          patch.coordinateMap := by
    funext current
    exact localGaugeOneForm_finiteFramePulledVector period hPeriod frame potential
      component patch current index
  rw [hFunction]
  exact fderiv_comp_coordinateMap_finiteFramePulledVector period hPeriod frame
    (finiteFramePotentialCoefficient period hPeriod frame potential component index)
    patch coordinate direction

private theorem localGaugeOneForm_lieBracket_finiteFramePulledVector
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin frame.count) :
    localGaugeOneForm period hPeriod potential component patch coordinate
        (fun _ =>
          VectorField.lieBracket (E := Vector4) Real
            (finiteFramePulledVector period hPeriod frame patch first)
            (finiteFramePulledVector period hPeriod frame patch second) coordinate) =
      finiteFrameBracketPotentialCoefficient period hPeriod frame potential
        component first second (patch.coordinateMap coordinate) := by
  rw [localGaugeOneForm_apply,
    coordinateMap_mfderiv_lieBracket_finiteFramePulledVector]
  rfl

/-- Cartan curvature in the generating family is the intrinsic exterior derivative. -/
theorem finiteFrameSmoothGaugeCurvatureCoefficient_eq_local
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin frame.count) :
    finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
        component first second (patch.coordinateMap coordinate) =
      localGaugeCurvature period hPeriod potential component patch coordinate
        ![finiteFramePulledVector period hPeriod frame patch first coordinate,
          finiteFramePulledVector period hPeriod frame patch second coordinate] := by
  let oneForm := localGaugeOneForm period hPeriod potential component patch
  let firstPulled := finiteFramePulledVector period hPeriod frame patch first
  let secondPulled := finiteFramePulledVector period hPeriod frame patch second
  have hExterior := extDeriv_oneForm_apply_twoVectorFields
    oneForm firstPulled secondPulled coordinate
    ((localGaugeOneForm_contDiff period hPeriod potential component patch)
      |>.differentiable (by simp) coordinate)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch first)
      |>.differentiable (by simp) coordinate)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch second)
      |>.differentiable (by simp) coordinate)
  rw [localGaugeOneForm_finiteFramePulled_derivative period hPeriod frame potential
      component patch coordinate first second,
    localGaugeOneForm_finiteFramePulled_derivative period hPeriod frame potential
      component patch coordinate second first,
    localGaugeOneForm_lieBracket_finiteFramePulledVector period hPeriod frame potential
      component patch coordinate first second] at hExterior
  change
    frameDerivative period hPeriod Real frame
          (finiteFramePotentialCoefficient period hPeriod frame potential component second)
          (patch.coordinateMap coordinate) first -
        frameDerivative period hPeriod Real frame
          (finiteFramePotentialCoefficient period hPeriod frame potential component first)
          (patch.coordinateMap coordinate) second -
      finiteFrameBracketPotentialCoefficient period hPeriod frame potential
        component first second (patch.coordinateMap coordinate) = _
  simpa only [oneForm, firstPulled, secondPulled, localGaugeCurvature] using
    hExterior.symm

private theorem localGaugeCurvature_redundant_expansion
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (row column : Fin 4) :
    localGaugeCurvatureMatrix period hPeriod potential component patch coordinate
        row column =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate first
              (Pi.single row 1) *
          finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate second
              (Pi.single column 1) *
          finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
            component first second (patch.coordinateMap coordinate) := by
  let curvature := alternatingTwoFormToBilin
    (localGaugeCurvature period hPeriod potential component patch coordinate)
  have hFirst := finiteFramePulledVector_reconstructs period hPeriod frame baseMetric
    patch coordinate (Pi.single row 1)
  have hSecond := finiteFramePulledVector_reconstructs period hPeriod frame baseMetric
    patch coordinate (Pi.single column 1)
  change curvature (Pi.single row 1) (Pi.single column 1) = _
  conv_lhs => rw [hFirst, hSecond]
  simp only [map_smul, LinearMap.sum_apply, map_sum, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameSmoothGaugeCurvatureCoefficient_eq_local period hPeriod frame
    potential component patch coordinate first second]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  have hCurvature :
      curvature
          (finiteFramePulledVector period hPeriod frame patch first coordinate)
          (finiteFramePulledVector period hPeriod frame patch second coordinate) =
        localGaugeCurvature period hPeriod potential component patch coordinate
          ![finiteFramePulledVector period hPeriod frame patch first coordinate,
            finiteFramePulledVector period hPeriod frame patch second coordinate] :=
    alternatingTwoFormToBilin_apply _ _ _
  rw [hCurvature]
  ring

private theorem redundantMaxwellContraction_algebra
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (inverse : κ → κ → Real)
    (coefficient : ι → κ → Real)
    (curvature : ι → ι → Real)
    (coordinateCurvature : κ → κ → Real)
    (hCoordinate : ∀ row column,
      coordinateCurvature row column =
        ∑ first : ι, ∑ second : ι,
          coefficient first row * coefficient second column *
            curvature first second) :
    (∑ first : ι, ∑ second : ι, ∑ raisedFirst : ι, ∑ raisedSecond : ι,
      (∑ row : κ, ∑ raisedRow : κ,
          inverse row raisedRow * coefficient first row *
            coefficient raisedFirst raisedRow) *
        (∑ column : κ, ∑ raisedColumn : κ,
          inverse column raisedColumn * coefficient second column *
            coefficient raisedSecond raisedColumn) *
        curvature first second * curvature raisedFirst raisedSecond) =
      ∑ row : κ, ∑ column : κ, ∑ raisedRow : κ, ∑ raisedColumn : κ,
        inverse row raisedRow * inverse column raisedColumn *
          coordinateCurvature row column *
          coordinateCurvature raisedRow raisedColumn := by
  classical
  let reindex :
      (ι × ι × ι × ι × κ × κ × κ × κ) ≃
        (κ × κ × κ × κ × ι × ι × ι × ι) :=
    { toFun := fun ⟨first, second, raisedFirst, raisedSecond,
          column, raisedColumn, row, raisedRow⟩ =>
        (row, column, raisedRow, raisedColumn,
          raisedFirst, raisedSecond, first, second)
      invFun := fun ⟨row, column, raisedRow, raisedColumn,
          raisedFirst, raisedSecond, first, second⟩ =>
        (first, second, raisedFirst, raisedSecond,
          column, raisedColumn, row, raisedRow)
      left_inv := by
        rintro ⟨first, second, raisedFirst, raisedSecond,
          column, raisedColumn, row, raisedRow⟩
        rfl
      right_inv := by
        rintro ⟨row, column, raisedRow, raisedColumn,
          raisedFirst, raisedSecond, first, second⟩
        rfl }
  let source : (ι × ι × ι × ι × κ × κ × κ × κ) → Real :=
    fun ⟨first, second, raisedFirst, raisedSecond,
        column, raisedColumn, row, raisedRow⟩ =>
      (inverse row raisedRow * coefficient first row *
          coefficient raisedFirst raisedRow) *
        (inverse column raisedColumn * coefficient second column *
          coefficient raisedSecond raisedColumn) *
        curvature first second * curvature raisedFirst raisedSecond
  let target : (κ × κ × κ × κ × ι × ι × ι × ι) → Real :=
    fun ⟨row, column, raisedRow, raisedColumn,
        raisedFirst, raisedSecond, first, second⟩ =>
      inverse row raisedRow * inverse column raisedColumn *
        (coefficient first row * coefficient second column *
          curvature first second) *
        (coefficient raisedFirst raisedRow *
          coefficient raisedSecond raisedColumn *
          curvature raisedFirst raisedSecond)
  have h := Fintype.sum_equiv reindex source target (by
    rintro ⟨first, second, raisedFirst, raisedSecond,
      column, raisedColumn, row, raisedRow⟩
    dsimp [source, target, reindex]
    ring)
  have hNested :
      (∑ first : ι, ∑ second : ι, ∑ raisedFirst : ι, ∑ raisedSecond : ι,
        ∑ column : κ, ∑ raisedColumn : κ, ∑ row : κ, ∑ raisedRow : κ,
          (inverse row raisedRow * coefficient first row *
              coefficient raisedFirst raisedRow) *
            (inverse column raisedColumn * coefficient second column *
              coefficient raisedSecond raisedColumn) *
            curvature first second * curvature raisedFirst raisedSecond) =
        ∑ row : κ, ∑ column : κ, ∑ raisedRow : κ, ∑ raisedColumn : κ,
          ∑ raisedFirst : ι, ∑ raisedSecond : ι, ∑ first : ι, ∑ second : ι,
            inverse row raisedRow * inverse column raisedColumn *
              (coefficient first row * coefficient second column *
                curvature first second) *
              (coefficient raisedFirst raisedRow *
                coefficient raisedSecond raisedColumn *
                curvature raisedFirst raisedSecond) := by
    simpa only [source, target, Fintype.sum_prod_type] using h
  calc
    _ = ∑ first : ι, ∑ second : ι, ∑ raisedFirst : ι, ∑ raisedSecond : ι,
        ∑ column : κ, ∑ raisedColumn : κ, ∑ row : κ, ∑ raisedRow : κ,
          (inverse row raisedRow * coefficient first row *
              coefficient raisedFirst raisedRow) *
            (inverse column raisedColumn * coefficient second column *
              coefficient raisedSecond raisedColumn) *
            curvature first second * curvature raisedFirst raisedSecond := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      apply Finset.sum_congr rfl
      intro raisedFirst _
      apply Finset.sum_congr rfl
      intro raisedSecond _
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = _ := hNested
    _ = _ := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      apply Finset.sum_congr rfl
      intro raisedRow _
      apply Finset.sum_congr rfl
      intro raisedColumn _
      rw [hCoordinate row column, hCoordinate raisedRow raisedColumn]
      symm
      simp only [Finset.sum_mul, Finset.mul_sum]

private theorem finiteFrameSmoothMaxwellPairing_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    finiteFrameSmoothMaxwellPairing period hPeriod frame baseMetric metric potential
        (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod metric potential potential patch coordinate := by
  classical
  simp only [finiteFrameSmoothMaxwellPairing, smoothScalarSum_apply,
    smoothScalarFieldMul_apply]
  simp_rw [← finiteFrameLocalInverseMetricCoefficientAt_eq_global
    period hPeriod frame baseMetric metric patch coordinate]
  simp only [finiteFrameLocalInverseMetricCoefficientAt, localMaxwellPairing]
  apply Finset.sum_congr rfl
  intro component _
  simpa only [mul_assoc] using redundantMaxwellContraction_algebra
    (ι := Fin frame.count) (κ := Fin 4)
    (fun row raisedRow =>
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ row raisedRow)
    (fun index row => finiteFrameLocalCoefficientAt period hPeriod frame baseMetric
      patch coordinate index (Pi.single row 1))
    (fun first second => finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod
      frame potential component first second (patch.coordinateMap coordinate))
    (localGaugeCurvatureMatrix period hPeriod potential component patch coordinate)
    (localGaugeCurvature_redundant_expansion period hPeriod frame baseMetric
      potential component patch coordinate)

/-- The redundant finite-frame Maxwell contraction is the intrinsic global scalar. -/
theorem finiteFrameSmoothMaxwellPairing_eq_global
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameSmoothMaxwellPairing period hPeriod frame baseMetric metric potential =
      globalSmoothMaxwellPairing period hPeriod metric potential potential := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  change finiteFrameSmoothMaxwellPairing period hPeriod frame baseMetric metric potential
      (patch.coordinateMap coordinate) =
    globalMaxwellPairing period hPeriod metric potential potential
      (patch.coordinateMap coordinate)
  rw [finiteFrameSmoothMaxwellPairing_eq_local period hPeriod frame baseMetric,
    globalMaxwellPairing_eq_local]

/-- Completed smooth inputs recover the intrinsic global Maxwell scalar. -/
theorem finiteFrameMaxwellPairingC0_smooth_intrinsic
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
        generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothMaxwellPairing period hPeriod metric potential potential) := by
  calc
    _ = smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothMaxwellPairing period hPeriod frame baseMetric metric potential) :=
      finiteFrameMaxwellPairingC0_smooth period hPeriod frame baseMetric variation metric
        hMetric hVariation potential
    _ = _ := congrArg (smoothToCanonicalPhysicalContinuousScalar period hPeriod)
      (finiteFrameSmoothMaxwellPairing_eq_global period hPeriod frame baseMetric metric potential)

end
end P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D
end JanusFormal
