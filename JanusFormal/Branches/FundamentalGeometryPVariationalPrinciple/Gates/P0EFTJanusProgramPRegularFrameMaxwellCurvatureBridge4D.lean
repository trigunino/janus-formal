import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

/-!
# Cartan-to-holonomic Maxwell curvature bridge

The regular-frame Cartan coefficients are identified with the already
implemented chartwise exterior derivative `dA`.  The proof pulls the global
frame through a genuine holonomic local diffeomorphism, applies the standard
exterior-derivative/Lie-bracket formula, and pushes the result back.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem smoothness_two_le_infty :
    minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- Pull one global regular-frame vector back to holonomic coordinates. -/
def pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Fin 4) : Vector4 → Vector4 :=
  VectorField.mpullback
    (modelWithCornersSelf Real Vector4) coverModelWithCorners
    patch.coordinateMap (metric.frame index)

private theorem coordinateMap_mfderiv_isInvertible
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate).IsInvertible := by
  let equivalence :=
    patch.coordinateMap_isLocalDiffeomorph
      |>.mfderivToContinuousLinearEquiv (by simp) coordinate
  exact ⟨equivalence, rfl⟩

theorem coordinateMap_mfderiv_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin 4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (pulledRegularFrameVector period hPeriod metric patch index
          coordinate) =
      metric.frame index (patch.coordinateMap coordinate) := by
  rw [pulledRegularFrameVector, VectorField.mpullback_apply]
  exact (coordinateMap_mfderiv_isInvertible period hPeriod patch coordinate)
    |>.self_apply_inverse _

theorem pulledRegularFrameVector_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin 4) :
    DifferentiableAt Real
      (pulledRegularFrameVector period hPeriod metric patch index)
      coordinate := by
  apply MDifferentiableAt.differentiableAt
  have hBundle := (metric.frame index).contMDiff.mdifferentiableAt (by simp)
    |>.mpullback_vectorField
      patch.coordinateMap_contMDiff.contMDiffAt
      (coordinateMap_mfderiv_isInvertible period hPeriod patch coordinate)
      (show (2 : ℕ∞ω) ≤ ∞ by
        exact WithTop.coe_le_coe.mpr le_top)
  exact (contMDiff_snd_tangentBundle_modelSpace Vector4
      (modelWithCornersSelf Real Vector4)).contMDiffAt
    |>.mdifferentiableAt one_ne_zero
    |>.comp coordinate hBundle

/-- The pulled regular-frame vectors are smooth coordinate vector fields.
This strengthens the pointwise differentiability interface used by the
Maxwell bridge and supplies the second derivatives needed by curvature. -/
theorem pulledRegularFrameVector_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Fin 4) :
    ContDiff Real ∞
      (pulledRegularFrameVector period hPeriod metric patch index) := by
  have hBundle := (metric.frame index).contMDiff.mpullback_vectorField
    patch.coordinateMap_contMDiff
    (fun coordinate =>
      coordinateMap_mfderiv_isInvertible period hPeriod patch coordinate)
    (by simp)
  exact ((contMDiff_snd_tangentBundle_modelSpace Vector4
    (modelWithCornersSelf Real Vector4)).comp hBundle).contDiff

theorem localGaugeOneForm_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin 4) :
    localGaugeOneForm period hPeriod potential component patch coordinate
        (fun _ => pulledRegularFrameVector period hPeriod metric patch index
          coordinate) =
      regularFramePotentialCoefficient period hPeriod metric potential
        component index (patch.coordinateMap coordinate) := by
  rw [localGaugeOneForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector]
  rfl

theorem fderiv_comp_coordinateMap_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction : Fin 4) :
    fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameVector period hPeriod metric patch direction
          coordinate) =
      frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
        field (patch.coordinateMap coordinate) direction := by
  let vector := pulledRegularFrameVector period hPeriod metric patch direction
    coordinate
  have hChain := mfderiv_comp_apply coordinate
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp)) vector
  have hChainReal := congrArg
    (NormedSpace.fromTangentSpace
      (field.toFun (patch.coordinateMap coordinate))) hChain
  have hLeft :
      fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate vector =
        NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv (modelWithCornersSelf Real Vector4)
            (modelWithCornersSelf Real Real)
            (field.toFun ∘ patch.coordinateMap)
            coordinate vector) := by
    rw [mfderiv_eq_fderiv]
    rfl
  have hRight :
      NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv coverModelWithCorners
            (modelWithCornersSelf Real Real) field.toFun
            (patch.coordinateMap coordinate)
            (mfderiv (modelWithCornersSelf Real Vector4)
              coverModelWithCorners patch.coordinateMap coordinate vector)) =
        frameDerivative period hPeriod Real
          (RegularFrame period hPeriod metric) field
          (patch.coordinateMap coordinate) direction := by
    rw [coordinateMap_mfderiv_pulledRegularFrameVector]
    rw [frameDerivative_eq_mfderiv]
    rfl
  exact hLeft.trans (hChainReal.trans hRight)

private theorem localGaugeOneForm_pulled_derivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction index : Fin 4) :
    fderiv Real
        (fun current =>
          localGaugeOneForm period hPeriod potential component patch current
            (fun _ => pulledRegularFrameVector period hPeriod metric patch
              index current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch direction
          coordinate) =
      regularFramePotentialDerivative period hPeriod metric potential
        component direction index (patch.coordinateMap coordinate) := by
  have hFunction :
      (fun current =>
        localGaugeOneForm period hPeriod potential component patch current
          (fun _ => pulledRegularFrameVector period hPeriod metric patch
            index current)) =
        (regularFramePotentialCoefficient period hPeriod metric potential
          component index).toFun ∘ patch.coordinateMap := by
    funext current
    exact localGaugeOneForm_pulledRegularFrameVector period hPeriod metric
      potential component patch current index
  rw [hFunction]
  exact fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
    metric
    (regularFramePotentialCoefficient period hPeriod metric potential
      component index)
    patch coordinate direction

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

theorem coordinateMap_mfderiv_lieBracket_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin 4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (VectorField.lieBracket (E := Vector4) Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second)
          coordinate) =
      smoothGhostLieBracket period hPeriod
        (metric.frame first) (metric.frame second)
        (patch.coordinateMap coordinate) := by
  let firstField := metric.frame first
  let secondField := metric.frame second
  let firstPulled :=
    pulledRegularFrameVector period hPeriod metric patch first
  let secondPulled :=
    pulledRegularFrameVector period hPeriod metric patch second
  have hNatural := VectorField.mpullback_mlieBracket
    (x₀ := coordinate)
    (f := patch.coordinateMap)
    (V := fun point => firstField point)
    (W := fun point => secondField point)
    (firstField.contMDiff.mdifferentiableAt (by simp))
    (secondField.contMDiff.mdifferentiableAt (by simp))
    patch.coordinateMap_contMDiff.contMDiffAt
    smoothness_two_le_infty
  have hEuclidean :
      VectorField.mlieBracket (modelWithCornersSelf Real Vector4)
          firstPulled secondPulled coordinate =
        VectorField.lieBracket (E := Vector4) Real firstPulled secondPulled
          coordinate := by
    rw [← VectorField.mlieBracketWithin_univ]
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [VectorField.lieBracketWithin_univ]
  have hApplied := congrArg
    (fun vector : Vector4 =>
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate vector)
    hNatural
  rw [VectorField.mpullback_apply,
    (coordinateMap_mfderiv_isInvertible period hPeriod patch coordinate)
      |>.self_apply_inverse] at hApplied
  dsimp [firstField, secondField] at hApplied
  dsimp [firstPulled, secondPulled, pulledRegularFrameVector] at hEuclidean
  rw [hEuclidean] at hApplied
  simpa only [firstField, secondField, firstPulled, secondPulled,
    pulledRegularFrameVector, smoothGhostLieBracket_apply] using
    hApplied.symm

private theorem localGaugeOneForm_lieBracket_pulledRegularFrameVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin 4) :
    localGaugeOneForm period hPeriod potential component patch coordinate
        (fun _ =>
          VectorField.lieBracket (E := Vector4) Real
            (pulledRegularFrameVector period hPeriod metric patch first)
            (pulledRegularFrameVector period hPeriod metric patch second)
            coordinate) =
      regularFrameBracketPotentialCoefficient period hPeriod metric potential
        component first second (patch.coordinateMap coordinate) := by
  rw [localGaugeOneForm_apply,
    coordinateMap_mfderiv_lieBracket_pulledRegularFrameVector]
  rfl

/-- The regular-frame Cartan coefficient is exactly the already implemented
chartwise exterior derivative `dA` evaluated on the pulled frame vectors. -/
theorem regularFrameGaugeCurvatureCoefficient_eq_localGaugeCurvature
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin 4) :
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second (patch.coordinateMap coordinate) =
      localGaugeCurvature period hPeriod potential component patch coordinate
        ![pulledRegularFrameVector period hPeriod metric patch first coordinate,
          pulledRegularFrameVector period hPeriod metric patch second
            coordinate] := by
  let oneForm :=
    localGaugeOneForm period hPeriod potential component patch
  let firstPulled :=
    pulledRegularFrameVector period hPeriod metric patch first
  let secondPulled :=
    pulledRegularFrameVector period hPeriod metric patch second
  have hExterior := extDeriv_oneForm_apply_twoVectorFields
    oneForm firstPulled secondPulled coordinate
    ((localGaugeOneForm_contDiff period hPeriod potential component patch)
      |>.differentiable (by simp) coordinate)
    (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate first)
    (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate second)
  rw [localGaugeOneForm_pulled_derivative period hPeriod metric potential
      component patch coordinate first second,
    localGaugeOneForm_pulled_derivative period hPeriod metric potential
      component patch coordinate second first,
    localGaugeOneForm_lieBracket_pulledRegularFrameVector period hPeriod
      metric potential component patch coordinate first second] at hExterior
  change
    regularFramePotentialDerivative period hPeriod metric potential
          component first second (patch.coordinateMap coordinate) -
        regularFramePotentialDerivative period hPeriod metric potential
          component second first (patch.coordinateMap coordinate) -
      regularFrameBracketPotentialCoefficient period hPeriod metric potential
        component first second (patch.coordinateMap coordinate) = _
  simpa only [oneForm, firstPulled, secondPulled, localGaugeCurvature] using
    hExterior.symm

/-- Tensorial compatibility gate: every component and every regular-frame
pair agrees with the genuine local curvature `dA` in every holonomic chart. -/
theorem regular_frame_maxwell_curvature_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4) (first second : Fin 4),
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first second (patch.coordinateMap coordinate) =
        localGaugeCurvature period hPeriod potential component patch coordinate
          ![pulledRegularFrameVector period hPeriod metric patch first
              coordinate,
            pulledRegularFrameVector period hPeriod metric patch second
              coordinate] :=
  regularFrameGaugeCurvatureCoefficient_eq_localGaugeCurvature
    period hPeriod metric potential

end

end P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
end JanusFormal
