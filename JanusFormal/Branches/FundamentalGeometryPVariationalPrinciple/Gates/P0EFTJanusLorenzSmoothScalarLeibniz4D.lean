import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D

/-!
# Smooth scalar Leibniz rule for the actual Lorenz operator

Multiplication of an intrinsic potential by a smooth scalar is constructed on
the tangent bundle. The local product rule descends to the actual global
operator, with principal term `df (inverseMetricSharp A)`.
-/

namespace JanusFormal
namespace P0EFTJanusLorenzSmoothScalarLeibniz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise multiplication of a genuine smooth one-form by a smooth scalar. -/
def smoothScalarMulGaugePotential
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod where
  toFun := fun component point => field point • potential.toFun component point
  contMDiff_eval := fun component => by
    have hProjection :
        ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
          (fun vector : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) => vector.1) :=
      Bundle.contMDiff_proj
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
    exact (field.contMDiff_toFun.comp hProjection).smul
      (potential.contMDiff_eval component)

@[simp]
theorem smoothScalarMulGaugePotential_apply
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod)
    (tangent : TangentSpace coverModelWithCorners point) :
    (smoothScalarMulGaugePotential period hPeriod field potential).toFun
        component point tangent =
      field point * potential.toFun component point tangent := rfl

theorem localRaisedAbelianGaugePotential_smoothScalarMul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper : Index4) :
    localRaisedAbelianGaugePotential period hPeriod metric
        (smoothScalarMulGaugePotential period hPeriod field potential)
        component patch coordinate upper =
      localScalarRepresentative period hPeriod field patch coordinate *
        localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate upper := by
  simp only [localRaisedAbelianGaugePotential, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  unfold localGaugeCoefficient
  rw [smoothScalarMulGaugePotential_apply]
  change _ = field (patch.coordinateMap coordinate) * _
  ring

/-- The ordinary product rule gives the first-order coefficient formula. -/
theorem localAbelianLorenzDivergence_smoothScalarMul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric
        (smoothScalarMulGaugePotential period hPeriod field potential)
        component patch coordinate =
      field (patch.coordinateMap coordinate) *
          localAbelianLorenzDivergence period hPeriod metric potential component
            patch coordinate +
        ∑ index : Index4,
          fderiv Real (localScalarRepresentative period hPeriod field patch)
              coordinate (Pi.single index 1) *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate index := by
  have hField := (localScalarRepresentative_contDiff period hPeriod field patch)
    |>.differentiable (by simp) coordinate
  have hDerivative (index : Index4) :
      fderiv Real
          (fun current => localRaisedAbelianGaugePotential period hPeriod metric
            (smoothScalarMulGaugePotential period hPeriod field potential)
            component patch current index) coordinate =
        localScalarRepresentative period hPeriod field patch coordinate •
            fderiv Real (fun current =>
              localRaisedAbelianGaugePotential period hPeriod metric potential
                component patch current index) coordinate +
          localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate index •
            fderiv Real (localScalarRepresentative period hPeriod field patch)
              coordinate := by
    simp_rw [localRaisedAbelianGaugePotential_smoothScalarMul]
    exact fderiv_fun_mul hField
      ((localRaisedAbelianGaugePotential_component_contDiff period hPeriod metric
        potential component patch index).differentiable (by simp) coordinate)
  unfold localAbelianLorenzDivergence
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [hDerivative derivative]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  simp_rw [localRaisedAbelianGaugePotential_smoothScalarMul]
  have hConnection :
      (∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          (localScalarRepresentative period hPeriod field patch coordinate *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate lower)) =
        field (patch.coordinateMap coordinate) *
          ∑ lower : Index4,
            localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
              localRaisedAbelianGaugePotential period hPeriod metric potential
                component patch coordinate lower := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    unfold localScalarRepresentative
    ring
  rw [hConnection]
  unfold localScalarRepresentative
  ring

/-- The local principal term is exactly the intrinsic differential on `A♯`. -/
theorem scalarDifferential_inverseMetricSharp_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
        (inverseMetricSharp period hPeriod metric (patch.coordinateMap coordinate)
          (potential.toFun component (patch.coordinateMap coordinate))) =
      ∑ index : Index4,
        fderiv Real (localScalarRepresentative period hPeriod field patch)
            coordinate (Pi.single index 1) *
          localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch coordinate index := by
  let direction := localRaisedAbelianGaugePotential period hPeriod metric potential
    component patch coordinate
  have hChain := mfderiv_comp_apply coordinate
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp)) direction
  have hChainReal := congrArg
    (NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate)))
    hChain
  have hLeft :
      fderiv Real (localScalarRepresentative period hPeriod field patch)
          coordinate direction =
        NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate))
          (mfderiv (modelWithCornersSelf Real Vector4) 𝓘(Real, Real)
            (field.toFun ∘ patch.coordinateMap) coordinate direction) := by
    change fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate direction = _
    rw [mfderiv_eq_fderiv]
    rfl
  have hRight :
      NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate))
          (mfderiv coverModelWithCorners 𝓘(Real, Real) field.toFun
            (patch.coordinateMap coordinate)
            (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
              patch.coordinateMap coordinate direction)) =
        scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
          (inverseMetricSharp period hPeriod metric (patch.coordinateMap coordinate)
            (potential.toFun component (patch.coordinateMap coordinate))) := by
    dsimp only [direction]
    rw [coordinateMap_mfderiv_localRaisedAbelianGaugePotential]
    rfl
  rw [← hLeft.trans (hChainReal.trans hRight)]
  have hExpansion : direction =
      ∑ index : Index4, direction index • Pi.single index (1 : Real) := by
    ext index
    simp [Pi.single_apply]
  calc
    fderiv Real (localScalarRepresentative period hPeriod field patch)
        coordinate direction =
      fderiv Real (localScalarRepresentative period hPeriod field patch)
        coordinate (∑ index : Index4,
          direction index • Pi.single index (1 : Real)) :=
      congrArg _ hExpansion
    _ = _ := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro index _
      exact mul_comm _ _

/-- Actual global Leibniz formula; neither the differential nor its coefficient
formula is supplied as a hypothesis. -/
theorem globalGeneralMetricAbelianLorenzCodifferential_smoothScalarMul_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) (component : Fin 2) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
        (smoothScalarMulGaugePotential period hPeriod field potential)
        point component =
      field point *
          globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
            potential point component +
        scalarDifferential period hPeriod field point
          (inverseMetricSharp period hPeriod metric point
            (potential.toFun component point)) := by
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  simp only [globalGeneralMetricAbelianLorenzCodifferential_apply,
    globalGeneralMetricAbelianLorenzValue_eq_local]
  rw [scalarDifferential_inverseMetricSharp_eq_local]
  exact localAbelianLorenzDivergence_smoothScalarMul period hPeriod metric field
    potential component witness.patch witness.coordinate

end
end P0EFTJanusLorenzSmoothScalarLeibniz4D
end JanusFormal
