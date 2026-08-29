import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarWave4D

/-!
# Global smooth scalar products on the canonical Lorentz quotient

This gate supplies the pointwise product missing from the smooth scalar-field
linear space and proves its local value and gradient Leibniz laws.  The
covariant-Hessian and wave product rules remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev ScalarIndex4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise multiplication of two global smooth scalar fields. -/
def smoothScalarFieldMul
    (first second : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point => first point * second point
  contMDiff_toFun := first.contMDiff_toFun.mul second.contMDiff_toFun

@[simp]
theorem smoothScalarFieldMul_apply
    (first second : SmoothScalarField period hPeriod)
    (point) :
    smoothScalarFieldMul period hPeriod first second point =
      first point * second point :=
  rfl

@[simp]
theorem smoothScalarFieldAdd_apply
    (first second : SmoothScalarField period hPeriod)
    (point) :
    (first + second) point = first point + second point :=
  rfl

@[simp]
theorem smoothScalarFieldSub_apply
    (first second : SmoothScalarField period hPeriod)
    (point) :
    (first - second) point = first point - second point :=
  rfl

@[simp]
theorem smoothScalarFieldSmul_toFun
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (point) :
    (scalar • field).toFun point = scalar * field.toFun point :=
  rfl

@[simp]
theorem smoothScalarFieldSub_toFun
    (first second : SmoothScalarField period hPeriod)
    (point) :
    (first - second).toFun point =
      first.toFun point - second.toFun point :=
  rfl

theorem localScalarRepresentative_mul
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarRepresentative period hPeriod
        (smoothScalarFieldMul period hPeriod first second) patch coordinate =
      localScalarRepresentative period hPeriod first patch coordinate *
        localScalarRepresentative period hPeriod second patch coordinate :=
  rfl

theorem localScalarGradient_mul
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarGradient period hPeriod
        (smoothScalarFieldMul period hPeriod first second) patch coordinate =
      fun index =>
        localScalarGradient period hPeriod first patch coordinate index *
            localScalarRepresentative period hPeriod second patch coordinate +
          localScalarRepresentative period hPeriod first patch coordinate *
            localScalarGradient period hPeriod second patch coordinate index := by
  funext index
  unfold localScalarGradient
  rw [show
      localScalarRepresentative period hPeriod
          (smoothScalarFieldMul period hPeriod first second) patch =
        localScalarRepresentative period hPeriod first patch *
          localScalarRepresentative period hPeriod second patch by rfl]
  have hFirst : DifferentiableAt Real
      (localScalarRepresentative period hPeriod first patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod first patch)
      |>.differentiable (by simp)).differentiableAt
  have hSecond : DifferentiableAt Real
      (localScalarRepresentative period hPeriod second patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod second patch)
      |>.differentiable (by simp)).differentiableAt
  rw [fderiv_mul hFirst hSecond]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem fderiv_localScalarRepresentative_mul
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    fderiv Real
        (localScalarRepresentative period hPeriod
          (smoothScalarFieldMul period hPeriod first second) patch) =
      fun coordinate =>
        localScalarRepresentative period hPeriod first patch coordinate •
            fderiv Real
              (localScalarRepresentative period hPeriod second patch) coordinate +
          localScalarRepresentative period hPeriod second patch coordinate •
            fderiv Real
              (localScalarRepresentative period hPeriod first patch) coordinate := by
  funext coordinate
  change fderiv Real
      (localScalarRepresentative period hPeriod first patch *
        localScalarRepresentative period hPeriod second patch) coordinate = _
  rw [fderiv_mul
    (((localScalarRepresentative_contDiff period hPeriod first patch)
      |>.differentiable (by simp)).differentiableAt)
    (((localScalarRepresentative_contDiff period hPeriod second patch)
      |>.differentiable (by simp)).differentiableAt)]

theorem localScalarPartialGradient_mul
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarPartialGradient period hPeriod
        (smoothScalarFieldMul period hPeriod first second) patch coordinate =
      fun firstIndex secondIndex =>
        localScalarPartialGradient period hPeriod first patch coordinate
            firstIndex secondIndex *
            localScalarRepresentative period hPeriod second patch coordinate +
          localScalarGradient period hPeriod first patch coordinate firstIndex *
            localScalarGradient period hPeriod second patch coordinate secondIndex +
          localScalarGradient period hPeriod first patch coordinate secondIndex *
            localScalarGradient period hPeriod second patch coordinate firstIndex +
          localScalarRepresentative period hPeriod first patch coordinate *
            localScalarPartialGradient period hPeriod second patch coordinate
              firstIndex secondIndex := by
  ext firstIndex secondIndex
  unfold localScalarPartialGradient localScalarGradient
  rw [fderiv_localScalarRepresentative_mul]
  have hFirst : DifferentiableAt Real
      (localScalarRepresentative period hPeriod first patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod first patch)
      |>.differentiable (by simp)).differentiableAt
  have hSecond : DifferentiableAt Real
      (localScalarRepresentative period hPeriod second patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod second patch)
      |>.differentiable (by simp)).differentiableAt
  have hFirstDerivative : DifferentiableAt Real
      (fderiv Real
        (localScalarRepresentative period hPeriod first patch)) coordinate :=
    (((localScalarRepresentative_contDiff period hPeriod first patch)
      |>.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hSecondDerivative : DifferentiableAt Real
      (fderiv Real
        (localScalarRepresentative period hPeriod second patch)) coordinate :=
    (((localScalarRepresentative_contDiff period hPeriod second patch)
      |>.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  let firstDirection : Vector4 := Pi.single firstIndex 1
  let secondDirection : Vector4 := Pi.single secondIndex 1
  change
    ((fderiv Real
      (localScalarRepresentative period hPeriod first patch •
          fderiv Real
            (localScalarRepresentative period hPeriod second patch) +
        localScalarRepresentative period hPeriod second patch •
          fderiv Real
            (localScalarRepresentative period hPeriod first patch))
      coordinate) firstDirection) secondDirection = _
  have hAdd := fderiv_add
    (hFirst.smul hSecondDerivative)
    (hSecond.smul hFirstDerivative)
  have hAddEval := congrArg
    (fun derivative =>
      derivative firstDirection secondDirection) hAdd
  rw [hAddEval]
  simp only [add_apply]
  have hLeft := fderiv_smul hFirst hSecondDerivative
  have hLeftEval := congrArg
    (fun derivative =>
      derivative firstDirection secondDirection) hLeft
  rw [hLeftEval]
  have hRight := fderiv_smul hSecond hFirstDerivative
  have hRightEval := congrArg
    (fun derivative =>
      derivative firstDirection secondDirection) hRight
  rw [hRightEval]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  change _ =
    ((fderiv Real
          (fderiv Real
            (localScalarRepresentative period hPeriod first patch)) coordinate)
        firstDirection) secondDirection *
          localScalarRepresentative period hPeriod second patch coordinate +
      (fderiv Real
          (localScalarRepresentative period hPeriod first patch) coordinate)
          firstDirection *
        (fderiv Real
          (localScalarRepresentative period hPeriod second patch) coordinate)
          secondDirection +
      (fderiv Real
          (localScalarRepresentative period hPeriod first patch) coordinate)
          secondDirection *
        (fderiv Real
          (localScalarRepresentative period hPeriod second patch) coordinate)
          firstDirection +
      localScalarRepresentative period hPeriod first patch coordinate *
        ((fderiv Real
            (fderiv Real
              (localScalarRepresentative period hPeriod second patch)) coordinate)
          firstDirection) secondDirection
  ring

/-! ## Algebraic covariant product jet -/

def covariantScalarJetProduct
    (first second : CovariantScalarJet2) :
    CovariantScalarJet2 where
  field := first.field * second.field
  gradient := fun index =>
    first.gradient index * second.field +
      first.field * second.gradient index
  hessian := fun firstIndex secondIndex =>
    first.hessian firstIndex secondIndex * second.field +
      first.gradient firstIndex * second.gradient secondIndex +
      first.gradient secondIndex * second.gradient firstIndex +
      first.field * second.hessian firstIndex secondIndex
  hessian_symmetric := by
    ext firstIndex secondIndex
    have hFirst := congrArg
      (fun matrix => matrix firstIndex secondIndex)
      first.hessian_symmetric
    have hSecond := congrArg
      (fun matrix => matrix firstIndex secondIndex)
      second.hessian_symmetric
    simp only [Matrix.transpose_apply] at hFirst hSecond ⊢
    rw [hFirst, hSecond]
    ring

def covariantScalarGradientPairing
    (data : FixedSignMetric4)
    (first second : CovariantScalarJet2) : Real :=
  ∑ firstIndex : ScalarIndex4, ∑ secondIndex : ScalarIndex4,
    data.metric⁻¹ firstIndex secondIndex *
      first.gradient firstIndex * second.gradient secondIndex

private theorem covariantScalarJet2_ext
    (first second : CovariantScalarJet2)
    (hField : first.field = second.field)
    (hGradient : first.gradient = second.gradient)
    (hHessian : first.hessian = second.hessian) :
    first = second := by
  cases first
  cases second
  simp_all

theorem covariantScalarGradientPairing_symmetric
    (data : FixedSignMetric4)
    (first second : CovariantScalarJet2) :
    covariantScalarGradientPairing data first second =
      covariantScalarGradientPairing data second first := by
  unfold covariantScalarGradientPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  have hMetric := congrArg
    (fun matrix => matrix firstIndex secondIndex)
    data.inverse_symmetric
  simp only [Matrix.transpose_apply] at hMetric
  rw [hMetric]
  ring

theorem covariantScalarJetWave_product
    (data : FixedSignMetric4)
    (first second : CovariantScalarJet2) :
    covariantScalarJetWave data
        (covariantScalarJetProduct first second) =
      first.field * covariantScalarJetWave data second +
        second.field * covariantScalarJetWave data first +
        2 * covariantScalarGradientPairing data first second := by
  have hFirstHessian :
      (∑ firstIndex, ∑ secondIndex,
          data.metric⁻¹ firstIndex secondIndex *
            (first.hessian firstIndex secondIndex * second.field)) =
        second.field * covariantScalarJetWave data first := by
    unfold covariantScalarJetWave
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro firstIndex _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro secondIndex _
    ring
  have hSecondHessian :
      (∑ firstIndex, ∑ secondIndex,
          data.metric⁻¹ firstIndex secondIndex *
            (first.field * second.hessian firstIndex secondIndex)) =
        first.field * covariantScalarJetWave data second := by
    unfold covariantScalarJetWave
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro firstIndex _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro secondIndex _
    ring
  have hCross :
      (∑ firstIndex, ∑ secondIndex,
          data.metric⁻¹ firstIndex secondIndex *
            (first.gradient firstIndex * second.gradient secondIndex)) =
        covariantScalarGradientPairing data first second :=
    by
      unfold covariantScalarGradientPairing
      apply Finset.sum_congr rfl
      intro firstIndex _
      apply Finset.sum_congr rfl
      intro secondIndex _
      ring
  have hCrossSwap :
      (∑ firstIndex, ∑ secondIndex,
          data.metric⁻¹ firstIndex secondIndex *
            (first.gradient secondIndex * second.gradient firstIndex)) =
        covariantScalarGradientPairing data second first := by
    unfold covariantScalarGradientPairing
    apply Finset.sum_congr rfl
    intro firstIndex _
    apply Finset.sum_congr rfl
    intro secondIndex _
    ring
  calc
    covariantScalarJetWave data
        (covariantScalarJetProduct first second) =
      first.field * covariantScalarJetWave data second +
        second.field * covariantScalarJetWave data first +
        covariantScalarGradientPairing data first second +
        covariantScalarGradientPairing data second first := by
          unfold covariantScalarJetWave covariantScalarJetProduct
          dsimp only
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [hFirstHessian, hSecondHessian, hCross, hCrossSwap]
          change
            second.field * covariantScalarJetWave data first +
                  covariantScalarGradientPairing data first second +
                covariantScalarGradientPairing data second first +
              first.field * covariantScalarJetWave data second =
              first.field * covariantScalarJetWave data second +
                  second.field * covariantScalarJetWave data first +
                covariantScalarGradientPairing data first second +
              covariantScalarGradientPairing data second first
          ring
    _ = _ := by
      rw [← covariantScalarGradientPairing_symmetric data first second]
      ring

theorem localCovariantScalarJet_mul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localCovariantScalarJet period hPeriod metric patch
        (smoothScalarFieldMul period hPeriod first second) coordinate =
      covariantScalarJetProduct
        (localCovariantScalarJet period hPeriod metric patch first coordinate)
        (localCovariantScalarJet period hPeriod metric patch second coordinate) := by
  apply covariantScalarJet2_ext
  · rfl
  · exact localScalarGradient_mul period hPeriod first second patch coordinate
  · funext firstIndex secondIndex
    change
      localScalarPartialGradient period hPeriod
            (smoothScalarFieldMul period hPeriod first second) patch coordinate
            firstIndex secondIndex -
          ∑ upper,
            (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
                upper firstIndex secondIndex *
              localScalarGradient period hPeriod
                (smoothScalarFieldMul period hPeriod first second) patch coordinate upper =
        (localScalarPartialGradient period hPeriod first patch coordinate
              firstIndex secondIndex -
            ∑ upper,
              (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
                  upper firstIndex secondIndex *
                localScalarGradient period hPeriod first patch coordinate upper) *
            localScalarRepresentative period hPeriod second patch coordinate +
          localScalarGradient period hPeriod first patch coordinate firstIndex *
            localScalarGradient period hPeriod second patch coordinate secondIndex +
          localScalarGradient period hPeriod first patch coordinate secondIndex *
            localScalarGradient period hPeriod second patch coordinate firstIndex +
          localScalarRepresentative period hPeriod first patch coordinate *
            (localScalarPartialGradient period hPeriod second patch coordinate
                firstIndex secondIndex -
              ∑ upper,
                (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
                    upper firstIndex secondIndex *
                  localScalarGradient period hPeriod second patch coordinate upper)
    rw [localScalarPartialGradient_mul,
      localScalarGradient_mul]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [sub_mul, mul_sub, Finset.mul_sum]
    rw [Finset.sum_mul]
    ring

theorem localCovariantScalarWave_mul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (smoothScalarFieldMul period hPeriod first second) coordinate) =
      (localCovariantScalarJet period hPeriod metric patch first coordinate).field *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch second coordinate) +
        (localCovariantScalarJet period hPeriod metric patch second coordinate).field *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch first coordinate) +
        2 * covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch first coordinate)
          (localCovariantScalarJet period hPeriod metric patch second coordinate) := by
  rw [localCovariantScalarJet_mul]
  exact covariantScalarJetWave_product _ _ _

def canonicalGlobalScalarGradientPairing
    (first second : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    (2 : Real)⁻¹ *
      (canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod first second) point -
        first point *
          canonicalGlobalSmoothScalarWave period hPeriod second point -
        second point *
          canonicalGlobalSmoothScalarWave period hPeriod first point)
  contMDiff_toFun :=
    contMDiff_const.mul
      (((canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod first second)).contMDiff_toFun.sub
        (first.contMDiff_toFun.mul
          (canonicalGlobalSmoothScalarWave period hPeriod second).contMDiff_toFun)).sub
        (second.contMDiff_toFun.mul
          (canonicalGlobalSmoothScalarWave period hPeriod first).contMDiff_toFun))

theorem canonicalGlobalSmoothScalarWave_mul
    (first second : SmoothScalarField period hPeriod)
    (point) :
    canonicalGlobalSmoothScalarWave period hPeriod
        (smoothScalarFieldMul period hPeriod first second) point =
      first point * canonicalGlobalSmoothScalarWave period hPeriod second point +
        second point * canonicalGlobalSmoothScalarWave period hPeriod first point +
        2 * canonicalGlobalScalarGradientPairing
          period hPeriod first second point := by
  unfold canonicalGlobalScalarGradientPairing
  change _ = _ + _ + 2 * ((2 : Real)⁻¹ * (_ - _ - _))
  ring

theorem canonicalGlobalScalarGradientPairing_eq_local
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalGlobalScalarGradientPairing period hPeriod first second
        (patch.coordinateMap coordinate) =
      covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch second coordinate) := by
  unfold canonicalGlobalScalarGradientPairing
  change (2 : Real)⁻¹ *
    (canonicalGlobalSmoothScalarWave period hPeriod
        (smoothScalarFieldMul period hPeriod first second)
          (patch.coordinateMap coordinate) -
      first (patch.coordinateMap coordinate) *
        canonicalGlobalSmoothScalarWave period hPeriod second
          (patch.coordinateMap coordinate) -
      second (patch.coordinateMap coordinate) *
        canonicalGlobalSmoothScalarWave period hPeriod first
          (patch.coordinateMap coordinate)) = _
  rw [canonicalGlobalSmoothScalarWave_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local]
  unfold canonicalPhysicalScalarWaveAtlasRepresentative
  rw [localCovariantScalarWave_mul]
  have hFirstValue :
      first (patch.coordinateMap coordinate) =
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first coordinate).field :=
    rfl
  have hSecondValue :
      second (patch.coordinateMap coordinate) =
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch second coordinate).field :=
    rfl
  rw [hFirstValue, hSecondValue]
  ring

theorem canonicalGlobalScalarGradientPairing_symmetric
    (first second : SmoothScalarField period hPeriod)
    (point) :
    canonicalGlobalScalarGradientPairing period hPeriod first second point =
      canonicalGlobalScalarGradientPairing period hPeriod second first point := by
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [canonicalGlobalScalarGradientPairing_eq_local,
    canonicalGlobalScalarGradientPairing_eq_local]
  exact covariantScalarGradientPairing_symmetric _ _ _

end

end P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
end JanusFormal
