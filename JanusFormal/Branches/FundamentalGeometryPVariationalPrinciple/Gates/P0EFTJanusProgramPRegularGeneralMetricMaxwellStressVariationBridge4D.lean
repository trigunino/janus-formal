import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

/-! # Maxwell stress tensor identified with the metric variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricMaxwellStressVariationBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Covariant quadratic Maxwell coefficient at one frame point. -/
def maxwellCovariantQuadraticAt
    (inverse : Matrix4) (curvature : Fin 2 → Matrix4) : Matrix4 :=
  fun first second =>
    ∑ component : Fin 2, ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
      curvature component first lowerFirst *
        inverse lowerFirst lowerSecond *
        curvature component second lowerSecond

/-- The covariant Maxwell stress matrix derived from the action. -/
def maxwellCovariantStressAt
    (metric inverse : Matrix4) (curvature : Fin 2 → Matrix4) : Matrix4 :=
  fun first second =>
    maxwellCovariantQuadraticAt inverse curvature first second -
      (1 / 4 : Real) * metric first second *
        maxwellPairingAt inverse curvature

/-- Pairing obtained by raising both indices of a covariant matrix. -/
def raisedCovariantMatrixPairingAt
    (inverse tensor variation : Matrix4) : Real :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
      inverse first lowerFirst * inverse second lowerSecond *
        tensor lowerFirst lowerSecond) * variation first second

private theorem firstVelocityCore_eq_raisedQuadraticCore
    (inverse variation : Matrix4) (curvature : Fin 2 → Matrix4)
    (hInverse : ∀ first second,
      inverse first second = inverse second first) :
    (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
        inverse μ a * variation a b * inverse b ρ * inverse ν σ *
          curvature component μ ν * curvature component ρ σ) =
      ∑ first : Fin 4, ∑ second : Fin 4,
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ component : Fin 2, ∑ ρ : Fin 4, ∑ σ : Fin 4,
            inverse first lowerFirst * inverse second lowerSecond *
              (curvature component lowerFirst ρ * inverse ρ σ *
                curvature component lowerSecond σ) *
              variation first second := by
  let reindex :
      (Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
        (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 2 × Fin 4 × Fin 4) :=
    { toFun := fun ⟨component, μ, ν, ρ, σ, a, b⟩ =>
        (a, b, μ, ρ, component, ν, σ)
      invFun := fun ⟨first, second, lowerFirst, lowerSecond,
          component, ρ, σ⟩ =>
        (component, lowerFirst, ρ, lowerSecond, σ, first, second)
      left_inv := by rintro ⟨component, μ, ν, ρ, σ, a, b⟩; rfl
      right_inv := by
        rintro ⟨first, second, lowerFirst, lowerSecond,
          component, ρ, σ⟩
        rfl }
  let source :
      (Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) →
        Real :=
    fun ⟨component, μ, ν, ρ, σ, a, b⟩ =>
      inverse μ a * variation a b * inverse b ρ * inverse ν σ *
        curvature component μ ν * curvature component ρ σ
  let target :
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 2 × Fin 4 × Fin 4) →
        Real :=
    fun ⟨first, second, lowerFirst, lowerSecond, component, ρ, σ⟩ =>
      inverse first lowerFirst * inverse second lowerSecond *
        (curvature component lowerFirst ρ * inverse ρ σ *
          curvature component lowerSecond σ) * variation first second
  have h := Fintype.sum_equiv reindex source target (by
    rintro ⟨component, μ, ν, ρ, σ, a, b⟩
    dsimp [source, target, reindex]
    rw [hInverse μ a]
    ring)
  simpa only [source, target, Fintype.sum_prod_type] using h

private theorem secondVelocityCore_eq_raisedQuadraticCore
    (inverse variation : Matrix4) (curvature : Fin 2 → Matrix4)
    (hInverse : ∀ first second,
      inverse first second = inverse second first)
    (hCurvature : ∀ component first second,
      curvature component first second =
        -curvature component second first) :
    (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
        inverse μ ρ * inverse ν a * variation a b * inverse b σ *
          curvature component μ ν * curvature component ρ σ) =
      ∑ first : Fin 4, ∑ second : Fin 4,
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ component : Fin 2, ∑ ρ : Fin 4, ∑ σ : Fin 4,
            inverse first lowerFirst * inverse second lowerSecond *
              (curvature component lowerFirst ρ * inverse ρ σ *
                curvature component lowerSecond σ) *
              variation first second := by
  let reindex :
      (Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
        (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 2 × Fin 4 × Fin 4) :=
    { toFun := fun ⟨component, μ, ν, ρ, σ, a, b⟩ =>
        (a, b, ν, σ, component, μ, ρ)
      invFun := fun ⟨first, second, lowerFirst, lowerSecond,
          component, ρ, σ⟩ =>
        (component, ρ, lowerFirst, σ, lowerSecond, first, second)
      left_inv := by rintro ⟨component, μ, ν, ρ, σ, a, b⟩; rfl
      right_inv := by
        rintro ⟨first, second, lowerFirst, lowerSecond,
          component, ρ, σ⟩
        rfl }
  let source :
      (Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) →
        Real :=
    fun ⟨component, μ, ν, ρ, σ, a, b⟩ =>
      inverse μ ρ * inverse ν a * variation a b * inverse b σ *
        curvature component μ ν * curvature component ρ σ
  let target :
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 2 × Fin 4 × Fin 4) →
        Real :=
    fun ⟨first, second, lowerFirst, lowerSecond, component, ρ, σ⟩ =>
      inverse first lowerFirst * inverse second lowerSecond *
        (curvature component lowerFirst ρ * inverse ρ σ *
          curvature component lowerSecond σ) * variation first second
  have h := Fintype.sum_equiv reindex source target (by
    rintro ⟨component, μ, ν, ρ, σ, a, b⟩
    dsimp [source, target, reindex]
    rw [hInverse ν a, hCurvature component μ ν,
      hCurvature component ρ σ]
    ring)
  simpa only [source, target, Fintype.sum_prod_type] using h

private theorem raisedQuadratic_expand
    (inverse variation : Matrix4) (curvature : Fin 2 → Matrix4) :
    raisedCovariantMatrixPairingAt inverse
        (maxwellCovariantQuadraticAt inverse curvature) variation =
      ∑ first : Fin 4, ∑ second : Fin 4,
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ component : Fin 2, ∑ ρ : Fin 4, ∑ σ : Fin 4,
            inverse first lowerFirst * inverse second lowerSecond *
              (curvature component lowerFirst ρ * inverse ρ σ *
                curvature component lowerSecond σ) *
              variation first second := by
  unfold raisedCovariantMatrixPairingAt maxwellCovariantQuadraticAt
  simp_rw [Finset.mul_sum, Finset.sum_mul]

private theorem maxwellMetricPairingVelocity_inverse_eq_neg_two_raisedQuadratic
    (inverse variation : Matrix4) (curvature : Fin 2 → Matrix4)
    (hInverse : ∀ first second,
      inverse first second = inverse second first)
    (hCurvature : ∀ component first second,
      curvature component first second =
        -curvature component second first) :
    maxwellMetricPairingVelocityAt inverse
        (inverseMetricVelocity inverse variation) curvature =
      -2 * raisedCovariantMatrixPairingAt inverse
        (maxwellCovariantQuadraticAt inverse curvature) variation := by
  have hVelocity (first second : Fin 4) :
      inverseMetricVelocity inverse variation first second =
        -(∑ a : Fin 4, ∑ b : Fin 4,
          inverse first a * variation a b * inverse b second) := by
    unfold inverseMetricVelocity
    simp only [Matrix.neg_apply, Matrix.mul_apply]
    congr 1
    calc
      (∑ b : Fin 4,
          (∑ a : Fin 4, inverse first a * variation a b) *
            inverse b second) =
          ∑ b : Fin 4, ∑ a : Fin 4,
            inverse first a * variation a b * inverse b second := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
      _ = ∑ a : Fin 4, ∑ b : Fin 4,
          inverse first a * variation a b * inverse b second :=
        Finset.sum_comm
  have hFirst :
      (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        ∑ ρ : Fin 4, ∑ σ : Fin 4,
          inverseMetricVelocity inverse variation μ ρ * inverse ν σ *
            curvature component μ ν * curvature component ρ σ) =
        -raisedCovariantMatrixPairingAt inverse
          (maxwellCovariantQuadraticAt inverse curvature) variation := by
    rw [raisedQuadratic_expand]
    calc
      (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        ∑ ρ : Fin 4, ∑ σ : Fin 4,
          inverseMetricVelocity inverse variation μ ρ * inverse ν σ *
            curvature component μ ν * curvature component ρ σ) =
          ∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
            ∑ ρ : Fin 4, ∑ σ : Fin 4,
              -(∑ a : Fin 4, ∑ b : Fin 4,
                inverse μ a * variation a b * inverse b ρ * inverse ν σ *
                  curvature component μ ν * curvature component ρ σ) := by
        apply Finset.sum_congr rfl
        intro component _
        apply Finset.sum_congr rfl
        intro μ _
        apply Finset.sum_congr rfl
        intro ν _
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        rw [hVelocity]
        let factor := inverse ν σ * curvature component μ ν *
          curvature component ρ σ
        calc
          (-(∑ a : Fin 4, ∑ b : Fin 4,
              inverse μ a * variation a b * inverse b ρ)) * inverse ν σ *
                curvature component μ ν * curvature component ρ σ =
              -((∑ a : Fin 4, ∑ b : Fin 4,
                inverse μ a * variation a b * inverse b ρ) * factor) := by
            dsimp [factor]
            ring
          _ = -(∑ a : Fin 4, ∑ b : Fin 4,
              (inverse μ a * variation a b * inverse b ρ) * factor) := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            dsimp [factor]
            ring
      _ = -(∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
            inverse μ a * variation a b * inverse b ρ * inverse ν σ *
              curvature component μ ν * curvature component ρ σ) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := congrArg Neg.neg
        (firstVelocityCore_eq_raisedQuadraticCore inverse variation curvature
          hInverse)
  have hSecond :
      (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        ∑ ρ : Fin 4, ∑ σ : Fin 4,
          inverse μ ρ * inverseMetricVelocity inverse variation ν σ *
            curvature component μ ν * curvature component ρ σ) =
        -raisedCovariantMatrixPairingAt inverse
          (maxwellCovariantQuadraticAt inverse curvature) variation := by
    rw [raisedQuadratic_expand]
    calc
      (∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        ∑ ρ : Fin 4, ∑ σ : Fin 4,
          inverse μ ρ * inverseMetricVelocity inverse variation ν σ *
            curvature component μ ν * curvature component ρ σ) =
          ∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
            ∑ ρ : Fin 4, ∑ σ : Fin 4,
              -(∑ a : Fin 4, ∑ b : Fin 4,
                inverse μ ρ * inverse ν a * variation a b * inverse b σ *
                  curvature component μ ν * curvature component ρ σ) := by
        apply Finset.sum_congr rfl
        intro component _
        apply Finset.sum_congr rfl
        intro μ _
        apply Finset.sum_congr rfl
        intro ν _
        apply Finset.sum_congr rfl
        intro ρ _
        apply Finset.sum_congr rfl
        intro σ _
        rw [hVelocity]
        let factor := inverse μ ρ * curvature component μ ν *
          curvature component ρ σ
        calc
          inverse μ ρ *
                (-(∑ a : Fin 4, ∑ b : Fin 4,
                  inverse ν a * variation a b * inverse b σ)) *
                curvature component μ ν * curvature component ρ σ =
              -((∑ a : Fin 4, ∑ b : Fin 4,
                inverse ν a * variation a b * inverse b σ) * factor) := by
            dsimp [factor]
            ring
          _ = -(∑ a : Fin 4, ∑ b : Fin 4,
              (inverse ν a * variation a b * inverse b σ) * factor) := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            dsimp [factor]
            ring
      _ = -(∑ component : Fin 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
            inverse μ ρ * inverse ν a * variation a b * inverse b σ *
              curvature component μ ν * curvature component ρ σ) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := congrArg Neg.neg
        (secondVelocityCore_eq_raisedQuadraticCore inverse variation curvature
          hInverse hCurvature)
  unfold maxwellMetricPairingVelocityAt
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hFirst, hSecond]
  ring

private theorem raisedMetric_eq_trace
    (metric inverse variation : Matrix4)
    (hMetricInverse : metric * inverse = 1)
    (hInverse : ∀ first second,
      inverse first second = inverse second first)
    (hVariation : ∀ first second,
      variation first second = variation second first) :
    raisedCovariantMatrixPairingAt inverse metric variation =
      metricTraceVariation inverse variation := by
  have hCollapse (lowerFirst second : Fin 4) :
      (∑ lowerSecond : Fin 4,
        inverse second lowerSecond * metric lowerFirst lowerSecond) =
        if lowerFirst = second then 1 else 0 := by
    calc
      (∑ lowerSecond : Fin 4,
          inverse second lowerSecond * metric lowerFirst lowerSecond) =
          ∑ lowerSecond : Fin 4,
            metric lowerFirst lowerSecond * inverse lowerSecond second := by
        apply Finset.sum_congr rfl
        intro lowerSecond _
        rw [hInverse second lowerSecond]
        ring
      _ = (metric * inverse) lowerFirst second := rfl
      _ = (1 : Matrix4) lowerFirst second := by rw [hMetricInverse]
      _ = if lowerFirst = second then 1 else 0 := by
        simp [Matrix.one_apply]
  have hTrace :
      metricTraceVariation inverse variation =
        ∑ first : Fin 4, ∑ second : Fin 4,
          inverse first second * variation second first := by
    rfl
  rw [hTrace]
  unfold raisedCovariantMatrixPairingAt
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  have hRaisedMetric :
      (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        inverse first lowerFirst * inverse second lowerSecond *
          metric lowerFirst lowerSecond) = inverse first second := by
    calc
      (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          inverse first lowerFirst * inverse second lowerSecond *
            metric lowerFirst lowerSecond) =
          ∑ lowerFirst : Fin 4,
            inverse first lowerFirst *
              (∑ lowerSecond : Fin 4,
                inverse second lowerSecond * metric lowerFirst lowerSecond) := by
        apply Finset.sum_congr rfl
        intro lowerFirst _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro lowerSecond _
        ring
      _ = inverse first second := by
        simp_rw [hCollapse]
        simp
  rw [hRaisedMetric, hVariation first second]

private theorem raisedCovariantMatrixPairingAt_sub
    (inverse first second variation : Matrix4) :
    raisedCovariantMatrixPairingAt inverse (first - second) variation =
      raisedCovariantMatrixPairingAt inverse first variation -
        raisedCovariantMatrixPairingAt inverse second variation := by
  unfold raisedCovariantMatrixPairingAt
  simp_rw [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_mul]
  simp only [Finset.sum_sub_distrib]

private theorem raisedCovariantMatrixPairingAt_smul
    (inverse tensor variation : Matrix4) (scalar : Real) :
    raisedCovariantMatrixPairingAt inverse (scalar • tensor) variation =
      scalar * raisedCovariantMatrixPairingAt inverse tensor variation := by
  unfold raisedCovariantMatrixPairingAt
  simp_rw [Matrix.smul_apply, smul_eq_mul]
  have hInner (first second : Fin 4) :
      (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        inverse first lowerFirst * inverse second lowerSecond *
          (scalar * tensor lowerFirst lowerSecond)) =
        scalar * (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          inverse first lowerFirst * inverse second lowerSecond *
            tensor lowerFirst lowerSecond) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lowerFirst _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lowerSecond _
    ring
  simp_rw [hInner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- The finite stress obtained from the Maxwell density is exactly the
double-raised pairing of its covariant stress matrix. -/
theorem variationalMaxwellStressPairing_eq_raisedCovariantStress
    (metric inverse variation : Matrix4) (curvature : Fin 2 → Matrix4)
    (hMetricInverse : metric * inverse = 1)
    (hInverse : ∀ first second,
      inverse first second = inverse second first)
    (hVariation : ∀ first second,
      variation first second = variation second first)
    (hCurvature : ∀ component first second,
      curvature component first second =
        -curvature component second first) :
    variationalMaxwellStressPairing inverse curvature variation =
      raisedCovariantMatrixPairingAt inverse
        (maxwellCovariantStressAt metric inverse curvature) variation := by
  have hStress :
      maxwellCovariantStressAt metric inverse curvature =
        maxwellCovariantQuadraticAt inverse curvature -
          ((1 / 4 : Real) * maxwellPairingAt inverse curvature) • metric := by
    ext first second
    simp [maxwellCovariantStressAt]
    ring
  rw [hStress, raisedCovariantMatrixPairingAt_sub,
    raisedCovariantMatrixPairingAt_smul]
  rw [raisedMetric_eq_trace metric inverse variation hMetricInverse hInverse
    hVariation]
  unfold variationalMaxwellStressPairing localMaxwellMetricVariation
  rw [maxwellMetricPairingVelocity_inverse_eq_neg_two_raisedQuadratic inverse
    variation curvature hInverse hCurvature]
  ring

private theorem regularFrameInverse_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : Fin 4) :
    regularFrameMetricInverseMatrixMap period hPeriod metric point first second =
      regularFrameMetricInverseMatrixMap period hPeriod metric point second first := by
  have hMetric :
      (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
        regularFrameMetricMatrixMap period hPeriod metric point := by
    ext row column
    exact metric.metric.tensor.symmetric point _ _
  have hInverse := Matrix.transpose_nonsing_inv
    (A := regularFrameMetricMatrixMap period hPeriod metric point)
  rw [hMetric] at hInverse
  exact congrFun (congrFun hInverse second) first

private theorem regularFrameMaxwellStressCoefficient_eq_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin 4) :
    regularFrameMaxwellStressCoefficient period hPeriod metric potential
        first second point =
      maxwellCovariantStressAt
        (regularFrameMetricMatrixMap period hPeriod metric point)
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun component row column =>
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component row column point)
        first second := by
  unfold regularFrameMaxwellStressCoefficient maxwellCovariantStressAt
    maxwellCovariantQuadraticAt regularFrameMaxwellQuadraticCoefficient
    regularFrameSmoothMaxwellPairing smoothMaxwellMatrixContraction
    maxwellPairingAt regularFrameMetricMatrixMap
    regularFrameMetricInverseMatrixMap regularFrameMetricInverseMatrix
    regularFrameGaugeCurvatureMatrix
  simp only [smoothScalarFieldSub_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  rw [show regularFrameMetricInverseMatrixMap period hPeriod metric point =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ from rfl]
  ring

/-- Pointwise, the global smooth tensor coefficients are exactly the stress
pairing derived by differentiating the Maxwell density. -/
theorem regularGeneralMetricMaxwellStress_variation_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    variationalMaxwellStressPairing
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun component first second =>
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first second point)
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) =
      raisedCovariantMatrixPairingAt
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun first second =>
          (regularGeneralMetricMaxwellStressTensor period hPeriod metric
            potential).tensor point
              (metric.frame first point) (metric.frame second point))
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) := by
  let metricMatrix := regularFrameMetricMatrixMap period hPeriod metric point
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let curvature : Fin 2 → Matrix4 := fun component first second =>
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
      component first second point
  let variationMatrix : Matrix4 := fun first second =>
    variation.tensor point (metric.frame first point) (metric.frame second point)
  have hMetricInverse : metricMatrix * inverse = 1 := by
    exact Matrix.mul_nonsing_inv metricMatrix
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hInverse : ∀ first second,
      inverse first second = inverse second first :=
    regularFrameInverse_symmetric period hPeriod metric point
  have hVariation : ∀ first second,
      variationMatrix first second = variationMatrix second first := by
    intro first second
    exact variation.symmetric point _ _
  have hCurvature : ∀ component first second,
      curvature component first second =
        -curvature component second first := by
    intro component first second
    exact congrArg
      (fun field : SmoothScalarField period hPeriod => field point)
      (regularFrameGaugeCurvatureCoefficient_swap period hPeriod metric
        potential component first second)
  rw [show (fun first second =>
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric
        potential).tensor point
          (metric.frame first point) (metric.frame second point)) =
      maxwellCovariantStressAt metricMatrix inverse curvature by
    funext first second
    rw [regularGeneralMetricMaxwellStressTensor_frame]
    exact regularFrameMaxwellStressCoefficient_eq_local period hPeriod metric
      potential point first second]
  exact variationalMaxwellStressPairing_eq_raisedCovariantStress
    metricMatrix inverse variationMatrix curvature hMetricInverse hInverse
      hVariation hCurvature

/-- Gate marker: the global Maxwell stress tensor is no longer merely a
candidate; its regular-frame pairing is the metric derivative of the density. -/
theorem regular_general_metric_maxwell_stress_variation_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    variationalMaxwellStressPairing
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun component first second =>
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first second point)
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) =
      raisedCovariantMatrixPairingAt
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun first second =>
          (regularGeneralMetricMaxwellStressTensor period hPeriod metric
            potential).tensor point
              (metric.frame first point) (metric.frame second point))
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) :=
  regularGeneralMetricMaxwellStress_variation_frame period hPeriod metric
    potential variation point

end
end P0EFTJanusProgramPRegularGeneralMetricMaxwellStressVariationBridge4D
end JanusFormal
