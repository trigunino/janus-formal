import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentFieldVariationLinearSpace4D

namespace JanusFormal
namespace P0EFTJanusCompleteVariationModuleCore4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem smoothSymmetric_ext_pointwise
    {first second : SmoothSymmetricCovariantTwoTensor period hPeriod}
    (h : ∀ point x y, first.tensor point x y = second.tensor point x y) :
    first = second := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  exact h point x y

instance : Zero (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  zero := zeroSymmetricTensor period hPeriod

instance : Add (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  add first second :=
    { tensor := first.tensor + second.tensor
      symmetric := by
        intro point x y
        simpa only [ContMDiffSection.coe_add, Pi.add_apply,
          ContinuousLinearMap.add_apply] using
          congrArg₂ (fun a b : Real => a + b) (first.symmetric point x y)
            (second.symmetric point x y) }

instance : Neg (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  neg tensor :=
    { tensor := -tensor.tensor
      symmetric := by
        intro point x y
        simpa only [ContMDiffSection.coe_neg, Pi.neg_apply,
          ContinuousLinearMap.neg_apply] using
          congrArg Neg.neg (tensor.symmetric point x y) }

instance : Sub (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  sub first second := first + -second

instance : AddCommGroup (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  add_assoc first second third := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change (first.tensor point x y + second.tensor point x y) +
      third.tensor point x y = first.tensor point x y +
        (second.tensor point x y + third.tensor point x y)
    ring
  zero_add tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change 0 + tensor.tensor point x y = tensor.tensor point x y
    ring
  add_zero tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change tensor.tensor point x y + 0 = tensor.tensor point x y
    ring
  nsmul := nsmulRec
  add_comm first second := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change first.tensor point x y + second.tensor point x y =
      second.tensor point x y + first.tensor point x y
    ring
  neg_add_cancel tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change -(tensor.tensor point x y) + tensor.tensor point x y = 0
    ring
  sub_eq_add_neg first second := by
    rfl
  zsmul := zsmulRec

instance : SMul Real (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  smul scalar tensor :=
    { tensor := scalar • tensor.tensor
      symmetric := by
        intro point x y
        simpa only [ContMDiffSection.coe_smul, Pi.smul_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul] using
          congrArg (scalar * .) (tensor.symmetric point x y) }

instance : Module Real (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  one_smul tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change (1 : Real) * tensor.tensor point x y = tensor.tensor point x y
    ring
  mul_smul first second tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change (first * second) * tensor.tensor point x y =
      first * (second * tensor.tensor point x y)
    ring
  smul_add scalar first second := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change scalar * (first.tensor point x y + second.tensor point x y) =
      scalar * first.tensor point x y + scalar * second.tensor point x y
    ring
  smul_zero scalar := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change scalar * 0 = (0 : Real)
    ring
  add_smul first second tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change (first + second) * tensor.tensor point x y =
      first * tensor.tensor point x y + second * tensor.tensor point x y
    ring
  zero_smul tensor := by
    apply smoothSymmetric_ext_pointwise
    intro point x y
    change (0 : Real) * tensor.tensor point x y = 0
    ring

@[ext] theorem ProgramPCompleteVariation4D.ext
    {first second : ProgramPCompleteVariation4D period hPeriod}
    (hIndependent : first.independent = second.independent)
    (hNormal : first.normalDisplacement = second.normalDisplacement)
    (hGhost : first.diffeomorphismGhost = second.diffeomorphismGhost)
    (hMetric : first.fullMetricPerturbation = second.fullMetricPerturbation) :
    first = second := by
  cases first
  cases second
  simp_all

instance : Zero (ProgramPCompleteVariation4D period hPeriod) where
  zero := ⟨0, 0, 0, 0⟩

instance : Add (ProgramPCompleteVariation4D period hPeriod) where
  add first second :=
    ⟨first.independent + second.independent,
      first.normalDisplacement + second.normalDisplacement,
      first.diffeomorphismGhost + second.diffeomorphismGhost,
      first.fullMetricPerturbation + second.fullMetricPerturbation⟩

instance : Neg (ProgramPCompleteVariation4D period hPeriod) where
  neg variation :=
    ⟨-variation.independent, -variation.normalDisplacement,
      -variation.diffeomorphismGhost, -variation.fullMetricPerturbation⟩

instance : Sub (ProgramPCompleteVariation4D period hPeriod) where
  sub first second := first + -second

instance : AddCommGroup (ProgramPCompleteVariation4D period hPeriod) where
  add_assoc first second third := by
    apply ProgramPCompleteVariation4D.ext
    · exact add_assoc first.independent second.independent third.independent
    · exact add_assoc first.normalDisplacement second.normalDisplacement third.normalDisplacement
    · exact add_assoc first.diffeomorphismGhost second.diffeomorphismGhost third.diffeomorphismGhost
    · exact add_assoc first.fullMetricPerturbation second.fullMetricPerturbation third.fullMetricPerturbation
  zero_add variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact zero_add variation.independent
    · exact zero_add variation.normalDisplacement
    · exact zero_add variation.diffeomorphismGhost
    · exact zero_add variation.fullMetricPerturbation
  add_zero variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact add_zero variation.independent
    · exact add_zero variation.normalDisplacement
    · exact add_zero variation.diffeomorphismGhost
    · exact add_zero variation.fullMetricPerturbation
  nsmul := nsmulRec
  add_comm first second := by
    apply ProgramPCompleteVariation4D.ext
    · exact add_comm first.independent second.independent
    · exact add_comm first.normalDisplacement second.normalDisplacement
    · exact add_comm first.diffeomorphismGhost second.diffeomorphismGhost
    · exact add_comm first.fullMetricPerturbation second.fullMetricPerturbation
  neg_add_cancel variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact neg_add_cancel variation.independent
    · exact neg_add_cancel variation.normalDisplacement
    · exact neg_add_cancel variation.diffeomorphismGhost
    · exact neg_add_cancel variation.fullMetricPerturbation
  sub_eq_add_neg first second := by
    rfl
  zsmul := zsmulRec

instance : SMul Real (ProgramPCompleteVariation4D period hPeriod) where
  smul scalar variation :=
    ⟨scalar • variation.independent, scalar • variation.normalDisplacement,
      scalar • variation.diffeomorphismGhost,
      scalar • variation.fullMetricPerturbation⟩

instance : Module Real (ProgramPCompleteVariation4D period hPeriod) where
  one_smul variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact one_smul Real variation.independent
    · exact one_smul Real variation.normalDisplacement
    · exact one_smul Real variation.diffeomorphismGhost
    · exact one_smul Real variation.fullMetricPerturbation
  mul_smul first second variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact mul_smul first second variation.independent
    · exact mul_smul first second variation.normalDisplacement
    · exact mul_smul first second variation.diffeomorphismGhost
    · exact mul_smul first second variation.fullMetricPerturbation
  smul_add scalar first second := by
    apply ProgramPCompleteVariation4D.ext
    · exact smul_add scalar first.independent second.independent
    · exact smul_add scalar first.normalDisplacement second.normalDisplacement
    · exact smul_add scalar first.diffeomorphismGhost second.diffeomorphismGhost
    · exact smul_add scalar first.fullMetricPerturbation second.fullMetricPerturbation
  smul_zero scalar := by
    apply ProgramPCompleteVariation4D.ext
    · change scalar • (0 : P0EFTJanusMappingTorusInducedFieldVariation4D.IndependentFieldVariation period hPeriod) = 0
      exact smul_zero scalar
    · change scalar • (0 : Sector → SmoothNormalDisplacement period hPeriod) = 0
      exact smul_zero scalar
    · change scalar • (0 : Sector → P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D.CInfinityThroatGhost period hPeriod) = 0
      exact smul_zero scalar
    · change scalar • (0 : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) = 0
      exact smul_zero scalar
  add_smul first second variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact add_smul first second variation.independent
    · exact add_smul first second variation.normalDisplacement
    · exact add_smul first second variation.diffeomorphismGhost
    · exact add_smul first second variation.fullMetricPerturbation
  zero_smul variation := by
    apply ProgramPCompleteVariation4D.ext
    · exact zero_smul Real variation.independent
    · exact zero_smul Real variation.normalDisplacement
    · exact zero_smul Real variation.diffeomorphismGhost
    · exact zero_smul Real variation.fullMetricPerturbation

/-- The canonical inclusion of independent variations is linear. -/
def independentCompleteVariationLinearMap :
    P0EFTJanusMappingTorusInducedFieldVariation4D.IndependentFieldVariation
        period hPeriod →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod where
  toFun := independentCompleteVariation period hPeriod
  map_add' first second := by
    apply ProgramPCompleteVariation4D.ext
    · rfl
    · funext sector
      change (0 : SmoothNormalDisplacement period hPeriod) = 0 + 0
      exact (zero_add 0).symm
    · funext sector
      apply ContMDiffSection.coe_injective
      funext point
      change (0 : ThroatCoverCoordinates) = 0 + 0
      exact (zero_add 0).symm
    · funext sector
      apply SmoothSymmetricCovariantTwoTensor.ext
      change (0 : SmoothCovariantTwoTensor period hPeriod) = 0 + 0
      exact (zero_add (0 : SmoothCovariantTwoTensor period hPeriod)).symm
  map_smul' scalar variation := by
    apply ProgramPCompleteVariation4D.ext
    · rfl
    · funext sector
      change (0 : SmoothNormalDisplacement period hPeriod) = scalar • 0
      exact (smul_zero scalar).symm
    · funext sector
      apply ContMDiffSection.coe_injective
      funext point
      change (0 : ThroatCoverCoordinates) = scalar • 0
      exact (smul_zero scalar).symm
    · funext sector
      apply SmoothSymmetricCovariantTwoTensor.ext
      change (0 : SmoothCovariantTwoTensor period hPeriod) = scalar • 0
      apply ContMDiffSection.ext
      intro point
      apply ContinuousLinearMap.ext
      intro x
      apply ContinuousLinearMap.ext
      intro y
      change (0 : Real) = scalar * 0
      ring

theorem normalModeAt_add
    (first second : ProgramPCompleteVariation4D period hPeriod) sector point :
    (first + second).normalModeAt period hPeriod sector point =
      first.normalModeAt period hPeriod sector point +
        second.normalModeAt period hPeriod sector point := by
  change _ = _ + _
  exact map_add _ _ _

theorem normalModeAt_smul
    (scalar : Real) (variation : ProgramPCompleteVariation4D period hPeriod)
    sector point :
    (scalar • variation).normalModeAt period hPeriod sector point =
      scalar * variation.normalModeAt period hPeriod sector point := by
  change _ = scalar * _
  exact map_smul _ scalar _

theorem diffeomorphismGhostAt_add
    (first second : ProgramPCompleteVariation4D period hPeriod) sector point :
    (first + second).diffeomorphismGhostAt period hPeriod sector point =
      addTangent (first.diffeomorphismGhostAt period hPeriod sector point)
        (second.diffeomorphismGhostAt period hPeriod sector point) := by
  change throatTangentToD9
    ((first.diffeomorphismGhost sector + second.diffeomorphismGhost sector) point) = _
  have hEval :
      (first.diffeomorphismGhost sector + second.diffeomorphismGhost sector) point =
        first.diffeomorphismGhost sector point +
          second.diffeomorphismGhost sector point := rfl
  rw [hEval]
  ext <;> rfl

theorem diffeomorphismGhostAt_smul
    (scalar : Real) (variation : ProgramPCompleteVariation4D period hPeriod)
    sector point :
    (scalar • variation).diffeomorphismGhostAt period hPeriod sector point =
      scaleTangent scalar
        (variation.diffeomorphismGhostAt period hPeriod sector point) := by
  change throatTangentToD9
    ((scalar • variation.diffeomorphismGhost sector) point) = _
  have hEval :
      (scalar • variation.diffeomorphismGhost sector) point =
        scalar • variation.diffeomorphismGhost sector point := rfl
  rw [hEval]
  ext <;> rfl

private theorem d9TensorChartCoefficient_add
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    patch i j coordinate :
    d9TensorChartCoefficient period hPeriod (first + second) patch i j coordinate =
      d9TensorChartCoefficient period hPeriod first patch i j coordinate +
        d9TensorChartCoefficient period hPeriod second patch i j coordinate := by
  change ((first.tensor + second.tensor) (patch.coordinateMap coordinate))
      (patch.frame coordinate i) (patch.frame coordinate j) = _
  rfl

private theorem d9TensorChartCoefficient_smul
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    patch i j coordinate :
    d9TensorChartCoefficient period hPeriod (scalar • tensor) patch i j coordinate =
      scalar * d9TensorChartCoefficient period hPeriod tensor patch i j coordinate := by
  change ((scalar • tensor.tensor) (patch.coordinateMap coordinate))
      (patch.frame coordinate i) (patch.frame coordinate j) = _
  rfl

theorem metricPerturbationAt_add
    (first second : ProgramPCompleteVariation4D period hPeriod) sector point :
    (first + second).metricPerturbationAt period hPeriod sector point =
      addSymmetric (first.metricPerturbationAt period hPeriod sector point)
        (second.metricPerturbationAt period hPeriod sector point) := by
  ext <;>
    simp only [ProgramPCompleteVariation4D.metricPerturbationAt,
      d9FullMetricProjection, d9TensorChartMetricVariation, addSymmetric] <;>
    exact d9TensorChartCoefficient_add period hPeriod _ _ _ _ _ _

theorem metricPerturbationAt_smul
    (scalar : Real) (variation : ProgramPCompleteVariation4D period hPeriod)
    sector point :
    (scalar • variation).metricPerturbationAt period hPeriod sector point =
      scaleSymmetric scalar
        (variation.metricPerturbationAt period hPeriod sector point) := by
  ext <;>
    simp only [ProgramPCompleteVariation4D.metricPerturbationAt,
      d9FullMetricProjection, d9TensorChartMetricVariation, scaleSymmetric] <;>
    exact d9TensorChartCoefficient_smul period hPeriod scalar _ _ _ _ _

end
end P0EFTJanusCompleteVariationModuleCore4D
end JanusFormal
