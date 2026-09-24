import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricJetLinearization4D

/-! Polynomial joint regularity of the velocity and mixed acceleration of the metric jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12MetricJetLinearizationSmooth4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff BigOperators
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12MetricJetCovector4D
open P0EFTJanusProgramPT12MetricJetLinearization4D

local instance : NormedAddCommGroup MetricVariationJet := inferInstance
local instance : NormedSpace Real MetricVariationJet := inferInstance

private def matrixProduct (left right : MetricMatrix) : MetricMatrix :=
  fun row column => ∑ middle, left row middle * right middle column

@[fun_prop] private theorem matrixProduct_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × MetricMatrix => matrixProduct input.1 input.2) := by
  unfold matrixProduct
  fun_prop

theorem metricJetVelocity_joint_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × MetricVariationJet => metricJetVelocity input.1 input.2) := by
  change ContDiff Real ∞ (fun input : MetricMatrix × MetricVariationJet =>
    (input.2.1, -matrixProduct (matrixProduct input.1 input.2.1) input.1, input.2.2.1, input.2.2.2))
  fun_prop

theorem metricJetAcceleration_joint_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × MetricVariationJet × MetricVariationJet =>
      metricJetAcceleration input.1 input.2.1 input.2.2) := by
  change ContDiff Real ∞ (fun input : MetricMatrix × MetricVariationJet × MetricVariationJet =>
    ((0 : MetricMatrix), matrixProduct
      (matrixProduct (matrixProduct input.1 input.2.2.1) (matrixProduct input.1 input.2.1.1) +
        matrixProduct (matrixProduct input.1 input.2.1.1) (matrixProduct input.1 input.2.2.1)) input.1,
      (0 : MetricFirstJet), (0 : MetricSecondJet)))
  fun_prop

end
end JanusFormal.P0EFTJanusProgramPT12MetricJetLinearizationSmooth4D
