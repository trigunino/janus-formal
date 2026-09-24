import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D

/-! Joint regularity in the frame coefficients, their derivatives, and the metric jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12CurvatureJetJointSmooth4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped ContDiff
open P0EFTJanusProgramPT12CurvatureJetSymbol4D

abbrev CurvatureSymbolInput := MetricFirstJet × MetricSecondJet × CurvatureJet

@[fun_prop] theorem jetKoszul_joint_contDiff (first second lower : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetKoszul input.1 input.2.2 first second lower) := by
  unfold jetKoszul
  fun_prop

@[fun_prop] theorem jetStructureDerivative_joint_contDiff (direction first second contracted row column : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetStructureDerivative input.1 input.2.1 input.2.2
      direction first second contracted row column) := by
  unfold jetStructureDerivative
  fun_prop

@[fun_prop] theorem jetKoszulDerivative_joint_contDiff (direction first second lower : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetKoszulDerivative input.1 input.2.1 input.2.2
      direction first second lower) := by
  unfold jetKoszulDerivative
  fun_prop

@[fun_prop] theorem jetChristoffel_joint_contDiff (upper first second : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetChristoffel input.1 input.2.2 upper first second) := by
  unfold jetChristoffel
  fun_prop

@[fun_prop] theorem jetChristoffelDerivative_joint_contDiff (direction upper first second : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetChristoffelDerivative input.1 input.2.1 input.2.2
      direction upper first second) := by
  unfold jetChristoffelDerivative
  fun_prop

@[fun_prop] theorem jetRiemann_joint_contDiff (upper lower first second : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetRiemann input.1 input.2.1 input.2.2
      upper lower first second) := by
  unfold jetRiemann
  fun_prop

@[fun_prop] theorem jetRicci_joint_contDiff (first second : Fin 4) :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetRicci input.1 input.2.1 input.2.2 first second) := by
  unfold jetRicci
  fun_prop

@[fun_prop] theorem jetScalarCurvature_joint_contDiff :
    ContDiff Real ∞ (fun input : CurvatureSymbolInput => jetScalarCurvature input.1 input.2.1 input.2.2) := by
  unfold jetScalarCurvature
  fun_prop

end
end JanusFormal.P0EFTJanusProgramPT12CurvatureJetJointSmooth4D
