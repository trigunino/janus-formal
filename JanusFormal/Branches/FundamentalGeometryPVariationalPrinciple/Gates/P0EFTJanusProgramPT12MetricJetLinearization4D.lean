import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricJetCovector4D
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul

/-! Linear dependence of curvature-jet velocity and mixed acceleration on the test metric jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12MetricJetLinearization4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12MetricJetCovector4D

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

private def valueLinear : MetricVariationJet →ₗ[Real] Matrix4 where
  toFun jet := jet.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def leftProduct (left : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun right := left * right
  map_add' first second := Matrix.mul_add left first second
  map_smul' scalar right := Matrix.mul_smul left scalar right

private def rightProduct (right : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun left := left * right
  map_add' first second := Matrix.add_mul first second right
  map_smul' scalar left := Matrix.smul_mul scalar left right

def metricJetVelocity (inverse : Matrix4) : MetricVariationJet →L[Real] CurvatureJet :=
  let inversePart := -((rightProduct inverse).comp ((leftProduct inverse).comp valueLinear))
  LinearMap.toContinuousLinearMap {
    toFun := fun jet => (jet.1, inversePart jet, jet.2.1, jet.2.2)
    map_add' := by intros; simp only [map_add]; rfl
    map_smul' := by intros; simp only [map_smul]; rfl }

def metricJetAcceleration (inverse : Matrix4) (first : MetricVariationJet) :
    MetricVariationJet →L[Real] CurvatureJet :=
  let firstRelative := leftProduct inverse first.1
  let inversePart := (rightProduct inverse).comp
    (((rightProduct firstRelative).comp (leftProduct inverse) +
      (leftProduct firstRelative).comp (leftProduct inverse)).comp valueLinear)
  LinearMap.toContinuousLinearMap {
    toFun := fun second => (0, inversePart second, 0, 0)
    map_add' := by intros; ext <;> simp
    map_smul' := by intros; ext <;> simp }

/-- The complete chain-rule density, including the inverse acceleration, is a covector in the test jet. -/
def metricJetHessianCovector (inverse : Matrix (Fin 4) (Fin 4) Real)
    (gradient : CurvatureJet →L[Real] Real) (hessian : CurvatureJet →L[Real] CurvatureJet →L[Real] Real)
    (first : MetricVariationJet) : MetricVariationJet →L[Real] Real :=
  (hessian (metricJetVelocity inverse first)).comp (metricJetVelocity inverse) +
    gradient.comp (metricJetAcceleration inverse first)

theorem metricJetHessianCovector_apply (inverse : Matrix (Fin 4) (Fin 4) Real)
    (gradient : CurvatureJet →L[Real] Real) (hessian : CurvatureJet →L[Real] CurvatureJet →L[Real] Real)
    (first second : MetricVariationJet) :
    metricJetHessianCovector inverse gradient hessian first second =
      hessian (metricJetVelocity inverse first) (metricJetVelocity inverse second) +
        gradient (metricJetAcceleration inverse first second) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12MetricJetLinearization4D
