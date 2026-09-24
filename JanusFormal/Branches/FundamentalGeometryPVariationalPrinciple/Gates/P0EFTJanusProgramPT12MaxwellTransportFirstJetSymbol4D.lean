import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellJetSymbol4D
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The transported Cartan curvature uses only the matrix value and first jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff BigOperators
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12MaxwellJetSymbol4D

abbrev MatrixFirstJet := MetricMatrix × MetricFirstJet
abbrev GaugeValue := Fin 4 → Fin 2 → Real
abbrev GaugeFirstJet := Fin 4 → GaugeValue
abbrev TransportSymbolParameters := MetricFirstJet × GaugeValue × GaugeFirstJet

def transportCurvatureSymbol (parameters : TransportSymbolParameters) (jet : MatrixFirstJet) : MaxwellCurvature :=
  fun component row column =>
    (∑ moving, (jet.1 moving column * parameters.2.2 row moving component +
      jet.2 row moving column * parameters.2.1 moving component)) -
    (∑ moving, (jet.1 moving row * parameters.2.2 column moving component +
      jet.2 column moving row * parameters.2.1 moving component)) -
    ∑ upper, parameters.1 row column upper *
      (∑ moving, jet.1 moving upper * parameters.2.1 moving component)

theorem transportCurvatureSymbol_contDiff :
    ContDiff Real ∞ (fun input : TransportSymbolParameters × MatrixFirstJet =>
      transportCurvatureSymbol input.1 input.2) := by
  unfold transportCurvatureSymbol
  fun_prop

/-- Exact linear dependence on the transported matrix jet. -/
def transportCurvatureLinear (parameters : TransportSymbolParameters) : MatrixFirstJet →L[Real] MaxwellCurvature :=
  LinearMap.toContinuousLinearMap
    { toFun := transportCurvatureSymbol parameters
      map_add' := by
        intro first second
        ext component row column
        simp [transportCurvatureSymbol, add_mul, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro scalar jet
        ext component row column
        simp only [transportCurvatureSymbol, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        simp only [mul_assoc, ← mul_add, ← Finset.mul_sum, ← mul_sub]
        simp only [mul_sub, Finset.mul_sum, mul_left_comm] }

@[simp]
theorem transportCurvatureLinear_apply (parameters : TransportSymbolParameters) (jet : MatrixFirstJet) :
    transportCurvatureLinear parameters jet = transportCurvatureSymbol parameters jet := rfl

end
end JanusFormal.P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
