import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D

/-! Explicit coefficients of a linear functional on the value and ordered metric jets. -/
namespace JanusFormal.P0EFTJanusProgramPT12MetricJetCovector4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open scoped BigOperators

abbrev MetricVariationJet := MetricMatrix × MetricFirstJet × MetricSecondJet

def valueBasis (row column : Fin 4) : MetricVariationJet :=
  (Pi.single row (Pi.single column 1), 0, 0)

def firstBasis (direction row column : Fin 4) : MetricVariationJet :=
  (0, Pi.single direction (Pi.single row (Pi.single column 1)), 0)

def secondBasis (outer inner row column : Fin 4) : MetricVariationJet :=
  (0, 0, Pi.single outer (Pi.single inner (Pi.single row (Pi.single column 1))))

theorem metricVariationJet_decomposition (jet : MetricVariationJet) :
    jet = (∑ row, ∑ column, jet.1 row column • valueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.2.1 direction row column • firstBasis direction row column) +
      (∑ outer, ∑ inner, ∑ row, ∑ column, jet.2.2 outer inner row column • secondBasis outer inner row column) := by
  rcases jet with ⟨value, first, second⟩
  ext <;> simp [valueBasis, firstBasis, secondBasis, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

theorem metricJetCovector_apply (linear : MetricVariationJet →L[Real] Real) (jet : MetricVariationJet) :
    linear jet =
      (∑ row, ∑ column, linear (valueBasis row column) * jet.1 row column) +
      (∑ direction, ∑ row, ∑ column, linear (firstBasis direction row column) * jet.2.1 direction row column) +
      (∑ outer, ∑ inner, ∑ row, ∑ column, linear (secondBasis outer inner row column) * jet.2.2 outer inner row column) := by
  calc
    linear jet = linear ((∑ row, ∑ column, jet.1 row column • valueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.2.1 direction row column • firstBasis direction row column) +
      (∑ outer, ∑ inner, ∑ row, ∑ column, jet.2.2 outer inner row column • secondBasis outer inner row column)) :=
        congrArg linear (metricVariationJet_decomposition jet)
    _ = _ := by simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

end
end JanusFormal.P0EFTJanusProgramPT12MetricJetCovector4D
