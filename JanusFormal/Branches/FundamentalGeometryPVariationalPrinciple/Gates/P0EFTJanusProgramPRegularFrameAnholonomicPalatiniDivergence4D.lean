import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D

/-! # Contracted Palatini divergence in the anholonomic regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Matrix
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D

private abbrev Index4 := Fin 4
private abbrev Matrix4 := Matrix Index4 Index4 Real

/-- A torsion-free regular-frame Palatini jet with the actual inverse-metric
jet and its metric-compatibility equation. -/
structure MetricCompatibleRegularFramePalatiniJet4 extends
    TorsionFreeRegularFrameConnectionVariationJet4 where
  inverse : Matrix4
  frameInverseDerivative : Index4 → Index4 → Index4 → Real
  inverse_symmetric : ∀ first second,
    inverse first second = inverse second first
  inverse_metric_compatible : ∀ derivative first second,
    frameInverseDerivative derivative first second +
      (∑ auxiliary : Index4,
        connection first derivative auxiliary * inverse auxiliary second) +
      ∑ auxiliary : Index4,
        connection second derivative auxiliary * inverse first auxiliary = 0

theorem MetricCompatibleRegularFramePalatiniJet4.frameInverseDerivative_eq
    (jet : MetricCompatibleRegularFramePalatiniJet4)
    (derivative first second : Index4) :
    jet.frameInverseDerivative derivative first second =
      -(∑ auxiliary : Index4,
          jet.connection first derivative auxiliary *
            jet.inverse auxiliary second) -
        ∑ auxiliary : Index4,
          jet.connection second derivative auxiliary *
            jet.inverse first auxiliary := by
  linarith [jet.inverse_metric_compatible derivative first second]

/-- Contraction of the genuine anholonomic Palatini Ricci velocity. -/
def regularFrameContractedPalatiniDerivative
    (jet : MetricCompatibleRegularFramePalatiniJet4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    jet.inverse first second *
      regularFramePalatiniRicciVelocity
        jet.toTorsionFreeRegularFrameConnectionVariationJet4 first second

/-- Palatini vector
`V^ρ = g^μν C^ρ_{νμ} - g^μρ C^ν_{νμ}` in the regular frame. -/
def regularFramePalatiniVector
    (jet : MetricCompatibleRegularFramePalatiniJet4)
    (vector : Index4) : Real :=
  (∑ first : Index4, ∑ second : Index4,
      jet.inverse first second * jet.variation vector second first) -
    ∑ first : Index4, ∑ contracted : Index4,
      jet.inverse first vector * jet.variation contracted contracted first

/-- Frame product-rule derivative of the Palatini vector. -/
def regularFramePalatiniVectorDerivative
    (jet : MetricCompatibleRegularFramePalatiniJet4)
    (derivative vector : Index4) : Real :=
  (∑ first : Index4, ∑ second : Index4,
      (jet.frameInverseDerivative derivative first second *
          jet.variation vector second first +
        jet.inverse first second *
          jet.frameVariationDerivative derivative vector second first)) -
    ∑ first : Index4, ∑ contracted : Index4,
      (jet.frameInverseDerivative derivative first vector *
          jet.variation contracted contracted first +
        jet.inverse first vector *
          jet.frameVariationDerivative derivative contracted contracted first)

/-- Covariant divergence `e_ρ V^ρ + Γ^ρ_{ρλ}V^λ` in the regular
frame. -/
def regularFramePalatiniVectorCovariantDivergence
    (jet : MetricCompatibleRegularFramePalatiniJet4) : Real :=
  ∑ derivative : Index4,
    (regularFramePalatiniVectorDerivative jet derivative derivative +
      ∑ auxiliary : Index4,
        jet.connection derivative derivative auxiliary *
          regularFramePalatiniVector jet auxiliary)

set_option maxHeartbeats 4000000 in
/-- Metric compatibility converts the contracted anholonomic Palatini
identity into the covariant divergence of its explicit vector. -/
theorem regularFrameContractedPalatiniDerivative_eq_covariantDivergence
    (jet : MetricCompatibleRegularFramePalatiniJet4) :
    regularFrameContractedPalatiniDerivative jet =
      regularFramePalatiniVectorCovariantDivergence jet := by
  unfold regularFrameContractedPalatiniDerivative
    regularFramePalatiniRicciVelocity
    regularFrameCovariantConnectionVariationDerivative
    regularFramePalatiniVectorCovariantDivergence
    regularFramePalatiniVectorDerivative regularFramePalatiniVector
  simp_rw [jet.frameInverseDerivative_eq]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Fin.sum_univ_four]
  ring

/-- Gate marker for the contracted anholonomic Palatini divergence. -/
theorem regular_frame_anholonomic_palatini_divergence_gate
    (jet : MetricCompatibleRegularFramePalatiniJet4) :
    regularFrameContractedPalatiniDerivative jet =
      regularFramePalatiniVectorCovariantDivergence jet :=
  regularFrameContractedPalatiniDerivative_eq_covariantDivergence jet

end
end P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
end JanusFormal
