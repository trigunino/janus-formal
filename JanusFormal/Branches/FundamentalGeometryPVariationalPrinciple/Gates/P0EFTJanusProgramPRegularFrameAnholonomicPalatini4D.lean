import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D

/-! # Anholonomic Palatini identity for the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D

private abbrev Index4 := Fin 4

/-- Torsion-freeness in an anholonomic frame is
`Γᵃ_bc - Γᵃ_cb = Cᵃ_bc`, not lower-index symmetry. -/
structure TorsionFreeRegularFrameConnectionVariationJet4 extends
    RegularFrameConnectionVariationJet4 where
  connection_torsionFree : ∀ upper first second,
    connection upper first second - connection upper second first =
      structureCoefficient first second upper

/-- Covariant derivative of the connection variation as a `(1,2)` tensor in
the fixed regular frame. -/
def regularFrameCovariantConnectionVariationDerivative
    (jet : TorsionFreeRegularFrameConnectionVariationJet4)
    (derivative upper first second : Index4) : Real :=
  jet.frameVariationDerivative derivative upper first second +
    (∑ auxiliary : Index4,
      jet.connection upper derivative auxiliary *
        jet.variation auxiliary first second) -
    (∑ auxiliary : Index4,
      jet.connection auxiliary derivative first *
        jet.variation upper auxiliary second) -
    ∑ auxiliary : Index4,
      jet.connection auxiliary derivative second *
        jet.variation upper first auxiliary

/-- Palatini form `δR_{μν} = ∇ρ C^ρ_{νμ} - ∇ν C^ρ_{ρμ}` in the
anholonomic regular frame. -/
def regularFramePalatiniRicciVelocity
    (jet : TorsionFreeRegularFrameConnectionVariationJet4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    (regularFrameCovariantConnectionVariationDerivative jet
        contracted contracted second first -
      regularFrameCovariantConnectionVariationDerivative jet
        second contracted contracted first)

/-- The explicit structure-coefficient term in the regular-frame curvature
is exactly what converts torsion-freeness into the covariant Palatini
identity. -/
theorem regularFrameRicciVelocityFromConnection_eq_palatini
    (jet : TorsionFreeRegularFrameConnectionVariationJet4)
    (first second : Index4) :
    regularFrameRicciVelocityFromConnection
        jet.toRegularFrameConnectionVariationJet4 first second =
      regularFramePalatiniRicciVelocity jet first second := by
  unfold regularFrameRicciVelocityFromConnection
    regularFramePalatiniRicciVelocity
    regularFrameCovariantConnectionVariationDerivative
  apply Finset.sum_congr rfl
  intro contracted _
  have hCancel :
      (∑ auxiliary : Index4,
          jet.connection auxiliary contracted second *
            jet.variation contracted auxiliary first) =
        (∑ auxiliary : Index4,
          jet.connection auxiliary second contracted *
            jet.variation contracted auxiliary first) +
        ∑ auxiliary : Index4,
          jet.structureCoefficient contracted second auxiliary *
            jet.variation contracted auxiliary first := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro auxiliary _
    have hTorsion := jet.connection_torsionFree
      auxiliary contracted second
    calc
      jet.connection auxiliary contracted second *
          jet.variation contracted auxiliary first =
        (jet.connection auxiliary second contracted +
            jet.structureCoefficient contracted second auxiliary) *
          jet.variation contracted auxiliary first := by
            congr 1
            linarith
      _ = jet.connection auxiliary second contracted *
            jet.variation contracted auxiliary first +
          jet.structureCoefficient contracted second auxiliary *
            jet.variation contracted auxiliary first := by ring
  simp_rw [Finset.sum_add_distrib]
  rw [hCancel]
  ring

/-- Gate marker for the correct anholonomic Palatini identity. -/
theorem regular_frame_anholonomic_palatini_gate
    (jet : TorsionFreeRegularFrameConnectionVariationJet4)
    (first second : Index4) :
    regularFrameRicciVelocityFromConnection
        jet.toRegularFrameConnectionVariationJet4 first second =
      regularFramePalatiniRicciVelocity jet first second :=
  regularFrameRicciVelocityFromConnection_eq_palatini jet first second

end
end P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D
end JanusFormal
