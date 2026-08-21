import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCanonicalDuhamelFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

/-!
# Isospectral commutator Duhamel frontend

Cyclicity makes the intrinsic trace of a certified nuclear commutator vanish.
Combined with unitary heat conjugation, this constructs the canonical Duhamel
trace-variation packet without a separate scalar derivative premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCommutatorDuhamelFrontend4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D
open P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
open P0EFTJanusProgramPNuclearHeatCanonicalDuhamelTraceVariationFrontend4D
open P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCanonicalDuhamelFrontend4D
open P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A Duhamel operator identified with a certified nuclear commutator has zero
intrinsic trace. -/
theorem intrinsicNuclearTrace_eq_zero_of_commutator
    {nuclear bounded duhamel : E →L[Real] E}
    (cyclic : CyclicNuclearCompositionExpansionData.{v, u}
      nuclear bounded)
    (leftTrace : IntrinsicNuclearTraceData.{u, v}
      (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData.{u, v}
      (nuclear.comp bounded))
    (duhamelTrace : IntrinsicNuclearTraceData.{u, v} duhamel)
    (duhamel_eq : duhamel = bounded.comp nuclear - nuclear.comp bounded) :
    intrinsicNuclearTrace duhamelTrace = 0 := by
  let commutatorTrace : IntrinsicNuclearTraceData.{u, v}
      (bounded.comp nuclear - nuclear.comp bounded) :=
    IntrinsicNuclearTraceData.transportOperator duhamelTrace duhamel_eq
  calc
    intrinsicNuclearTrace duhamelTrace =
        intrinsicNuclearTrace commutatorTrace :=
      (IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
        duhamelTrace duhamel_eq).symm
    _ = intrinsicNuclearTrace leftTrace - intrinsicNuclearTrace rightTrace :=
      intrinsicNuclearTrace_sub leftTrace rightTrace commutatorTrace
    _ = 0 := sub_eq_zero.mpr
      (cyclic.intrinsicNuclearTrace_comp_comm leftTrace rightTrace)

/-- Unitary heat conjugation plus a pointwise certified commutator constructs
the minimal canonical Duhamel trace-variation frontend. -/
def nuclearHeatCanonicalDuhamelTraceVariationFrontendData_of_commutator
    (heatFamily : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (nuclearOperator boundedOperator duhamelOperator :
      Real → HeatTime → E →L[Real] E)
    (cyclic : ∀ parameter time,
      CyclicNuclearCompositionExpansionData.{v, u}
        (nuclearOperator parameter time) (boundedOperator parameter time))
    (leftTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v}
        ((boundedOperator parameter time).comp
          (nuclearOperator parameter time)))
    (rightTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v}
        ((nuclearOperator parameter time).comp
          (boundedOperator parameter time)))
    (duhamelTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v} (duhamelOperator parameter time))
    (duhamel_eq : ∀ parameter time,
      duhamelOperator parameter time =
        (boundedOperator parameter time).comp
            (nuclearOperator parameter time) -
          (nuclearOperator parameter time).comp
            (boundedOperator parameter time)) :
    NuclearHeatCanonicalDuhamelTraceVariationFrontendData.{u, v}
      (E := E) :=
  nuclearHeatCanonicalDuhamelTraceVariationFrontendData_of_unitaryConjugated
    heatFamily duhamelOperator duhamelTrace fun parameter time =>
      intrinsicNuclearTrace_eq_zero_of_commutator
        (cyclic parameter time) (leftTrace parameter time)
          (rightTrace parameter time) (duhamelTrace parameter time)
            (duhamel_eq parameter time)

/-- The aligned cyclicity packet is generated automatically from one nuclear
rank-one expansion of the first commutator factor. -/
def nuclearHeatCanonicalDuhamelTraceVariationFrontendData_of_commutatorExpansion
    (heatFamily : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (nuclearOperator boundedOperator duhamelOperator :
      Real → HeatTime → E →L[Real] E)
    (nuclearExpansion : ∀ parameter time,
      SummableRankOneOperatorExpansion.{v, u}
        (nuclearOperator parameter time))
    (leftTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v}
        ((boundedOperator parameter time).comp
          (nuclearOperator parameter time)))
    (rightTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v}
        ((nuclearOperator parameter time).comp
          (boundedOperator parameter time)))
    (duhamelTrace : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v} (duhamelOperator parameter time))
    (duhamel_eq : ∀ parameter time,
      duhamelOperator parameter time =
        (boundedOperator parameter time).comp
            (nuclearOperator parameter time) -
          (nuclearOperator parameter time).comp
            (boundedOperator parameter time)) :
    NuclearHeatCanonicalDuhamelTraceVariationFrontendData.{u, v}
      (E := E) :=
  nuclearHeatCanonicalDuhamelTraceVariationFrontendData_of_commutator
    heatFamily nuclearOperator boundedOperator duhamelOperator
      (fun parameter time =>
        P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D.SummableRankOneOperatorExpansion.toCyclicCompositionData
          (nuclearExpansion parameter time)
          (boundedOperator parameter time))
      leftTrace rightTrace duhamelTrace duhamel_eq

end
end P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCommutatorDuhamelFrontend4D
end JanusFormal
