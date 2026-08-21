import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

/-!
# Product-throat real heat trace from one explicit expansion

Once the abstract heat operator is identified isometrically with the concrete
product operator, one explicit real rank-one expansion computes its intrinsic
trace.  This removes a separate abstract trace-normalization premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceProductThroatRealHeatTraceExpansionFrontend4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One concrete real rank-one expansion closes the real heat-trace
identification after operator conjugacy has been proved. -/
def referenceProductThroatRealHeatTraceIdentificationData_of_expansion
    (productData : ProductThroatSpectralData) (fold : Fold)
    (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (operatorIdentification :
      ReferenceProductThroatHeatOperatorIdentificationData productData fold
        (fun _ => twist) nuclear)
    (expansion : ∀ time,
      SummableRankOneOperatorExpansion.{v}
        (productThroatHeatOperatorReal productData time fold twist))
    (expansionTrace_eq : ∀ time,
      (expansion time).expansionTrace =
        2 * productThroatNuclearHeatTrace productData time fold twist) :
    ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear where
  operatorIdentification := operatorIdentification
  heatTrace_eq_realProductTrace := by
    intro parameter time
    calc
      nuclear.heatTrace parameter time =
          intrinsicNuclearTrace
            (operatorIdentification.productHeatTraceClass parameter time) :=
        (operatorIdentification.productHeatTraceClass_trace_eq
          parameter time).symm
      _ = (expansion time).expansionTrace :=
        ((operatorIdentification.productHeatTraceClass parameter time).expansionTrace_eq
          (expansion time)).symm
      _ = 2 * productThroatNuclearHeatTrace productData time fold twist :=
        expansionTrace_eq time

end
end P0EFTJanusProgramPReferenceProductThroatRealHeatTraceExpansionFrontend4D
end JanusFormal
