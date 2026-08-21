import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

/-!
# Reference heat identification with a product-throat family

The circle twist may vary with the family parameter.  An isometric coordinate
map and an operator identity then generate the product-side nuclear certificate
and equality of intrinsic traces.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D

universe e i

variable {E : Type e}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Realification of the complex-linear product-throat heat operator. -/
def productThroatHeatOperatorReal
    (productData : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert productData →L[Real]
      ProductThroatHeatHilbert productData :=
  (productThroatHeatOperator productData time fold twist).restrictScalars Real

/-- Exact operator-level identification of a reference heat family with a
parameter-dependent product-throat heat family. -/
structure ReferenceProductThroatHeatOperatorIdentificationData
    (productData : ProductThroatSpectralData) (fold : Fold)
    (twist : Real → CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)) where
  coordinates : E ≃ₗᵢ[Real] ProductThroatHeatHilbert productData
  heatOperator_eq : ∀ parameter time,
    isometricEquivalenceConjugatedOperator coordinates
        (nuclear.heatOperator parameter time) =
      productThroatHeatOperatorReal productData time fold (twist parameter)

namespace ReferenceProductThroatHeatOperatorIdentificationData

/-- Nuclear certificate on the concrete product heat operator, generated from
the reference certificate by isometric transport. -/
def productHeatTraceClass
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : Real → CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    (identification :
      ReferenceProductThroatHeatOperatorIdentificationData
        productData fold twist nuclear)
    (parameter : Real) (time : HeatTime) :
    IntrinsicNuclearTraceData.{0, i}
      (productThroatHeatOperatorReal productData time fold (twist parameter)) :=
  IntrinsicNuclearTraceData.transportOperator
    (intrinsicNuclearTraceDataIsometricEquivalenceTransport
      identification.coordinates (nuclear.heatTraceClass parameter time))
    (identification.heatOperator_eq parameter time)

/-- The concrete product-side trace is exactly the original reference heat
trace. -/
theorem productHeatTraceClass_trace_eq
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : Real → CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    (identification :
      ReferenceProductThroatHeatOperatorIdentificationData
        productData fold twist nuclear)
    (parameter : Real) (time : HeatTime) :
    intrinsicNuclearTrace
        (identification.productHeatTraceClass parameter time) =
      nuclear.heatTrace parameter time := by
  calc
    intrinsicNuclearTrace
        (identification.productHeatTraceClass parameter time) =
        intrinsicNuclearTrace
          (intrinsicNuclearTraceDataIsometricEquivalenceTransport
            identification.coordinates
              (nuclear.heatTraceClass parameter time)) :=
      IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
        (intrinsicNuclearTraceDataIsometricEquivalenceTransport
          identification.coordinates (nuclear.heatTraceClass parameter time))
        (identification.heatOperator_eq parameter time)
    _ = intrinsicNuclearTrace (nuclear.heatTraceClass parameter time) :=
      intrinsicNuclearTraceDataIsometricEquivalenceTransport_trace
        identification.coordinates (nuclear.heatTraceClass parameter time)
    _ = nuclear.heatTrace parameter time := rfl

/-- Public product-reference identification checkpoint. -/
theorem reference_product_throat_heat_operator_identification_gate
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : Real → CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    (identification :
      ReferenceProductThroatHeatOperatorIdentificationData
        productData fold twist nuclear)
    (parameter : Real) (time : HeatTime) :
    isometricEquivalenceConjugatedOperator identification.coordinates
        (nuclear.heatOperator parameter time) =
        productThroatHeatOperatorReal productData time fold (twist parameter) ∧
    intrinsicNuclearTrace
        (identification.productHeatTraceClass parameter time) =
      nuclear.heatTrace parameter time :=
  ⟨identification.heatOperator_eq parameter time,
    identification.productHeatTraceClass_trace_eq parameter time⟩

end ReferenceProductThroatHeatOperatorIdentificationData

end
end P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D
end JanusFormal
