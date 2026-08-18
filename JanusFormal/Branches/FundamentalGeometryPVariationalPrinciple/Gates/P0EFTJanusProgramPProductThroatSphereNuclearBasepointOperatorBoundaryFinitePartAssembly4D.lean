import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearBasepointCompatibleFinitePartAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

/-!
# Operator-boundary origin of the basepoint-compatible Duhamel identity

The short operator in this packet represents the UV-renormalized Duhamel
integral directly.  Thus no invalid splitting into two possibly nonintegrable
short-time integrals is used.  A local signed operator identity and the
terminal long-time boundary limit generate the scalar identity required by
the basepoint-compatible finite-part assembly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereNuclearBasepointCompatibleFinitePartAssembly4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

universe u v w

variable {Index : Type*}
variable {LongCutoff : Type w}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Intrinsic operator representing the already-renormalized short-time
Duhamel integral. -/
structure RenormalizedNuclearDuhamelOperatorIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1) where
  integratedOperator : Real → E →L[Real] E
  integratedTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (integratedOperator parameter)
  scalarIntegral_eq_trace : ∀ parameter,
    (∫ time in Set.Ioo (0 : Real) 1,
      shortTime.renormalizedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (integratedTraceClass parameter)

/-- Canonically signed operator data.  The local identity is

`(Short_ren - FP) + B = Log`,

and the terminal primitive supplies `Long = B`. -/
structure ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))) where
  finitePartOperator : Real → E →L[Real] E
  finitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (finitePartOperator parameter)
  finitePartDerivative_eq_trace : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      intrinsicNuclearTrace (finitePartTraceClass parameter)
  renormalizedShortTime :
    RenormalizedNuclearDuhamelOperatorIntegralData.{u, v} nuclear shortTime
  shortMinusFinitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      (renormalizedShortTime.integratedOperator parameter -
        finitePartOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      ((renormalizedShortTime.integratedOperator parameter -
          finitePartOperator parameter) +
        longTime.integratedOperator parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  logarithmicDerivativeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      (logarithmicDerivativeOperator parameter)
  matchingOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    (renormalizedShortTime.integratedOperator parameter -
        finitePartOperator parameter) + matchingOperator parameter =
      logarithmicDerivativeOperator parameter
  longBoundaryLimit : ∀ parameter,
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData longCutoffFilter
      (longTime.integratedOperator parameter) (matchingOperator parameter)

namespace ReferenceNuclearRenormalizedDuhamelGreenBoundaryData

/-- Intrinsic nuclear trace is additive when trace certificates for both
summands and their sum are available. -/
theorem intrinsicNuclearTrace_add
    {first second : E →L[Real] E}
    (firstTrace : IntrinsicNuclearTraceData.{u, v} first)
    (secondTrace : IntrinsicNuclearTraceData.{u, v} second)
    (sumTrace : IntrinsicNuclearTraceData.{u, v} (first + second)) :
    intrinsicNuclearTrace sumTrace =
      intrinsicNuclearTrace firstTrace + intrinsicNuclearTrace secondTrace := by
  let firstAsDifference : IntrinsicNuclearTraceData.{u, v}
      ((first + second) - second) :=
    P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
      firstTrace (by abel)
  have hSub := intrinsicNuclearTrace_sub sumTrace secondTrace firstAsDifference
  have hTransport : intrinsicNuclearTrace firstAsDifference =
      intrinsicNuclearTrace firstTrace := by
    simp [firstAsDifference]
  rw [hTransport] at hSub
  linarith

/-- The actual terminal primitive removes the long-time boundary term. -/
theorem longBoundaryIdentity
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    longTime.integratedOperator parameter = data.matchingOperator parameter :=
  (data.longBoundaryLimit parameter).boundaryIdentity

/-- Local short matching and terminal decay give the complete signed operator
identity. -/
theorem totalOperator_eq_logarithmicDerivative
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    ((data.renormalizedShortTime.integratedOperator parameter -
        data.finitePartOperator parameter) +
      longTime.integratedOperator parameter) =
        data.logarithmicDerivativeOperator parameter := by
  rw [data.longBoundaryIdentity parameter]
  exact data.shortBoundaryIdentity parameter

theorem shortMinusFinitePart_trace
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    intrinsicNuclearTrace (data.shortMinusFinitePartTraceClass parameter) =
      intrinsicNuclearTrace
          (data.renormalizedShortTime.integratedTraceClass parameter) -
        intrinsicNuclearTrace (data.finitePartTraceClass parameter) :=
  intrinsicNuclearTrace_sub
    (data.renormalizedShortTime.integratedTraceClass parameter)
    (data.finitePartTraceClass parameter)
    (data.shortMinusFinitePartTraceClass parameter)

theorem total_trace
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
      intrinsicNuclearTrace (data.shortMinusFinitePartTraceClass parameter) +
        intrinsicNuclearTrace (longTime.integratedTraceClass parameter) :=
  intrinsicNuclearTrace_add
    (data.shortMinusFinitePartTraceClass parameter)
    (longTime.integratedTraceClass parameter)
    (data.totalTraceClass parameter)

/-- Intrinsic trace of the signed logarithmic derivative operator. -/
def logarithmicTrace
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) : Real :=
  intrinsicNuclearTrace (data.logarithmicDerivativeTraceClass parameter)

theorem totalTrace_eq_logarithmicTrace
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
      data.logarithmicTrace parameter := by
  let transported : IntrinsicNuclearTraceData.{u, v}
      (data.logarithmicDerivativeOperator parameter) :=
    P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
      (data.totalTraceClass parameter)
      (data.totalOperator_eq_logarithmicDerivative parameter)
  calc
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
        intrinsicNuclearTrace transported := by
      exact
        (P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
          (data.totalTraceClass parameter)
          (data.totalOperator_eq_logarithmicDerivative parameter)).symm
    _ = intrinsicNuclearTrace
        (data.logarithmicDerivativeTraceClass parameter) :=
      intrinsicNuclearTrace_unique transported
        (data.logarithmicDerivativeTraceClass parameter)
    _ = data.logarithmicTrace parameter := rfl

/-- The scalar field formerly assumed by the finite-part assembly follows
from the signed operator identity. -/
theorem duhamel_integral_identity
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      longCutoffFilter nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    -finitePartDerivative finiteCounterterm parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) =
      data.logarithmicTrace parameter := by
  rw [data.finitePartDerivative_eq_trace parameter,
    data.renormalizedShortTime.scalarIntegral_eq_trace parameter,
    longTime.scalarIntegral_eq_trace parameter]
  calc
    -intrinsicNuclearTrace (data.finitePartTraceClass parameter) +
          intrinsicNuclearTrace
            (data.renormalizedShortTime.integratedTraceClass parameter) +
        intrinsicNuclearTrace (longTime.integratedTraceClass parameter) =
      intrinsicNuclearTrace
          (data.shortMinusFinitePartTraceClass parameter) +
        intrinsicNuclearTrace (longTime.integratedTraceClass parameter) := by
      rw [data.shortMinusFinitePart_trace parameter]
      ring
    _ = intrinsicNuclearTrace (data.totalTraceClass parameter) :=
      (data.total_trace parameter).symm
    _ = data.logarithmicTrace parameter :=
      data.totalTrace_eq_logarithmicTrace parameter

end ReferenceNuclearRenormalizedDuhamelGreenBoundaryData

/-- Spherical-basepoint compatible assembly whose terminal scalar identity is
generated by local operator matching and a long-time primitive limit. -/
structure ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData
    (Index : Type*)
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTimeBasepoint :
    ProductThroatSphereNuclearShortTimeBasepointQuadraticData sphereData nuclear
  longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
    (Set.Ioi (1 : Real))
  operatorBoundary : ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
    longCutoffFilter nuclear finiteCounterterm
      shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic longTime
  familyHeatTrace_eq : ∀ parameter time,
    family.finitePartFamily.heatTrace parameter time =
      nuclear.heatTrace parameter time
  familyCounterterm_eq : ∀ parameter time,
    (family.finitePartFamily.finitePart parameter).counterterm time =
      counterterm finiteCounterterm.variation parameter time
  rawCountertermFinitePart_eq : ∀ parameter,
    (family.finitePartFamily.finitePart parameter).countertermFinitePart =
      finitePartContribution finiteCounterterm parameter
  shortTime_counterterm_eq : ∀ parameter time,
    shortTimeBasepoint.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData

/-- Forget the operator construction only after deriving the scalar Duhamel
identity. -/
def toBasepointCompatibleFinitePartAssembly
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData
        Index longCutoffFilter sphereData family nuclear) :
    ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData
      Index sphereData family nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTimeBasepoint := data.shortTimeBasepoint
  longTime := data.longTime.weighted
  familyHeatTrace_eq := data.familyHeatTrace_eq
  familyCounterterm_eq := data.familyCounterterm_eq
  rawCountertermFinitePart_eq := data.rawCountertermFinitePart_eq
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  logarithmicTrace := data.operatorBoundary.logarithmicTrace
  duhamel_integral_identity := data.operatorBoundary.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public operator-boundary basepoint checkpoint. -/
theorem product_throat_sphere_nuclear_basepoint_operator_boundary_finite_part_assembly_gate
    (Index : Type*)
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data :
      ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData
        Index longCutoffFilter sphereData family nuclear) :
    (∀ parameter,
      data.longTime.integratedOperator parameter =
        data.operatorBoundary.matchingOperator parameter) ∧
    (∀ parameter,
      ((data.operatorBoundary.renormalizedShortTime.integratedOperator parameter -
          data.operatorBoundary.finitePartOperator parameter) +
        data.longTime.integratedOperator parameter) =
          data.operatorBoundary.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      -finitePartDerivative data.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.renormalizedDuhamelTrace
              data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
              parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time) =
        data.operatorBoundary.logarithmicTrace parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        (data.operatorBoundary.logarithmicTrace parameter) parameter) := by
  refine ⟨data.operatorBoundary.longBoundaryIdentity,
    data.operatorBoundary.totalOperator_eq_logarithmicDerivative,
    data.operatorBoundary.duhamel_integral_identity, ?_⟩
  exact
    (P0EFTJanusProgramPProductThroatSphereNuclearBasepointCompatibleFinitePartAssembly4D.ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData.product_throat_sphere_nuclear_basepoint_compatible_finite_part_assembly_gate
      Index sphereData family nuclear
        data.toBasepointCompatibleFinitePartAssembly).2.2.1

end ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData

end
end P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D
end JanusFormal
