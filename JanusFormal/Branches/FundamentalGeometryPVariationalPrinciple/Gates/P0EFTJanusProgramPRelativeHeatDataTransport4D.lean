import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Transport relative heat data across equality of heat traces

Finite-part and Mellin-continuation packets are dependently typed by the
positive-time heat-trace function.  Geometric arguments, notably unitary
conjugation, naturally produce an equality between two trace functions rather
than definitional equality.

This file transports the existing certificates through such an equality.  The
counterterm, convergence abscissa, zeta function, derivative at zero and all
analytic estimates are unchanged.  Their determinant values are preserved
exactly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatDataTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

end
end P0EFTJanusProgramPRelativeHeatDataTransport4D
namespace P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
namespace RelativeHeatFinitePartData

set_option autoImplicit false
open P0EFTJanusCircleDiracHeatTraceCancellation

/-- Reinterpret finite-part data through equality of the heat trace. -/
def transportHeatTrace
    {first second : HeatTime → Real}
    (data : RelativeHeatFinitePartData first)
    (hTrace : first = second) :
    RelativeHeatFinitePartData second := by
  cases hTrace
  exact data

@[simp]
theorem transportHeatTrace_counterterm
    {first second : HeatTime → Real}
    (data : RelativeHeatFinitePartData first)
    (hTrace : first = second) :
    (data.transportHeatTrace hTrace).counterterm = data.counterterm := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_countertermFinitePart
    {first second : HeatTime → Real}
    (data : RelativeHeatFinitePartData first)
    (hTrace : first = second) :
    (data.transportHeatTrace hTrace).countertermFinitePart =
      data.countertermFinitePart := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_logDeterminant
    {first second : HeatTime → Real}
    (data : RelativeHeatFinitePartData first)
    (hTrace : first = second) :
    relativeHeatFinitePartLogDeterminant
        (data.transportHeatTrace hTrace) =
      relativeHeatFinitePartLogDeterminant data := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_determinant
    {first second : HeatTime → Real}
    (data : RelativeHeatFinitePartData first)
    (hTrace : first = second) :
    relativeHeatFinitePartDeterminant
        (data.transportHeatTrace hTrace) =
      relativeHeatFinitePartDeterminant data := by
  cases hTrace
  rfl

end RelativeHeatFinitePartData
end P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

namespace P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
namespace RelativeHeatMellinZetaContinuationData

set_option autoImplicit false
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- Reinterpret one Mellin continuation through equality of its heat trace. -/
def transportHeatTrace
    {first second : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData first}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    RelativeHeatMellinZetaContinuationData
      (finitePart.transportHeatTrace hTrace) := by
  cases hTrace
  exact continuation

@[simp]
theorem transportHeatTrace_convergenceAbscissa
    {first second : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData first}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    (continuation.transportHeatTrace hTrace).convergenceAbscissa =
      continuation.convergenceAbscissa := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_zeta
    {first second : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData first}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    (continuation.transportHeatTrace hTrace).zeta = continuation.zeta := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_derivativeAtZero
    {first second : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData first}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    (continuation.transportHeatTrace hTrace).derivativeAtZero =
      continuation.derivativeAtZero := by
  cases hTrace
  rfl

@[simp]
theorem transportHeatTrace_zetaDeterminant
    {first second : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData first}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    relativeHeatMellinZetaDeterminant
        (continuation.transportHeatTrace hTrace) =
      relativeHeatMellinZetaDeterminant continuation := by
  cases hTrace
  rfl

end RelativeHeatMellinZetaContinuationData
end P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

namespace P0EFTJanusProgramPRelativeHeatDataTransport4D

set_option autoImplicit false
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- Public dependent-data transport checkpoint. -/
theorem relative_heat_data_transport_gate
    {first second : HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData first)
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (hTrace : first = second) :
    relativeHeatFinitePartLogDeterminant
        (finitePart.transportHeatTrace hTrace) =
      relativeHeatFinitePartLogDeterminant finitePart ∧
    (continuation.transportHeatTrace hTrace).zeta = continuation.zeta ∧
    (continuation.transportHeatTrace hTrace).derivativeAtZero =
      continuation.derivativeAtZero ∧
    relativeHeatMellinZetaDeterminant
        (continuation.transportHeatTrace hTrace) =
      relativeHeatMellinZetaDeterminant continuation :=
  ⟨finitePart.transportHeatTrace_logDeterminant hTrace,
    continuation.transportHeatTrace_zeta hTrace,
    continuation.transportHeatTrace_derivativeAtZero hTrace,
    continuation.transportHeatTrace_zetaDeterminant hTrace⟩

end P0EFTJanusProgramPRelativeHeatDataTransport4D
end JanusFormal
