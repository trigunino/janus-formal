import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatTraceCancellation

/-!
# Finite-part determinant of an intrinsic relative heat trace

Once the positive-time relative heat trace is intrinsic, one may renormalize
its logarithmic heat integral.  This file packages the exact remaining
short-time subtraction and long-time integrability data and constructs a
positive, nonzero relative determinant.

The definition is a real finite-part determinant.  Identification with a
complex zeta derivative and with the Quillen/Bismut--Freed determinant line is
deliberately kept as a subsequent comparison theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation

/-- Extend a positive-time heat trace by zero outside the positive half-line. -/
def positiveTimeTraceExtension
    (heatTrace : HeatTime → Real) (time : Real) : Real :=
  if hTime : 0 < time then heatTrace ⟨time, hTime⟩ else 0

@[simp]
theorem positiveTimeTraceExtension_of_pos
    (heatTrace : HeatTime → Real) {time : Real} (hTime : 0 < time) :
    positiveTimeTraceExtension heatTrace time = heatTrace ⟨time, hTime⟩ := by
  simp [positiveTimeTraceExtension, hTime]

@[simp]
theorem positiveTimeTraceExtension_of_nonpos
    (heatTrace : HeatTime → Real) {time : Real} (hTime : time ≤ 0) :
    positiveTimeTraceExtension heatTrace time = 0 := by
  simp [positiveTimeTraceExtension, not_lt.mpr hTime]

/-- Renormalization data for the logarithmic relative heat integral.

`countertermFinitePart` records the explicitly integrated finite part of the
chosen short-time counterterm.  The two integrability fields are the actual
analytic obligations: the subtracted trace near zero and the unsubtracted
relative trace at infinity. -/
structure RelativeHeatFinitePartData
    (heatTrace : HeatTime → Real) where
  counterterm : Real → Real
  countertermFinitePart : Real
  shortTimeIntegrable : IntegrableOn
    (fun time =>
      (positiveTimeTraceExtension heatTrace time - counterterm time) / time)
    (Set.Ioc (0 : Real) 1) volume
  longTimeIntegrable : IntegrableOn
    (fun time => positiveTimeTraceExtension heatTrace time / time)
    (Set.Ioi (1 : Real)) volume

/-- Subtracted short-time logarithmic integral. -/
def relativeHeatShortTimeFinitePart
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  ∫ time in Set.Ioc (0 : Real) 1,
    (positiveTimeTraceExtension heatTrace time - data.counterterm time) / time

/-- Long-time logarithmic integral. -/
def relativeHeatLongTimeIntegral
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  ∫ time in Set.Ioi (1 : Real),
    positiveTimeTraceExtension heatTrace time / time

/-- Renormalized logarithm of the relative determinant.  The sign is the
standard heat/zeta convention `log det_rel = - FP ∫ Tr_rel(t) dt/t`. -/
def relativeHeatFinitePartLogDeterminant
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  -(data.countertermFinitePart +
      relativeHeatShortTimeFinitePart data +
      relativeHeatLongTimeIntegral data)

/-- Positive finite-part relative determinant. -/
def relativeHeatFinitePartDeterminant
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  Real.exp (relativeHeatFinitePartLogDeterminant data)

/-- The finite-part determinant is strictly positive. -/
theorem relativeHeatFinitePartDeterminant_pos
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    0 < relativeHeatFinitePartDeterminant data :=
  Real.exp_pos _

/-- In particular, the determinant is nonzero. -/
theorem relativeHeatFinitePartDeterminant_ne_zero
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    relativeHeatFinitePartDeterminant data ≠ 0 :=
  ne_of_gt (relativeHeatFinitePartDeterminant_pos data)

/-- The logarithm recovers the finite-part logarithmic integral exactly. -/
theorem log_relativeHeatFinitePartDeterminant
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    Real.log (relativeHeatFinitePartDeterminant data) =
      relativeHeatFinitePartLogDeterminant data := by
  unfold relativeHeatFinitePartDeterminant
  rw [Real.log_exp]

/-- Trivial renormalization of the zero heat trace. -/
def zeroRelativeHeatFinitePartData :
    RelativeHeatFinitePartData (fun _ : HeatTime => 0) where
  counterterm := 0
  countertermFinitePart := 0
  shortTimeIntegrable := by
    simpa [positiveTimeTraceExtension] using
      (integrableOn_zero : IntegrableOn (fun _ : Real => (0 : Real))
        (Set.Ioc (0 : Real) 1))
  longTimeIntegrable := by
    simpa [positiveTimeTraceExtension] using
      (integrableOn_zero : IntegrableOn (fun _ : Real => (0 : Real))
        (Set.Ioi (1 : Real)))

@[simp]
theorem zeroRelativeHeatFinitePartLogDeterminant :
    relativeHeatFinitePartLogDeterminant zeroRelativeHeatFinitePartData = 0 := by
  simp [relativeHeatFinitePartLogDeterminant,
    relativeHeatShortTimeFinitePart, relativeHeatLongTimeIntegral,
    positiveTimeTraceExtension, zeroRelativeHeatFinitePartData]

@[simp]
theorem zeroRelativeHeatFinitePartDeterminant :
    relativeHeatFinitePartDeterminant zeroRelativeHeatFinitePartData = 1 := by
  simp [relativeHeatFinitePartDeterminant]

/-- Public finite-part determinant checkpoint. -/
theorem relative_heat_finite_part_determinant_gate
    (heatTrace : HeatTime → Real)
    (data : RelativeHeatFinitePartData heatTrace) :
    0 < relativeHeatFinitePartDeterminant data ∧
      Real.log (relativeHeatFinitePartDeterminant data) =
        relativeHeatFinitePartLogDeterminant data :=
  ⟨relativeHeatFinitePartDeterminant_pos data,
    log_relativeHeatFinitePartDeterminant data⟩

end
end P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
end JanusFormal
