import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Reality of the Mellin zeta derivative from its real-axis germ

A standalone reference zeta function is real on the real spectral axis wherever
it is defined by the Mellin transform of a real heat trace.  Once analytic
continuation connects that real interval to the origin, the continued function
is locally real on the real axis near zero.

This file isolates the final differential consequence.  If

```text
Im (zeta x) = 0
```

for real `x` in a neighborhood of zero, then the imaginary part of
`zeta'(0)` vanishes.  Mathlib's `HasDerivAt.comp_ofReal` restricts the complex
derivative to the real axis with the same complex derivative; composition with
`Complex.imCLM` and uniqueness of the real derivative finish the proof.

Thus reality of the regularized derivative is no longer an independent scalar
field.  The remaining input is the geometric/analytic real-axis germ.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- One continuation whose restriction to the real spectral axis is locally
real near zero. -/
structure RelativeHeatMellinZetaRealAxisRealityData
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) where
  eventually_im_zero :
    (fun spectral : Real => (continuation.zeta (spectral : Complex)).im) =ᶠ[𝓝 0]
      (fun _ : Real => 0)

namespace RelativeHeatMellinZetaRealAxisRealityData

/-- The complex derivative restricts to the real axis with the same
Complex-valued derivative. -/
theorem hasDerivAt_realAxis
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (_data : RelativeHeatMellinZetaRealAxisRealityData continuation) :
    HasDerivAt
      (fun spectral : Real => continuation.zeta (spectral : Complex))
      continuation.derivativeAtZero 0 :=
  continuation.hasDerivAt_zero.comp_ofReal

/-- The imaginary part of the real-axis restriction has derivative equal to
the imaginary part of the complex derivative at zero. -/
theorem hasDerivAt_realAxis_im
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaRealAxisRealityData continuation) :
    HasDerivAt
      (fun spectral : Real => (continuation.zeta (spectral : Complex)).im)
      continuation.derivativeAtZero.im 0 := by
  have hComposition :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 data.hasDerivAt_realAxis
  simpa [Function.comp_def] using hComposition

/-- A locally zero real function has derivative zero. -/
theorem hasDerivAt_realAxis_im_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaRealAxisRealityData continuation) :
    HasDerivAt
      (fun spectral : Real => (continuation.zeta (spectral : Complex)).im)
      0 0 := by
  have hConstant : HasDerivAt (fun _ : Real => (0 : Real)) 0 0 :=
    hasDerivAt_const 0 0
  exact hConstant.congr_of_eventuallyEq data.eventually_im_zero

/-- Reality of the regularized zeta derivative follows from the real-axis
germ. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaRealAxisRealityData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.hasDerivAt_realAxis_im.unique data.hasDerivAt_realAxis_im_zero

/-- Public real-axis reality checkpoint. -/
theorem relative_heat_mellin_zeta_real_axis_reality_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaRealAxisRealityData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.derivativeAtZero_im_eq_zero

end RelativeHeatMellinZetaRealAxisRealityData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D
end JanusFormal
