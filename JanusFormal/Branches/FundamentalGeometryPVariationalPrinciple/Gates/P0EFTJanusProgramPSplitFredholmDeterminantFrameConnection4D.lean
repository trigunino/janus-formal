import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSplitFredholmDeterminantFrameAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-!
# Connection on split Fredholm determinant coordinates

Let `D_red` be the zeta determinant of the invertible kernel complement and let
`k_i` be a nonzero local coordinate for the complexified named kernel volume.
The full local determinant coordinate is

`D_i = k_i D_red`.

If the reduced connection coefficient is `A_red`, the coefficient in the local
full frame is

`A_i = A_red - k_i' / k_i`.

Then `D_i' + A_i D_i = 0`.  On an overlap, with
`g_ij = k_j / k_i`, the exact gauge law is

`g_ij' + A_j g_ij = g_ij A_i`.

This is the differential form of the coordinate-level tensor-product
comparison.  The abstract complex determinant line is still not identified by
definition; the file proves the transition and connection laws that any such
identification must satisfy.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSplitFredholmDeterminantFrameConnection4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPSplitFredholmDeterminantFamily4D
open P0EFTJanusProgramPSplitFredholmDeterminantFrameAtlas4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E Index : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- A differentiable kernel-frame atlas tied to the same reduced zeta family
that supplies the split determinant coordinate. -/
structure SplitFredholmDeterminantFrameConnectionData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode]
    (Index : Type*) where
  atlas : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index
  reducedFamily : RelativeZetaDeterminantFamilyData
  reduced_agreement : ∀ parameter,
    atlas.split.reducedDeterminant parameter =
      relativeZetaDeterminantCoordinate reducedFamily parameter
  kernelFrameDerivative : Index → Real → Complex
  kernelFrame_hasDerivAt : ∀ index parameter,
    HasDerivAt (atlas.kernelFrameCoordinate index)
      (kernelFrameDerivative index parameter) parameter

namespace SplitFredholmDeterminantFrameConnectionData

/-- Ordinary derivative of one full local determinant coordinate. -/
def localDeterminantDerivative
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (index : Index) (parameter : Real) : Complex :=
  data.kernelFrameDerivative index parameter *
      relativeZetaDeterminantCoordinate data.reducedFamily parameter +
    data.atlas.kernelFrameCoordinate index parameter *
      relativeZetaDeterminantCoordinateDerivative data.reducedFamily parameter

/-- The displayed derivative is the actual derivative of the full local
coordinate. -/
theorem localDeterminant_hasDerivAt
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (index : Index) (parameter : Real) :
    HasDerivAt (data.atlas.localDeterminant index)
      (data.localDeterminantDerivative index parameter) parameter := by
  have hFrame := data.kernelFrame_hasDerivAt index parameter
  have hReduced :=
    relativeZetaDeterminantCoordinate_hasDerivAt data.reducedFamily parameter
  have hFunction : data.atlas.localDeterminant index =
      data.atlas.kernelFrameCoordinate index *
        relativeZetaDeterminantCoordinate data.reducedFamily := by
    funext current
    unfold SplitFredholmDeterminantFrameAtlasData.localDeterminant
    rw [data.reduced_agreement current]
    rfl
  rw [hFunction]
  simpa only [localDeterminantDerivative] using hFrame.mul hReduced

/-- Connection coefficient in one full Fredholm determinant frame. -/
def localConnectionCoefficient
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (index : Index) (parameter : Real) : Complex :=
  relativeZetaConnectionCoefficient data.reducedFamily parameter -
    data.kernelFrameDerivative index parameter /
      data.atlas.kernelFrameCoordinate index parameter

/-- Covariant derivative of a scalar first jet in one full determinant frame. -/
def localConnectionAt
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (index : Index) (parameter : Real)
    (value derivative : Complex) : Complex :=
  derivative + data.localConnectionCoefficient index parameter * value

/-- Every full local determinant coordinate is parallel for the transformed
connection. -/
theorem localDeterminant_parallel
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (index : Index) (parameter : Real) :
    data.localConnectionAt index parameter
        (data.atlas.localDeterminant index parameter)
        (data.localDeterminantDerivative index parameter) = 0 := by
  unfold localConnectionAt localConnectionCoefficient
    localDeterminantDerivative
    SplitFredholmDeterminantFrameAtlasData.localDeterminant
    relativeZetaConnectionCoefficient
    relativeZetaDeterminantCoordinateDerivative
  rw [data.reduced_agreement parameter]
  field_simp [data.atlas.kernelFrameCoordinate_ne_zero index parameter]
  ring

/-- Derivative of the frame transition `k_j / k_i`. -/
def transitionDerivative
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (first second : Index) (parameter : Real) : Complex :=
  (data.kernelFrameDerivative second parameter *
        data.atlas.kernelFrameCoordinate first parameter -
      data.atlas.kernelFrameCoordinate second parameter *
        data.kernelFrameDerivative first parameter) /
    (data.atlas.kernelFrameCoordinate first parameter) ^ 2

/-- The transition derivative is the actual derivative of the frame ratio. -/
theorem transition_hasDerivAt
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (first second : Index) (parameter : Real) :
    HasDerivAt (data.atlas.transition first second)
      (data.transitionDerivative first second parameter) parameter := by
  have hNumerator := data.kernelFrame_hasDerivAt second parameter
  have hDenominator := data.kernelFrame_hasDerivAt first parameter
  have hDenominatorInverse :
      HasDerivAt ((data.atlas.kernelFrameCoordinate first)⁻¹)
        (-data.kernelFrameDerivative first parameter /
          data.atlas.kernelFrameCoordinate first parameter ^ 2) parameter := by
    have hInverseF :=
      (hasFDerivAt_inv' (𝕜 := Real)
        (data.atlas.kernelFrameCoordinate_ne_zero first parameter)).comp
        parameter hDenominator
    change HasFDerivAt
      (fun current => (data.atlas.kernelFrameCoordinate first current)⁻¹)
      (ContinuousLinearMap.toSpanSingleton Real
        (-data.kernelFrameDerivative first parameter /
          data.atlas.kernelFrameCoordinate first parameter ^ 2)) parameter
    have hFunction :
        (fun current => (data.atlas.kernelFrameCoordinate first current)⁻¹) =
          Inv.inv ∘ data.atlas.kernelFrameCoordinate first := rfl
    rw [hFunction]
    have hDerivative :
        ContinuousLinearMap.toSpanSingleton Real
            (-data.kernelFrameDerivative first parameter /
              data.atlas.kernelFrameCoordinate first parameter ^ 2) =
          (-ContinuousLinearMap.mulLeftRight Real Complex
              (data.atlas.kernelFrameCoordinate first parameter)⁻¹
              (data.atlas.kernelFrameCoordinate first parameter)⁻¹).comp
            (ContinuousLinearMap.toSpanSingleton Real
              (data.kernelFrameDerivative first parameter)) := by
      ext
      simp
      ring
    rw [hDerivative]
    exact hInverseF
  have hQuotient := hNumerator.mul hDenominatorInverse
  unfold SplitFredholmDeterminantFrameAtlasData.transition
  have hDerivative :
      data.transitionDerivative first second parameter =
        data.kernelFrameDerivative second parameter *
            (data.atlas.kernelFrameCoordinate first parameter)⁻¹ +
          data.atlas.kernelFrameCoordinate second parameter *
            (-data.kernelFrameDerivative first parameter /
              data.atlas.kernelFrameCoordinate first parameter ^ 2) := by
    unfold transitionDerivative
    field_simp [data.atlas.kernelFrameCoordinate_ne_zero first parameter]
    ring
  rw [hDerivative]
  change HasDerivAt
    (data.atlas.kernelFrameCoordinate second *
      (data.atlas.kernelFrameCoordinate first)⁻¹) _ parameter
  exact hQuotient

/-- Gauge-transformation identity for the local full determinant
connections. -/
theorem transition_connection_gauge
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (first second : Index) (parameter : Real) :
    data.transitionDerivative first second parameter +
        data.localConnectionCoefficient second parameter *
          data.atlas.transition first second parameter =
      data.atlas.transition first second parameter *
        data.localConnectionCoefficient first parameter := by
  unfold transitionDerivative localConnectionCoefficient
    SplitFredholmDeterminantFrameAtlasData.transition
  field_simp [data.atlas.kernelFrameCoordinate_ne_zero first parameter,
    data.atlas.kernelFrameCoordinate_ne_zero second parameter]
  ring

/-- Gauge covariance of an arbitrary scalar first jet. -/
theorem localConnection_gauge_covariant
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index)
    (first second : Index) (parameter : Real)
    (value derivative : Complex) :
    data.localConnectionAt second parameter
        (data.atlas.transition first second parameter * value)
        (data.transitionDerivative first second parameter * value +
          data.atlas.transition first second parameter * derivative) =
      data.atlas.transition first second parameter *
        data.localConnectionAt first parameter value derivative := by
  unfold localConnectionAt
  linear_combination
    (data.transition_connection_gauge first second parameter) * value

/-- Complete connection certificate for the split Fredholm determinant atlas. -/
structure SplitFredholmDeterminantFrameConnectionCertificate
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index) :
    Prop where
  atlas : SplitFredholmDeterminantFrameAtlasData.SplitFredholmDeterminantFrameAtlasCertificate
    data.atlas
  local_derivative : ∀ index parameter,
    HasDerivAt (data.atlas.localDeterminant index)
      (data.localDeterminantDerivative index parameter) parameter
  local_parallel : ∀ index parameter,
    data.localConnectionAt index parameter
        (data.atlas.localDeterminant index parameter)
        (data.localDeterminantDerivative index parameter) = 0
  transition_derivative : ∀ first second parameter,
    HasDerivAt (data.atlas.transition first second)
      (data.transitionDerivative first second parameter) parameter
  connection_gauge : ∀ first second parameter,
    data.transitionDerivative first second parameter +
        data.localConnectionCoefficient second parameter *
          data.atlas.transition first second parameter =
      data.atlas.transition first second parameter *
        data.localConnectionCoefficient first parameter
  connection_covariant : ∀ first second parameter value derivative,
    data.localConnectionAt second parameter
        (data.atlas.transition first second parameter * value)
        (data.transitionDerivative first second parameter * value +
          data.atlas.transition first second parameter * derivative) =
      data.atlas.transition first second parameter *
        data.localConnectionAt first parameter value derivative

/-- Build the connection certificate. -/
def certificate
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index) :
    SplitFredholmDeterminantFrameConnectionCertificate data where
  atlas := data.atlas.certificate
  local_derivative := data.localDeterminant_hasDerivAt
  local_parallel := data.localDeterminant_parallel
  transition_derivative := data.transition_hasDerivAt
  connection_gauge := data.transition_connection_gauge
  connection_covariant := data.localConnection_gauge_covariant

/-- Public split Fredholm determinant connection checkpoint. -/
theorem split_fredholm_determinant_frame_connection_gate
    (operator : Real → E →L[Real] E)
    (data : SplitFredholmDeterminantFrameConnectionData operator ZeroMode Index) :
    SplitFredholmDeterminantFrameConnectionCertificate data :=
  data.certificate

end SplitFredholmDeterminantFrameConnectionData

end
end P0EFTJanusProgramPSplitFredholmDeterminantFrameConnection4D
end JanusFormal
