import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameTransport4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportLaws4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Naturality square between cokernel/kernel duality and family transport. -/
theorem cokernelTopKernelTopEquiv_transport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (value : data.cokernelTop first) :
    cokernelTopKernelTopEquiv data second
        (data.cokernelTopTransport first second value) =
      data.kernelTopTransport first second
        (cokernelTopKernelTopEquiv data first value) := by
  change
    exteriorPower.map determinantDegree
        (data.cokernelKernelEquiv second).toLinearMap
      (exteriorPower.map determinantDegree
        (data.cokernelTransport first second).toLinearMap value) =
      exteriorPower.map determinantDegree
        (data.kernels.kernelTransport first second).toLinearMap
      (exteriorPower.map determinantDegree
        (data.cokernelKernelEquiv first).toLinearMap value)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  congr 1
  apply LinearMap.ext
  intro current
  exact data.cokernelKernelEquiv_transport first second current

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameTransport4D
end JanusFormal
