import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOFutureBimetricInterface
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalFieldBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

namespace JanusFormal
namespace P0EFTJanusCOProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusMappingTorusGlobalFieldBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

/-- P now constructs an unconditional finite smooth spanning tangent family on
the compact effective D8 quotient. -/
theorem compact_object_d8_tangent_frame_exists
    (period : Real) (hPeriod : period ≠ 0) :
    Nonempty (SmoothD8Frame period hPeriod) :=
  smoothD8FrameInput_closed period hPeriod

/-- P/D8 now provides the actual effective throat inclusion and proves its PT
equivariance on the same mapping-torus quotient. -/
theorem effective_throat_geometry_is_pt_equivariant
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusThroat period hPeriod) :
    fixedThroatQuotientInclusion period hPeriod
        ((effectiveThroatPT period hPeriod).act point) =
      (effectiveSpacetimePT period hPeriod).act
        (fixedThroatQuotientInclusion period hPeriod point) :=
  effectiveThroatEmbedding_pt_equivariant period hPeriod point

structure COBridgeBoundary where
  effectiveD8ThroatClosed : Prop
  throatPTEquivarianceClosed : Prop
  finiteSmoothTangentFrameClosed : Prop
  graphH1ThroatTraceAvailable : Prop
  staticEulerEquationsOpen : Prop
  signedMatterStressOpen : Prop
  junctionAndConversionLawOpen : Prop

end P0EFTJanusCOProgramPTechnicalBridge
end JanusFormal
