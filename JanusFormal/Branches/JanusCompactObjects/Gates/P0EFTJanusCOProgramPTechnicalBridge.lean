import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOFutureBimetricInterface
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalFieldBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeometricNormalJunction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

namespace JanusFormal
namespace P0EFTJanusCOProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusMappingTorusGlobalFieldBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeometricNormalJunction4D

/-- Stationarity of the geometric junction action implies the corresponding
weak normal balance on the actual embedded throat. Israel/null identification
and the physical matter source remain separate. -/
def geometric_junction_stationarity_implies_weak_balance :=
  stationary_weak_geometric_normal_balance

/-- With the explicit geometric Robin normal law, stationarity yields the
weak Robin balance. The physical identification of its coefficients remains
an input for compact-object matter. -/
def geometric_robin_law_stationarity_implies_weak_balance :=
  stationary_weak_robin_balance_of_geometricNormalLaw

/-- The actual intrinsic Lorentz metric restricts to a smooth nondegenerate
metric on the effective throat. -/
def intrinsic_compact_object_throat_metric_is_nondegenerate :=
  P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D.intrinsicGeneralLorentzMetricThroatTrace_nondegenerate

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
  geometricNormalWeakBalanceClosed : Prop
  geometricRobinWeakBalanceClosed : Prop
  intrinsicThroatMetricNondegenerateClosed : Prop
  staticEulerEquationsOpen : Prop
  signedMatterStressOpen : Prop
  junctionAndConversionLawOpen : Prop

end P0EFTJanusCOProgramPTechnicalBridge
end JanusFormal
