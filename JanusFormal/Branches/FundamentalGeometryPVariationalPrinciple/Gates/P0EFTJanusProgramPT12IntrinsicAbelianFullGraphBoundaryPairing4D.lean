import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostPairing4D

/-! Exact pairing of the joint graph Riesz with the complete bulk + GHY
Hessian on the faithful paired Abelian smooth sector. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphBoundaryPairing4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
open P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostCore4D
open P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostPairing4D
open P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local notation "Graph" => IntrinsicAbelianFullGraph period hPeriod
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local instance graphGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Graph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod

theorem intrinsicAbelianFullGraphRiesz_eq_completeHessian
    (couplings : GlobalCandidateAActionCouplings)
    (plusEinsteinScale minusEinsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients) (first second : State) :
    inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first)) (intrinsicAbelianFullSmooth period hPeriod second) =
    intrinsicBoundaryCompleteHessian period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients
      (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings
        (intrinsicBulkSmoothPairedAbelianFields period hPeriod first))
      (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings
        (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)) :=
  (intrinsicAbelianFullGraphRiesz_smooth_pairing period hPeriod couplings first second).trans
    (intrinsicBoundaryCompleteHessian_pairedAbelian period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod first)
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)).symm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphBoundaryPairing4D
