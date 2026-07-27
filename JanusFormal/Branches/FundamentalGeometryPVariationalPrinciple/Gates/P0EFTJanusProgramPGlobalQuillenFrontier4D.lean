import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalRegulatorFrontier4D
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleQuillenMetricFlatConnection

/-!
# Exact frontier of the global Quillen problem

The normalized circle Fredholm family has an actual determinant line, an
explicit Hermitian metric, a compatible flat connection, unitary closed
holonomy and exact endpoint clutching.

This is not `QUILLEN-GLOBAL-01`: no theorem yet identifies this Fourier-circle
model with the Quillen/Bismut--Freed line of the full geometric Janus Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalQuillenFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleDeterminantTopologicalBundle
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleQuillenMetricFlatConnection

/-- Complete geometric data currently proved for the circle determinant
family. -/
structure ProgramPGlobalQuillenFrontierCertificate4D (fold : Fold) where
  quotientLineRankOne :
    ∀ holonomy : CircleHolonomyQuotient,
      Module.finrank Complex (CircleDeterminantQuotientFiber holonomy) = 1
  connectionFlat :
    circleQuillenConnectionCurvature fold = fun _ _ => 0
  closedHolonomyNonzero :
    circleQuillenClosedHolonomy fold ≠ 0
  closedHolonomyUnitary :
    ‖circleQuillenClosedHolonomy fold‖ = 1
  parallelTransportIsometry :
    ∀ first second : Real, ∀ value : Complex,
      circleQuillenCoordinateNormSq fold second
          (circleQuillenParallelTransport fold first second value) =
        circleQuillenCoordinateNormSq fold first value
  endpointClutching :
    ∀ value : CircleDeterminantFiber fold unitCircleTwist,
      circleUnitEndpointDescent fold value =
        circlePeriodicEndpointDescent fold
          (circleLargeGaugeDeterminantTransition fold value)

def programPGlobalQuillenFrontierCertificate4D (fold : Fold) :
    ProgramPGlobalQuillenFrontierCertificate4D fold where
  quotientLineRankOne :=
    circleDeterminantQuotientFiber_finrank_one
  connectionFlat :=
    circleQuillenConnection_is_flat fold
  closedHolonomyNonzero :=
    circleQuillenClosedHolonomy_ne_zero fold
  closedHolonomyUnitary :=
    circleQuillenClosedHolonomy_norm_one fold
  parallelTransportIsometry :=
    circleQuillenParallelTransport_isometry fold
  endpointClutching :=
    circleEndpointDescent_clutching fold

theorem global_quillen_frontier_gate (fold : Fold) :
    Nonempty (ProgramPGlobalQuillenFrontierCertificate4D fold) :=
  ⟨programPGlobalQuillenFrontierCertificate4D fold⟩

end
end P0EFTJanusProgramPGlobalQuillenFrontier4D
end JanusFormal
