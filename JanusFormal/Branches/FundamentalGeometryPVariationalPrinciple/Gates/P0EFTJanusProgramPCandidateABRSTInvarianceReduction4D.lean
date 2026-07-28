import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNonlinearGlobalBRST4D

/-!
# Exact Candidate-A nonlinear BRST invariance reduction

The global Noether gate already exposes termwise diffeomorphism invariance of
the nine exact Candidate-A blocks.  This gate joins that precise contract to
the unified nonlinear BRST packet.  Once the termwise symmetry is supplied,
exact action invariance, the Euler/Noether identity, square-zero, and boundary
stability are simultaneous theorems.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusProgramPNonlinearGlobalBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Exact reduction certificate: the only nonconstructed datum is the
termwise nine-block diffeomorphism symmetry already isolated by the global
Noether layer. -/
structure CandidateANonlinearBRSTInvarianceReduction4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismGaugeSymmetry
        period hPeriod chart) : Prop where
  actionInvariant :
    ∀ ghost parameter configuration,
      globalCandidateAActionPullback period hPeriod chart
          (globalLinearGaugeAffineTransform period hPeriod chart
            symmetry.generator (ghost, parameter) configuration) =
        globalCandidateAActionPullback period hPeriod chart configuration
  noetherIdentity :
    ∀ configuration ghost,
      globalEulerLagrangeOperator period hPeriod chart configuration
          (symmetry.generator ghost) = 0
  nonlinearSquareZero :
    ∀ packet : ProgramPNonlinearBRSTPacket period hPeriod,
      programPNonlinearBRST period hPeriod
          (programPNonlinearBRST period hPeriod packet) =
        programPNonlinearBRSTZero period hPeriod
  boundaryStable :
    ∀ packet : ProgramPNonlinearBRSTPacket period hPeriod,
      BoundaryCompatible period hPeriod packet →
        BoundaryCompatible period hPeriod
          (programPNonlinearBRST period hPeriod packet)

/-- The exact nine-block symmetry contract discharges the complete reduction
certificate without any additional analytic assumption. -/
def candidateANonlinearBRSTInvarianceReduction4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismGaugeSymmetry
        period hPeriod chart) :
    CandidateANonlinearBRSTInvarianceReduction4D
      period hPeriod chart symmetry where
  actionInvariant :=
    globalCandidateAAction_linearGauge_invariant
      period hPeriod chart symmetry
  noetherIdentity :=
    globalEuler_annihilates_diffeomorphismGauge
      period hPeriod chart symmetry
  nonlinearSquareZero :=
    programPNonlinearBRST_square_zero period hPeriod
  boundaryStable :=
    programPNonlinearBRST_boundary_stable period hPeriod

end
end P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D
end JanusFormal
