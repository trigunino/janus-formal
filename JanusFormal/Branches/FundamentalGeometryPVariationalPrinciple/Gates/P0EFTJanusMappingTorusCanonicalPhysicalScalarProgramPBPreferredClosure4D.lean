import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialFiberCancellation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialTimePrimitive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalStandardBoundaryFinalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerCanonicalL2Operators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorStandardBoundaryProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveFinalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveStandardBoundaryFinalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothRellichTransport4D

/-!
# Preferred physical scalar Program P-B closure

The physical and elliptic regimes are now separated.

The general off-shell Lorentzian boundary-system endpoint is
`P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D`.
Its unrestricted local-divergence/cut-bulk identity is retained as an explicit
off-shell interface, not as a Program P theorem.

For Program P itself, boundary tangency derives homogeneous Dirichlet data.
On the global Euler sector the local divergence vanishes pointwise and the
cut-bulk divergence vanishes by the proved Dirichlet boundary theorem.
Therefore the exact local-divergence/cut-bulk identity is now unconditional on
the physical on-shell domain. No new Stokes or boundary axiom is introduced.

Coercivity, source inversion, unique variational minimization, Gaussian
positivity, self-adjointness and Fredholm index zero are unconditional in the
positive time-static sector derived from the unchanged scalar action.
Compact resolvent is also unconditional at every finite smooth-mode Galerkin
cutoff.

Independently, the canonical Hilbert renorming of the full physical graph
`H¹` gives an unconditional coercive graph-energy problem for every bulk `L²`
source, with a unique minimizer and positive self-adjoint bulk response.  This
is an intrinsic elliptic regulator, not a replacement for the Lorentzian
action Hessian.

Physical Rellich compactness on the full graph `H¹ → L²` space is now
unconditional: finite smooth localization, canonical/Lebesgue volume
comparison, Euclidean Rellich, extension, and exact partition reconstruction
are all proved. Consequently the intrinsic coercive bulk response is compact.
Lorentzian compact-resolvent conclusions still require the relevant
operator-specific elliptic/coercive realization; Rellich itself is no longer
an external obligation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBPreferredClosure4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarDirichletOrientedGreenStokesClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothRellichTransport4D

/-- Compatibility marker for the conditional elliptic completed-boundary route. -/
theorem canonicalPhysicalScalarProgramPBPreferredPDEClosure_available : True :=
  trivial

/-- Marker for the conditional auxiliary elliptic obligations package. -/
theorem canonicalPhysicalScalarProgramPBFinalObligations_available : True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.canonicalPhysicalScalarProgramPFinalObligations_available

/-- Unconditional coercive and variational closure on the positive static
sector of the unchanged scalar action. -/
def canonicalPhysicalScalarProgramPBStaticCoerciveVariational_certificate
    (period : Real) (hPeriod : period ≠ 0)
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticScalarEnergyH1 period hPeriod data) :=
  completed_static_scalar_coercive_variational_closure
    period hPeriod data source

/-- Unconditional compact-resolvent closure at every finite smooth static
Galerkin cutoff. -/
def canonicalPhysicalScalarProgramPBStaticGalerkinCompactResolvent_certificate
    (period : Real) (hPeriod : period ≠ 0)
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount →
      StaticGlobalScalarTest period hPeriod data) :=
  static_scalar_galerkin_compact_resolvent_closure
    period hPeriod data modes

/-- Unconditional coercive closure of the canonical full-H1 graph energy for
every physical bulk-L2 source. -/
def canonicalPhysicalScalarProgramPBIntrinsicH1CoerciveVariational_certificate
    (period : Real) (hPeriod : period ≠ 0)
    (source : CanonicalPhysicalBulkL2 period hPeriod) :=
  canonicalPhysicalScalarIntrinsicH1CoerciveVariational_certificate
    period hPeriod source

/-- Unconditional physical Rellich compactness from finite smooth chart
transport and exact partition reconstruction. -/
def canonicalPhysicalScalarProgramPBRellich_certificate
    (period : Real) (hPeriod : period ≠ 0) :=
  canonicalPhysicalScalarRellich period hPeriod

/-- The full-bulk intrinsic graph-energy response is compact without an
external Rellich hypothesis. -/
def canonicalPhysicalScalarProgramPBIntrinsicH1CompactResponse_certificate
    (period : Real) (hPeriod : period ≠ 0) :=
  canonicalPhysicalScalarIntrinsicH1BulkResponse_isCompact
    period hPeriod (canonicalPhysicalScalarRellich period hPeriod)

/-- The local Euclidean compactness part of Rellich is proved; exact
chart-measure transport and partition reconstruction imply the global result. -/
def canonicalPhysicalScalarProgramPBEuclideanRellichTransport_certificate
    (period : Real) (hPeriod : period ≠ 0)
    (transport :
      CanonicalPhysicalScalarEuclideanRellichTransportData period hPeriod) :=
  transport.certificate period hPeriod

/-- Exact Euclidean chart transport makes the unconditional graph-energy
bulk response compact. -/
def canonicalPhysicalScalarProgramPBIntrinsicH1CompactResponse_of_transport
    (period : Real) (hPeriod : period ≠ 0)
    (transport :
      CanonicalPhysicalScalarEuclideanRellichTransportData period hPeriod) :=
  canonicalPhysicalScalarIntrinsicH1BulkResponse_isCompact
    period hPeriod (transport.rellich period hPeriod)

/-- Marker for the preferred conditional Lorentzian Green/boundary interface. -/
theorem canonicalPhysicalScalarProgramPBPreferredLorentzianBoundaryClosure_available :
    True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D.CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData.lorentzianBoundaryClosure_interface_available

/-- The unrestricted off-shell Green interface exists exactly when its
unrestricted local-divergence input exists. -/
theorem canonicalPhysicalScalarProgramPBPreferredGreen_nonempty_iff
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real) :
    Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
          period hPeriod massSquared) ↔
      Nonempty
        (CanonicalPhysicalScalarCanonicalLocalDivergenceData
          period hPeriod massSquared) :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData.nonempty_iff_canonicalLocalDivergenceData
    period hPeriod

/-- With wave naturality discharged, the unrestricted off-shell Green frontier
is exactly the displayed universal local-divergence/cut-bulk identity. -/
theorem canonicalPhysicalScalarProgramPBPreferredGreen_nonempty_iff_stokes
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real) :
      Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
          period hPeriod massSquared) ↔
      ∀ field test :
          P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D.SmoothScalarField
            period hPeriod,
        (∫ parameter,
          canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 *
          P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
            period hPeriod massSquared field test Set.univ :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData.nonempty_iff_localDivergence_integral_eq_cutBulk
    period hPeriod

/-- The oriented Green--Stokes obstruction is closed unconditionally on the
preferred homogeneous Dirichlet boundary domain. -/
def canonicalPhysicalScalarProgramPBPreferredDirichletGreenStokes_certificate
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real) :=
  canonicalPhysicalScalarDirichletOrientedGreenStokesClosure_certificate
    period hPeriod massSquared

/-- On the actual Program P tangent domain, homogeneous Dirichlet data and
the measured oriented Green--Stokes closure are derived rather than assumed. -/
def canonicalPhysicalScalarProgramPBPreferredBoundaryTangentMeasuredGreenStokes_certificate :=
  programPBoundaryTangents_measuredGreenStokes_certificate

/-- Metric Green--Stokes closure for Euler components of actual Program P
boundary tangents, with no independent boundary hypothesis. -/
def canonicalPhysicalScalarProgramPBPreferredBoundaryTangentMetricGreenStokes_certificate :=
  programPBoundaryTangents_metricGreenStokes_certificate

/-- Exact local-divergence/cut-bulk closure on the actual Program P Dirichlet
Euler sector, with no external Green--Stokes input. -/
def canonicalPhysicalScalarProgramPBPreferredBoundaryTangentLocalDivergenceCutBulk_certificate :=
  programPBoundaryTangents_localDivergence_eq_cutBulk

/-- Preferred closure now means the safe Lorentzian Green/boundary endpoint. -/
theorem canonicalPhysicalScalarProgramPBPreferredClosure_available : True :=
  canonicalPhysicalScalarProgramPBPreferredLorentzianBoundaryClosure_available

/-- Explicit marker for the optional elliptic/coercive compatibility branch. -/
theorem canonicalPhysicalScalarProgramPBEllipticCoerciveCompatibility_available :
    True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.canonicalPhysicalScalarProgramPEllipticCoerciveFinalObligations_available

/-- The legacy positive-square endpoint factors through direct coercivity. -/
theorem canonicalPhysicalScalarProgramPBExternalPositiveCompatibility_available :
    True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D.canonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure_available

/-- Marker for the periodic-time-primitive final endpoint. -/
theorem canonicalPhysicalScalarProgramPBTimePrimitiveClosure_available : True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveFinalClosure4D.canonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveFinalClosure_available

/-- The former universal-transport endpoint has no data for a nonzero period. -/
theorem canonicalPhysicalScalarProgramPBTransportedNormalClosure_unavailable
    (period : Real) (hPeriod : period ≠ 0) :
    ¬ Nonempty (CanonicalLatitudeNormalToHalfCollarTransportData period) :=
  analytical_not_nonempty_of_period_ne_zero period hPeriod

/-- The corrected weighted transport has the required factor-two pushforward. -/
theorem canonicalPhysicalScalarProgramPBWeightedTransport_map
    (period : Real) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) • canonicalLatitudeCollarMeasure period :=
  map_canonicalLatitudeCorrectedCauchyJetProductMeasure period

/-- Marker for the corrected weighted transported-normal Green route. -/
theorem canonicalPhysicalScalarProgramPBWeightedTransportedNormalGreen_available :
    True :=
  trivial

/-- Marker for the local-divergence weighted Green route. -/
theorem canonicalPhysicalScalarProgramPBWeightedTransportedGlobalGreen_available :
    True :=
  trivial

/-- Compatibility marker for the conditional coercive final endpoint. -/
theorem canonicalPhysicalScalarProgramPBWeightedTransportedNormalFinalClosure_available :
    True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D.canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure_available

/-- Marker for the safe smooth Dirichlet, Neumann and Robin families. -/
theorem canonicalPhysicalScalarProgramPBPreferredStandardBoundaries_available : True :=
  canonicalPhysicalScalarProgramPBPreferredLorentzianBoundaryClosure_available

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBPreferredClosure4D
end JanusFormal
