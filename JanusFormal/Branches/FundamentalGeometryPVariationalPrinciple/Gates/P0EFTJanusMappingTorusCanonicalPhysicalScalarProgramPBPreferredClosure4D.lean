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

/-!
# Preferred physical scalar Program P-B closure

The physical and elliptic regimes are now separated.

The preferred Lorentzian endpoint is
`P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D`.
The intrinsic wave is now canonical; its sole remaining geometric input is the
local-divergence/cut-bulk identity.  The weighted cancellation is derived.  It
constructs the dense Green core, the exact physical Euler/Green identity and
symmetric smooth Dirichlet, Neumann and Robin realizations.  It does not assume
elliptic coercivity or bounded tangential residual maps on boundary `L²`.

Compact resolvent, semibounded spectrum, variational minimization and Gaussian
positivity remain available only through the explicitly conditional auxiliary
elliptic/coercive package in
`P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D`.
Those conclusions are no longer advertised as consequences of the Lorentzian
wave operator.
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

/-- Compatibility marker for the conditional elliptic completed-boundary route. -/
theorem canonicalPhysicalScalarProgramPBPreferredPDEClosure_available : True :=
  trivial

/-- Marker for the conditional auxiliary elliptic obligations package. -/
theorem canonicalPhysicalScalarProgramPBFinalObligations_available : True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.canonicalPhysicalScalarProgramPFinalObligations_available

/-- Marker for the preferred conditional Lorentzian Green/boundary interface. -/
theorem canonicalPhysicalScalarProgramPBPreferredLorentzianBoundaryClosure_available :
    True :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D.CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData.lorentzianBoundaryClosure_interface_available

/-- The preferred Lorentzian Green input exists exactly when the canonical
local-divergence input exists. -/
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

/-- With wave naturality discharged, the preferred Green frontier is exactly
the displayed local-divergence/cut-bulk identity. -/
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
