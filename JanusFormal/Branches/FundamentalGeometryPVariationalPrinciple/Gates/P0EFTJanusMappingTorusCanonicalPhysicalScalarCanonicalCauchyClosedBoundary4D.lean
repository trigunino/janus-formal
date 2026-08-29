import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetSquaredGraphBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D

/-!
# Canonical Cauchy-closed physical boundary data

The value and normal boundary cores are fixed to the canonical smooth periodic
and antiperiodic types.  The explicit global Cauchy extension is fixed by the
latitude jet.  Its graph bound is supplied in the natural squared-energy form.

Thus the boundary-triple interface is reduced to:

* canonical Green-core geometry;
* squared bulk and Euler-residual estimates for the explicit extension;
* squared Gårding;
* higher normal regularity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedBoundary4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetSquaredGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical physical boundary data with squared extension estimates. -/
structure CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
    (massSquared : Real) where
  core : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
    period hPeriod massSquared
  garding : core.greenCore.SquaredGardingEstimate period hPeriod
  normalRegularity : core.greenCore.NormalRegularityData
    period hPeriod (Regularity := Regularity)
  extensionEstimate :
    core.toCauchyJetGeometricData.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod

namespace CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData

/-- Conversion to the general Cauchy-closed boundary package. -/
def toCauchyClosedBoundaryData
    (boundaryData : CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared (ValueCore period) (NormalCore period)
      (Regularity := Regularity) where
  cauchy := boundaryData.core.toCauchyJetGeometricData
  garding := boundaryData.garding
  normalRegularity := boundaryData.normalRegularity
  extensionEstimate := boundaryData.extensionEstimate.toComponentGraphEstimateData

/-- Correct completed physical boundary triple. -/
def triple
    (boundaryData : CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :=
  boundaryData.toCauchyClosedBoundaryData.triple

/-- Completed physical boundary inputs. -/
def completedInputs
    (boundaryData : CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :=
  boundaryData.toCauchyClosedBoundaryData.completedInputs

/-- Canonical Cauchy-closed boundary certificate. -/
theorem certificate
    (boundaryData : CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      boundaryData.core.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          boundaryData.core.greenCore.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.core.greenCore.core
          boundaryData.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
            |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
            |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  ⟨boundaryData.core.boundaryDensity.valueDense,
    boundaryData.core.boundaryDensity.normalDense,
    P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D.canonicalPhysicalScalarMinimalCoreDense
      period hPeriod boundaryData.core.greenCore,
    boundaryData.triple.inclusion_injective,
    boundaryData.toCauchyClosedBoundaryData.extensionEstimate
      |>.completedBoundaryTrace_surjective
        (boundaryData.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
          |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
          |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound)⟩

end CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedBoundary4D
end JanusFormal
