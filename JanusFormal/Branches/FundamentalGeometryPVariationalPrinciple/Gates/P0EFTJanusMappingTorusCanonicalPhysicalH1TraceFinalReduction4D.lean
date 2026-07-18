import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeEuclideanConeJacobian4D

/-!
# Final reduction of the canonical physical trace

Normal-frame reconstruction is unconditional.  Consequently the complete
physical trace follows from the exact weighted latitude pushforward.  This
file records reusable reductions from either a cone identity or chart data;
the radial--polar gate proves the cone identity without extra assumptions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1TraceFinalReduction4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
open P0EFTJanusMappingTorusPositiveLatitudeEuclideanConeJacobian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A weighted sphere formula supplies the complete latitude comparison
package. -/
def canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalLatitudeFrameEnergyComparison period hPeriod :=
  CanonicalNormalFrameReconstructionBound.combineCoarea period hPeriod
    (canonicalNormalFrameReconstructionBound period hPeriod)
    (canonicalLatitudeCoareaBoundOfWeightedMapFormula
      period hPeriod hFormula)

def canonicalPhysicalH1TraceBoundOfWeightedMapFormula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalH1TraceBoundOfLatitudeComparison period hPeriod
    (canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula
      period hPeriod hFormula)

def canonicalPhysicalH1TraceOfWeightedMapFormula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalH1TraceOfLatitudeComparison period hPeriod
    (canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula
      period hPeriod hFormula)

theorem canonicalPhysicalH1TraceOfWeightedMapFormula_agrees_on_smooth
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalH1TraceOfWeightedMapFormula period hPeriod hFormula
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  canonicalPhysicalH1TraceOfLatitudeComparison_agrees_on_smooth
    period hPeriod
    (canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula
      period hPeriod hFormula) field

theorem canonicalPhysicalH1TraceExists_of_weightedMapFormula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  canonicalPhysicalH1TraceExists_ofLatitudeComparison period hPeriod
    (canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula
      period hPeriod hFormula)

/-- The ordinary Euclidean cone identity is sufficient for the complete
physical trace. -/
def canonicalPhysicalH1TraceBoundOfEuclideanCone
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalH1TraceBoundOfWeightedMapFormula period hPeriod
    (canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone hCone)

def canonicalPhysicalH1TraceOfEuclideanCone
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalH1TraceOfWeightedMapFormula period hPeriod
    (canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone hCone)

theorem canonicalPhysicalH1TraceExists_of_euclideanCone
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  canonicalPhysicalH1TraceExists_of_weightedMapFormula period hPeriod
    (canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone hCone)

/-- API-ready local Euclidean chart data also closes the complete trace. -/
def canonicalPhysicalH1TraceBoundOfEuclideanChartCertificate
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalH1TraceBoundOfEuclideanCone period hPeriod
    (euclideanConeJacobianFormula_of_chartCertificate certificate)

theorem canonicalPhysicalH1TraceExists_of_euclideanChartCertificate
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  canonicalPhysicalH1TraceExists_of_euclideanCone period hPeriod
    (euclideanConeJacobianFormula_of_chartCertificate certificate)

end

end P0EFTJanusMappingTorusCanonicalPhysicalH1TraceFinalReduction4D
end JanusFormal
