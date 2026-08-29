import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanGlobalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNonlinearGlobalBRST4D

/-!
# Canonical tensorial Cartan BRST data

The canonical Maxwell and metric Cartan actions jointly realize the existing
tensorial representation interface.  Its algebraic coadjoint-antifield BRST
certificate follows without introducing a geometric or integrated dual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCanonicalTensorialCartanBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPNonlinearGlobalBRST4D
open P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical Cartan data in both intrinsic tensorial sectors. -/
def canonicalTensorialCartanActionData :
    TensorialCartanActionData period hPeriod where
  gauge := gaugePotentialCartanActionData period hPeriod
  metric := symmetricTensorCartanActionData period hPeriod

/-- Canonical Maxwell/metric smooth-ghost Lie representations. -/
def canonicalTensorialInfinitesimalLieActionData :
    TensorialInfinitesimalLieActionData period hPeriod :=
  (canonicalTensorialCartanActionData period hPeriod)
    |>.toTensorialInfinitesimalLieActionData period hPeriod

/-- Algebraic coadjoint-antifield BRST closure for the canonical tensorial
actions.  No geometric or integrated antifield dual is asserted. -/
def canonicalTensorialCoadjointAntifieldBRSTCertificate4D :
    TensorialCoadjointAntifieldBRSTCertificate4D period hPeriod
      (canonicalTensorialInfinitesimalLieActionData period hPeriod) :=
  programP_tensorial_coadjoint_antifield_gate period hPeriod
    (canonicalTensorialInfinitesimalLieActionData period hPeriod)

end

end P0EFTJanusProgramPCanonicalTensorialCartanBRST4D
end JanusFormal
