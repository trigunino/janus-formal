namespace JanusFormal
namespace P0EFTJanusNullWorldvolumeSpectralAudit

set_option autoImplicit false

/--
Metric and continuation inputs required before applying elliptic heat-kernel
technology to a lightlike world-volume.
-/
structure WorldvolumeSpectralMetricStatus where
  lorentzianInducedMetricDegenerate : Prop
  auxiliaryIntrinsicMetricConstructed : Prop
  auxiliaryMetricNondegenerate : Prop
  auxiliaryMetricPositiveEuclideanContinuationDerived : Prop
  wickRotationOrContourDerived : Prop
  euclideanProductMetricIdentified : Prop
  diracOperatorElliptic : Prop
  heatSemigroupTraceClass : Prop
  relationToBulkNullJunctionDerived : Prop

/-- D7 is admissible only through a nondegenerate auxiliary/Wick-rotated metric. -/
def spectralMetricAdmissible
    (s : WorldvolumeSpectralMetricStatus) : Prop :=
  s.auxiliaryIntrinsicMetricConstructed /\
  s.auxiliaryMetricNondegenerate /\
  s.auxiliaryMetricPositiveEuclideanContinuationDerived /\
  s.wickRotationOrContourDerived /\
  s.euclideanProductMetricIdentified /\
  s.diracOperatorElliptic /\
  s.heatSemigroupTraceClass /\
  s.relationToBulkNullJunctionDerived

/-- A degenerate induced metric alone is insufficient for the standard D7 heat kernel. -/
theorem null_induced_metric_without_auxiliary_geometry_blocks_d7
    (s : WorldvolumeSpectralMetricStatus)
    (hNoAuxiliary : Not s.auxiliaryIntrinsicMetricConstructed) :
    Not (spectralMetricAdmissible s) := by
  intro hAdmissible
  exact hNoAuxiliary hAdmissible.1

/-- Missing ellipticity blocks the heat-kernel construction even after choosing a metric. -/
theorem nonelliptic_operator_blocks_d7
    (s : WorldvolumeSpectralMetricStatus)
    (hNonelliptic : Not s.diracOperatorElliptic) :
    Not (spectralMetricAdmissible s) := by
  intro hAdmissible
  exact hNonelliptic hAdmissible.2.2.2.2.2.1

/-- Missing the bridge back to the Lorentzian null junction prevents physical interpretation. -/
theorem missing_null_junction_bridge_blocks_physical_d7
    (s : WorldvolumeSpectralMetricStatus)
    (hMissing : Not s.relationToBulkNullJunctionDerived) :
    Not (spectralMetricAdmissible s) := by
  intro hAdmissible
  exact hMissing hAdmissible.2.2.2.2.2.2.2

/--
The Riemannian product `S2 x S1` used in D7 must therefore be interpreted as an
auxiliary Euclidean spectral geometry, not silently as the degenerate metric
induced on a Lorentzian lightlike brane.  A complete theory must derive the
auxiliary metric and its return map to the physical null junction.
-/
structure NullToEuclideanSpectralClosureStatus where
  llBraneAuxiliaryMetricDerivedFromAction : Prop
  constraintEquationsSolved : Prop
  euclideanSectionConstructed : Prop
  productThroatMetricDerived : Prop
  operatorEllipticityProved : Prop
  determinantContourFixed : Prop
  analyticContinuationBackToLorentzianDerived : Prop
  junctionStressAndChargeMatched : Prop


def nullToEuclideanSpectralClosure
    (s : NullToEuclideanSpectralClosureStatus) : Prop :=
  s.llBraneAuxiliaryMetricDerivedFromAction /\
  s.constraintEquationsSolved /\
  s.euclideanSectionConstructed /\
  s.productThroatMetricDerived /\
  s.operatorEllipticityProved /\
  s.determinantContourFixed /\
  s.analyticContinuationBackToLorentzianDerived /\
  s.junctionStressAndChargeMatched

end P0EFTJanusNullWorldvolumeSpectralAudit
end JanusFormal
