import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetIntrinsicLeviCivita4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : ℝ) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- A global Levi--Civita connection presented on the genuine holonomic atlas.
The local objects are metric-compatible torsion-free connection jets, their
coefficients are smooth, and their overlap law is the full affine Christoffel
law with the second derivative of the coordinate transition. -/
structure GlobalHolonomicLeviCivitaConnection
    (metric : SmoothGeneralLorentzMetric period hPeriod) where
  localJet :
    SmoothHolonomicFrameChart4 period hPeriod →
      Vector4 → MetricCompatibleTorsionFreeConnectionJet4
  localJet_eq : ∀ patch coordinate,
    localJet patch coordinate =
      localLeviCivitaConnectionJet period hPeriod metric patch coordinate
  christoffel_contDiff : ∀ patch upper first second,
    ContDiff ℝ ∞ (fun coordinate =>
      (localJet patch coordinate).christoffel upper first second)
  overlap : ∀ firstPatch secondPatch firstCoordinate secondCoordinate
      (samePoint : firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate),
    HolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate

/-- The intrinsic quotient metric constructs the global holonomic
Levi--Civita connection; no overlap datum is supplied by the caller. -/
def intrinsicGlobalHolonomicLeviCivitaConnection :
    GlobalHolonomicLeviCivitaConnection period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) where
  localJet :=
    localLeviCivitaConnectionJet period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
  localJet_eq := by
    intro patch coordinate
    rfl
  christoffel_contDiff := by
    intro patch upper first second
    exact localLeviCivitaChristoffel_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch upper first second
  overlap := by
    intro firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    exact canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint

/-- Exact local coefficient of the constructed global connection. -/
@[simp]
theorem intrinsicGlobalHolonomicLeviCivitaConnection_christoffel
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper first second : Index4) :
    ((intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
      patch coordinate).christoffel upper first second =
      localLeviCivitaChristoffel period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate upper first second :=
  rfl

/-- Torsion freeness is inherited pointwise from the actual Levi--Civita jet. -/
theorem intrinsicGlobalHolonomicLeviCivitaConnection_torsionFree
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper first second : Index4) :
    ((intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
      patch coordinate).christoffel upper first second =
      ((intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
        patch coordinate).christoffel upper second first :=
  (intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
    patch coordinate |>.torsionFree upper first second

/-- Metric compatibility is inherited pointwise from the actual
Levi--Civita jet. -/
theorem intrinsicGlobalHolonomicLeviCivitaConnection_metricCompatible
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localMetricDerivative period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate derivative first second =
      (∑ upper : Index4,
        ((intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
            patch coordinate).christoffel upper derivative first *
          localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch upper second coordinate) +
        ∑ upper : Index4,
          ((intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
              patch coordinate).christoffel upper derivative second *
            localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch first upper coordinate := by
  exact (intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod).localJet
    patch coordinate |>.metricCompatible derivative first second

/-- One bundled certificate closes the intrinsic-transversality and global
Levi--Civita substage required by the physical second-jet carrier. -/
structure PhysicalSecondJetIntrinsicLeviCivitaCertificate where
  hasNoTangentialRadical :
    HasNoTangentialRadical period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
  throatMetricNondegenerate :
    ThroatTensorIsNondegenerate period hPeriod
      (generalLorentzMetricThroatTrace period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod))
  connection :
    GlobalHolonomicLeviCivitaConnection period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
  connection_eq :
    connection = intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod

/-- Canonical inhabitant built entirely from the intrinsic quotient metric and
its genuine holonomic transition maps. -/
def physicalSecondJetIntrinsicLeviCivitaCertificate :
    PhysicalSecondJetIntrinsicLeviCivitaCertificate period hPeriod where
  hasNoTangentialRadical :=
    intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical period hPeriod
  throatMetricNondegenerate :=
    intrinsicGeneralLorentzMetricThroatTrace_nondegenerate period hPeriod
  connection := intrinsicGlobalHolonomicLeviCivitaConnection period hPeriod
  connection_eq := rfl

end

end P0EFTJanusPhysicalSecondJetIntrinsicLeviCivita4D
end JanusFormal
