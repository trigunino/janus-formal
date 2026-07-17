import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

/-!
# Overlap compatibility for local Levi--Civita and scalar jets

The local constructions only consume the metric first jet and the scalar
second jet.  This gate proves that two supplied holonomic patches give exactly
the same Levi--Civita connection, scalar Euler residual, raised gradient and
stress divergence whenever those finite jets agree on an overlap point.

Thus the remaining global gluing obligation is reduced to the coordinate
transition theorem asserting these tensorial jet equalities for the real
quotient atlas.  No such transition theorem is assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Exact first-jet compatibility consumed by the local Levi--Civita
construction at a pair of representatives of one overlap point. -/
structure LocalMetricFirstJetAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  metricMatrix_eq :
    localMetricMatrix period hPeriod metric firstPatch firstCoordinate =
      localMetricMatrix period hPeriod metric secondPatch secondCoordinate
  metricDerivative_eq :
    localMetricDerivative period hPeriod metric firstPatch firstCoordinate =
      localMetricDerivative period hPeriod metric secondPatch secondCoordinate

theorem localLeviCivitaChristoffel_eq_of_firstJetAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localLeviCivitaChristoffel period hPeriod metric firstPatch firstCoordinate =
      localLeviCivitaChristoffel
        period hPeriod metric secondPatch secondCoordinate := by
  funext upper first second
  unfold localLeviCivitaChristoffel leviCivitaChristoffel
  simp only [localFixedSignMetric]
  rw [agreement.metricMatrix_eq, agreement.metricDerivative_eq]

/-- Exact scalar second-jet compatibility at the same overlap point. -/
structure LocalScalarSecondJetAgreement
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  field_eq :
    localScalarRepresentative period hPeriod field firstPatch firstCoordinate =
      localScalarRepresentative period hPeriod field secondPatch secondCoordinate
  gradient_eq :
    localScalarGradient period hPeriod field firstPatch firstCoordinate =
      localScalarGradient period hPeriod field secondPatch secondCoordinate
  partialGradient_eq :
    localScalarPartialGradient period hPeriod field firstPatch firstCoordinate =
      localScalarPartialGradient period hPeriod field secondPatch secondCoordinate

private theorem coordinateScalarJet2_ext
    (first second : CoordinateScalarJet2)
    (hField : first.field = second.field)
    (hGradient : first.gradient = second.gradient)
    (hPartialGradient : first.partialGradient = second.partialGradient) :
    first = second := by
  cases first with
  | mk firstField firstGradient firstPartial firstSymmetric =>
      cases second with
      | mk secondField secondGradient secondPartial secondSymmetric =>
          dsimp at hField hGradient hPartialGradient
          subst secondField
          subst secondGradient
          subst secondPartial
          rfl

private theorem covariantScalarJet2_ext
    (first second : CovariantScalarJet2)
    (hField : first.field = second.field)
    (hGradient : first.gradient = second.gradient)
    (hHessian : first.hessian = second.hessian) :
    first = second := by
  cases first with
  | mk firstField firstGradient firstHessian firstSymmetric =>
      cases second with
      | mk secondField secondGradient secondHessian secondSymmetric =>
          dsimp at hField hGradient hHessian
          subst secondField
          subst secondGradient
          subst secondHessian
          rfl

theorem localCoordinateScalarJet_eq_of_secondJetAgreement
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCoordinateScalarJet
        period hPeriod field firstPatch firstCoordinate =
      localCoordinateScalarJet
        period hPeriod field secondPatch secondCoordinate := by
  apply coordinateScalarJet2_ext
  · exact agreement.field_eq
  · exact agreement.gradient_eq
  · exact agreement.partialGradient_eq

theorem localCovariantScalarJet_eq_of_overlap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (metricAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (scalarAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCovariantScalarJet
        period hPeriod metric firstPatch field firstCoordinate =
      localCovariantScalarJet
        period hPeriod metric secondPatch field secondCoordinate := by
  apply covariantScalarJet2_ext
  · exact scalarAgreement.field_eq
  · exact scalarAgreement.gradient_eq
  · ext first second
    unfold localCovariantScalarJet coordinateScalarJetNormalForm
      coordinateCovariantHessian localCoordinateScalarJet
    simp only [localLeviCivitaConnectionJet_christoffel]
    rw [scalarAgreement.partialGradient_eq,
      scalarAgreement.gradient_eq,
      localLeviCivitaChristoffel_eq_of_firstJetAgreement
        period hPeriod metric firstPatch secondPatch
        firstCoordinate secondCoordinate metricAgreement]

theorem localSmoothScalarEulerResidual_eq_of_overlap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (metricAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (scalarAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarEulerResidual period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarEulerResidual period hPeriod metric secondPatch field
        massSquared source secondCoordinate := by
  unfold localSmoothScalarEulerResidual covariantScalarStressEulerResidual
    covariantScalarJetWave
  simp only [localFixedSignMetric]
  rw [metricAgreement.metricMatrix_eq, scalarAgreement.field_eq,
    localCovariantScalarJet_eq_of_overlap
      period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate metricAgreement scalarAgreement]

theorem localSmoothScalarRaisedGradient_eq_of_overlap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (metricAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (scalarAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarRaisedGradient period hPeriod metric firstPatch field
        firstCoordinate =
      localSmoothScalarRaisedGradient period hPeriod metric secondPatch field
        secondCoordinate := by
  unfold localSmoothScalarRaisedGradient covariantScalarJetRaisedGradient
  simp only [localFixedSignMetric]
  rw [metricAgreement.metricMatrix_eq,
    localCovariantScalarJet_eq_of_overlap
      period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate metricAgreement scalarAgreement]

/-- The realized stress divergence is independent of the local representative
once the finite metric/scalar jets agree. -/
theorem localSmoothScalarStressDivergence_eq_of_overlap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (metricAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (scalarAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarStressDivergence period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarStressDivergence period hPeriod metric secondPatch field
        massSquared source secondCoordinate := by
  funext index
  rw [localSmoothScalarStressDivergence_apply,
    localSmoothScalarStressDivergence_apply,
    localSmoothScalarEulerResidual_eq_of_overlap
      period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate massSquared source
      metricAgreement scalarAgreement,
    localSmoothScalarRaisedGradient_eq_of_overlap
      period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate metricAgreement scalarAgreement]

end

end P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D
end JanusFormal
