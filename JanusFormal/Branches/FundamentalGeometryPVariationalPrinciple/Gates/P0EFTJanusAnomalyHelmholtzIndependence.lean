import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoupledSectorHelmholtzSelection

namespace JanusFormal
namespace P0EFTJanusAnomalyHelmholtzIndependence

set_option autoImplicit false

open P0EFTJanusCoupledSectorHelmholtzSelection

/-- Candidate theory carrying parity-odd anomaly data and parity-even equations. -/
structure CandidateTheory where
  anomalyCoefficient : ℤ
  linearizedEulerOperator : LinearOperator3

/-- Vanishing parity/global anomaly proxy. -/
def AnomalyFree (theory : CandidateTheory) : Prop :=
  theory.anomalyCoefficient = 0

/-- Variational/Helmholtz admissibility of the parity-even equations. -/
def HelmholtzAdmissible (theory : CandidateTheory) : Prop :=
  FormallySelfAdjoint theory.linearizedEulerOperator

/-- Anomaly-free but nonreciprocal candidate. -/
def anomalyFreeNonVariational : CandidateTheory :=
  { anomalyCoefficient := 0
    linearizedEulerOperator :=
      { nn := 1, nt := 1, no := 0
        tn := 0, tt := 1, to := 0
        on := 0, ot := 0, oo := 1 } }

/-- Variational but anomalous candidate. -/
def variationalAnomalous : CandidateTheory :=
  { anomalyCoefficient := 1
    linearizedEulerOperator :=
      { nn := 1, nt := 0, no := 0
        tn := 0, tt := 1, to := 0
        on := 0, ot := 0, oo := 1 } }

/-- Fully consistent algebraic candidate. -/
def anomalyFreeVariational : CandidateTheory :=
  { anomalyCoefficient := 0
    linearizedEulerOperator :=
      { nn := 1, nt := 0, no := 0
        tn := 0, tt := 1, to := 0
        on := 0, ot := 0, oo := 1 } }

/-- Anomaly cancellation does not imply Helmholtz integrability. -/
theorem anomaly_free_does_not_imply_helmholtz :
    AnomalyFree anomalyFreeNonVariational /\
      Not (HelmholtzAdmissible anomalyFreeNonVariational) := by
  constructor
  · rfl
  · intro hHelmholtz
    exact (by norm_num) hHelmholtz.1

/-- Helmholtz integrability does not imply anomaly cancellation. -/
theorem helmholtz_does_not_imply_anomaly_free :
    HelmholtzAdmissible variationalAnomalous /\
      Not (AnomalyFree variationalAnomalous) := by
  constructor
  · exact ⟨rfl, rfl, rfl⟩
  · norm_num [AnomalyFree, variationalAnomalous]

/-- The two constraints are jointly satisfiable. -/
theorem anomaly_and_helmholtz_are_compatible :
    AnomalyFree anomalyFreeVariational /\
      HelmholtzAdmissible anomalyFreeVariational := by
  exact ⟨rfl, ⟨rfl, rfl, rfl⟩⟩

/-- Complete two-filter status. -/
def FullyConsistent (theory : CandidateTheory) : Prop :=
  AnomalyFree theory /\ HelmholtzAdmissible theory

/-- Neither filter can replace the other. -/
theorem two_independent_filters_matrix :
    (∃ theory,
      AnomalyFree theory /\
      Not (HelmholtzAdmissible theory)) /\
    (∃ theory,
      HelmholtzAdmissible theory /\
      Not (AnomalyFree theory)) /\
    (∃ theory, FullyConsistent theory) := by
  exact ⟨
    ⟨anomalyFreeNonVariational,
      anomaly_free_does_not_imply_helmholtz⟩,
    ⟨variationalAnomalous,
      helmholtz_does_not_imply_anomaly_free⟩,
    ⟨anomalyFreeVariational,
      anomaly_and_helmholtz_are_compatible⟩⟩

/--
Program-P synthesis: P-B tests determinant-line/anomaly consistency, whereas
P-C tests variational reciprocity of the parity-even equations.  They are
logically independent and must both be imposed on the same field/ghost content.
-/
structure AnomalyHelmholtzPhysicalStatus where
  commonFieldContentDerived : Prop
  regulatorAndStatisticsFixed : Prop
  anomalyPolynomialComputed : Prop
  globalAnomalyComputed : Prop
  fullEulerOperatorDerived : Prop
  helmholtzConditionsProved : Prop
  anomalyCancellationProved : Prop
  variationalActionReconstructed : Prop
  sameCountertermSchemeUsed : Prop


def anomalyHelmholtzPhysicalClosure
    (s : AnomalyHelmholtzPhysicalStatus) : Prop :=
  s.commonFieldContentDerived /\
  s.regulatorAndStatisticsFixed /\
  s.anomalyPolynomialComputed /\
  s.globalAnomalyComputed /\
  s.fullEulerOperatorDerived /\
  s.helmholtzConditionsProved /\
  s.anomalyCancellationProved /\
  s.variationalActionReconstructed /\
  s.sameCountertermSchemeUsed

end P0EFTJanusAnomalyHelmholtzIndependence
end JanusFormal
