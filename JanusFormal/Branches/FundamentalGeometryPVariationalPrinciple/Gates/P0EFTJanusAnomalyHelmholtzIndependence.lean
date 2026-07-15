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

/-- Realizability by a quadratic potential in the finite three-sector model. -/
def VariationallyRealizable (theory : CandidateTheory) : Prop :=
  ∃ potential : QuadraticPotential3,
    hessianOperator potential = theory.linearizedEulerOperator

/-- In this finite model, Helmholtz admissibility is exactly realizability. -/
theorem variationally_realizable_iff_helmholtz
    (theory : CandidateTheory) :
    VariationallyRealizable theory ↔ HelmholtzAdmissible theory := by
  simpa [VariationallyRealizable, HelmholtzAdmissible] using
    helmholtz_realizability_iff theory.linearizedEulerOperator

/-- Anomaly-free but nonreciprocal candidate. -/
def anomalyFreeNonVariational : CandidateTheory :=
  { anomalyCoefficient := 0
    linearizedEulerOperator :=
      { nn := 1, nt := 1, no := 0
        tn := 0, tt := 1, trOdd := 0
        on := 0, ot := 0, oo := 1 } }

/-- Variational but anomalous candidate. -/
def variationalAnomalous : CandidateTheory :=
  { anomalyCoefficient := 1
    linearizedEulerOperator :=
      { nn := 1, nt := 0, no := 0
        tn := 0, tt := 1, trOdd := 0
        on := 0, ot := 0, oo := 1 } }

/-- Fully consistent algebraic candidate. -/
def anomalyFreeVariational : CandidateTheory :=
  { anomalyCoefficient := 0
    linearizedEulerOperator :=
      { nn := 1, nt := 0, no := 0
        tn := 0, tt := 1, trOdd := 0
        on := 0, ot := 0, oo := 1 } }

/-- Candidate failing both the anomaly and variational filters. -/
def anomalousNonVariational : CandidateTheory :=
  { anomalyCoefficient := 1
    linearizedEulerOperator :=
      { nn := 1, nt := 1, no := 0
        tn := 0, tt := 1, trOdd := 0
        on := 0, ot := 0, oo := 1 } }

/-- Anomaly cancellation does not imply Helmholtz integrability. -/
theorem anomaly_free_does_not_imply_helmholtz :
    AnomalyFree anomalyFreeNonVariational /\
      Not (HelmholtzAdmissible anomalyFreeNonVariational) := by
  constructor
  · rfl
  · intro hHelmholtz
    norm_num [HelmholtzAdmissible, FormallySelfAdjoint,
      anomalyFreeNonVariational] at hHelmholtz

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

/-- Both filters can fail on the same algebraic candidate. -/
theorem anomaly_and_helmholtz_can_both_fail :
    Not (AnomalyFree anomalousNonVariational) /\
      Not (HelmholtzAdmissible anomalousNonVariational) := by
  constructor
  · norm_num [AnomalyFree, anomalousNonVariational]
  · intro hHelmholtz
    norm_num [HelmholtzAdmissible, FormallySelfAdjoint,
      anomalousNonVariational] at hHelmholtz

/--
The four explicit candidates synthesize every Boolean truth pattern of the two
filters.  This is only a finite algebraic independence theorem for the declared
proxies; it makes no claim about the anomaly of the physical Janus theory.
-/
theorem every_filter_truth_pattern_is_realized
    (anomaly helmholtz : Bool) :
    ∃ theory : CandidateTheory,
      (AnomalyFree theory ↔ anomaly = true) /\
      (HelmholtzAdmissible theory ↔ helmholtz = true) := by
  cases anomaly <;> cases helmholtz
  · refine ⟨anomalousNonVariational, ?_, ?_⟩
    · simpa using anomaly_and_helmholtz_can_both_fail.1
    · simpa using anomaly_and_helmholtz_can_both_fail.2
  · refine ⟨variationalAnomalous, ?_, ?_⟩
    · simpa using helmholtz_does_not_imply_anomaly_free.2
    · simpa using helmholtz_does_not_imply_anomaly_free.1
  · refine ⟨anomalyFreeNonVariational, ?_, ?_⟩
    · simpa using anomaly_free_does_not_imply_helmholtz.1
    · simpa using anomaly_free_does_not_imply_helmholtz.2
  · refine ⟨anomalyFreeVariational, ?_, ?_⟩
    · simpa using anomaly_and_helmholtz_are_compatible.1
    · simpa using anomaly_and_helmholtz_are_compatible.2

/-- The same four-state synthesis stated directly with potential realizability. -/
theorem every_anomaly_variational_truth_pattern_is_realized
    (anomaly variational : Bool) :
    ∃ theory : CandidateTheory,
      (AnomalyFree theory ↔ anomaly = true) /\
      (VariationallyRealizable theory ↔ variational = true) := by
  obtain ⟨theory, hAnomaly, hHelmholtz⟩ :=
    every_filter_truth_pattern_is_realized anomaly variational
  exact ⟨theory, hAnomaly,
    (variationally_realizable_iff_helmholtz theory).trans hHelmholtz⟩

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
