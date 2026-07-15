import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoupledSectorHelmholtzSelection

namespace JanusFormal
namespace P0EFTJanusParentBulkHelmholtzReciprocity

set_option autoImplicit false

open P0EFTJanusCoupledSectorHelmholtzSelection

/--
One quadratic bulk mode coupled to the two PT-even throat sectors.  This is the
finite-dimensional Schur-complement model of a Dirichlet-to-Neumann reduction.
-/
structure ParentBulkTwoSectorData where
  bulkCoefficient : ℝ
  bulkToNormal : ℝ
  bulkToTrace : ℝ
  boundaryNormal : ℝ
  boundaryMixing : ℝ
  boundaryTrace : ℝ
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

/-- Parent bulk-plus-boundary action. -/
noncomputable def parentAction
    (data : ParentBulkTwoSectorData)
    (bulk normal trace : ℝ) : ℝ :=
  data.bulkCoefficient * bulk ^ 2 / 2 +
    bulk * (data.bulkToNormal * normal +
      data.bulkToTrace * trace) +
    data.boundaryNormal * normal ^ 2 / 2 +
    data.boundaryMixing * normal * trace +
    data.boundaryTrace * trace ^ 2 / 2

/-- Bulk Euler derivative at fixed throat data. -/
def bulkEulerDerivative
    (data : ParentBulkTwoSectorData)
    (bulk normal trace : ℝ) : ℝ :=
  data.bulkCoefficient * bulk +
    data.bulkToNormal * normal +
    data.bulkToTrace * trace

/-- Unique stationary bulk mode. -/
noncomputable def stationaryBulk
    (data : ParentBulkTwoSectorData)
    (normal trace : ℝ) : ℝ :=
  -(data.bulkToNormal * normal +
      data.bulkToTrace * trace) /
    data.bulkCoefficient

/-- The stationary mode solves the bulk equation. -/
theorem stationary_bulk_solves_euler
    (data : ParentBulkTwoSectorData)
    (normal trace : ℝ) :
    bulkEulerDerivative data
        (stationaryBulk data normal trace)
        normal trace = 0 := by
  unfold bulkEulerDerivative stationaryBulk
  field_simp [data.bulkCoefficientNonzero]
  ring

/-- The stationary bulk mode is unique. -/
theorem stationary_bulk_unique
    (data : ParentBulkTwoSectorData)
    (bulk normal trace : ℝ)
    (hStationary :
      bulkEulerDerivative data bulk normal trace = 0) :
    bulk = stationaryBulk data normal trace := by
  unfold bulkEulerDerivative at hStationary
  unfold stationaryBulk
  apply (eq_div_iff data.bulkCoefficientNonzero).2
  nlinarith

/-- Schur-complement normal coefficient. -/
noncomputable def reducedNormalCoefficient
    (data : ParentBulkTwoSectorData) : ℝ :=
  data.boundaryNormal -
    data.bulkToNormal ^ 2 / data.bulkCoefficient

/-- Schur-complement trace coefficient. -/
noncomputable def reducedTraceCoefficient
    (data : ParentBulkTwoSectorData) : ℝ :=
  data.boundaryTrace -
    data.bulkToTrace ^ 2 / data.bulkCoefficient

/-- Schur-complement reciprocal mixing coefficient. -/
noncomputable def reducedMixingCoefficient
    (data : ParentBulkTwoSectorData) : ℝ :=
  data.boundaryMixing -
    data.bulkToNormal * data.bulkToTrace /
      data.bulkCoefficient

/-- Reduced PT-even three-sector potential, with the odd sector omitted. -/
noncomputable def reducedPotential
    (data : ParentBulkTwoSectorData) : QuadraticPotential3 :=
  { nn := reducedNormalCoefficient data
    tt := reducedTraceCoefficient data
    oo := 0
    nt := reducedMixingCoefficient data
    no := 0
    trOdd := 0 }

/-- On-shell boundary action. -/
noncomputable def reducedAction
    (data : ParentBulkTwoSectorData)
    (normal trace : ℝ) : ℝ :=
  parentAction data
    (stationaryBulk data normal trace)
    normal trace

/-- Exact Schur-complement formula for the reduced action. -/
theorem reduced_action_formula
    (data : ParentBulkTwoSectorData)
    (normal trace : ℝ) :
    reducedAction data normal trace =
      potentialValue (reducedPotential data)
        normal trace 0 := by
  unfold reducedAction parentAction stationaryBulk
    reducedPotential reducedNormalCoefficient
    reducedTraceCoefficient reducedMixingCoefficient
    potentialValue
  field_simp [data.bulkCoefficientNonzero]
  ring

/-- Parent-bulk reduction automatically gives a Helmholtz-realizable Hessian. -/
theorem reduced_hessian_formally_self_adjoint
    (data : ParentBulkTwoSectorData) :
    FormallySelfAdjoint
      (hessianOperator (reducedPotential data)) :=
  hessian_formally_self_adjoint (reducedPotential data)

/-- The reduced potential is automatically PT invariant in the declared parity assignment. -/
theorem reduced_potential_pt_invariant
    (data : ParentBulkTwoSectorData) :
    PTInvariant (reducedPotential data) := by
  exact mixed_odd_couplings_zero_imply_pt_invariant
    (reducedPotential data) rfl rfl

/-- P-A parent reduction supplies a concrete witness for the P-C inverse problem. -/
theorem parent_reduction_supplies_helmholtz_witness
    (data : ParentBulkTwoSectorData) :
    ∃ potential : QuadraticPotential3,
      hessianOperator potential =
        hessianOperator (reducedPotential data) /\
      PTInvariant potential := by
  exact ⟨reducedPotential data, rfl,
    reduced_potential_pt_invariant data⟩

/--
Scoped parent-bulk synthesis for this finite-dimensional quadratic model: the
bulk stationary point is unique, its on-shell action has the stated Schur
complement, and the reduced Hessian is reciprocal and PT invariant.
-/
theorem parent_bulk_helmholtz_reciprocity_synthesis
    (data : ParentBulkTwoSectorData)
    (normal trace : ℝ) :
    (∃! bulk : ℝ,
      bulkEulerDerivative data bulk normal trace = 0) /\
    reducedAction data normal trace =
      potentialValue (reducedPotential data) normal trace 0 /\
    FormallySelfAdjoint
      (hessianOperator (reducedPotential data)) /\
    PTInvariant (reducedPotential data) := by
  refine ⟨?_, reduced_action_formula data normal trace,
    reduced_hessian_formally_self_adjoint data,
    reduced_potential_pt_invariant data⟩
  refine ⟨stationaryBulk data normal trace,
    stationary_bulk_solves_euler data normal trace, ?_⟩
  intro bulk hBulk
  exact stationary_bulk_unique data bulk normal trace hBulk

/-- Two parent theories can induce different reciprocal throat interactions. -/
def firstParent : ParentBulkTwoSectorData :=
  { bulkCoefficient := 1
    bulkToNormal := 0
    bulkToTrace := 0
    boundaryNormal := 1
    boundaryMixing := 0
    boundaryTrace := 1
    bulkCoefficientNonzero := by norm_num }


def secondParent : ParentBulkTwoSectorData :=
  { bulkCoefficient := 1
    bulkToNormal := 1
    bulkToTrace := 1
    boundaryNormal := 2
    boundaryMixing := 0
    boundaryTrace := 2
    bulkCoefficientNonzero := by norm_num }

/-- The two examples have equal reduced diagonals but different reduced mixing. -/
theorem parent_choice_changes_same_parity_mixing :
    (reducedPotential firstParent).nn =
        (reducedPotential secondParent).nn /\
    (reducedPotential firstParent).tt =
        (reducedPotential secondParent).tt /\
    (reducedPotential firstParent).nt ≠
        (reducedPotential secondParent).nt := by
  norm_num [reducedPotential, reducedNormalCoefficient,
    reducedTraceCoefficient, reducedMixingCoefficient,
    firstParent, secondParent]

/--
Strong P-A/P-C synthesis: a symmetric parent variational problem guarantees
reciprocity and PT compatibility of the reduced Hessian.  It does not make the
result absolute, because different admissible parent actions and boundary terms
produce different same-parity interactions.
-/
structure ParentBulkReciprocityPhysicalStatus where
  parentFieldContentDerived : Prop
  parentActionDerived : Prop
  parentGaugeFixingDerived : Prop
  boundaryAndJunctionTermsDerived : Prop
  wellPosedBulkProblemProved : Prop
  onShellReductionConstructed : Prop
  reducedHessianSelfAdjoint : Prop
  ptCompatibilityDerived : Prop
  parentActionUniquelySelected : Prop
  finiteBoundaryCountertermsFixed : Prop


def parentBulkReciprocityPhysicalClosure
    (s : ParentBulkReciprocityPhysicalStatus) : Prop :=
  s.parentFieldContentDerived /\
  s.parentActionDerived /\
  s.parentGaugeFixingDerived /\
  s.boundaryAndJunctionTermsDerived /\
  s.wellPosedBulkProblemProved /\
  s.onShellReductionConstructed /\
  s.reducedHessianSelfAdjoint /\
  s.ptCompatibilityDerived /\
  s.parentActionUniquelySelected /\
  s.finiteBoundaryCountertermsFixed

end P0EFTJanusParentBulkHelmholtzReciprocity
end JanusFormal
