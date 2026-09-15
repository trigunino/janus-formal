import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D

/-!
# Local GHY-to-joint transgression on a measured carrier

This module isolates the analytic statement needed by a local
codimension-two trace.  A scalar density is given on a measured joint
carrier and along each real collar fibre.  When its weighted density is the
derivative of a primitive, the fundamental theorem of calculus produces the
two oriented endpoint densities.  Fubini then identifies the product
integral with their measured joint coefficient.

The construction is deliberately abstract.  It does not construct an
incidence map from the physical orientation boundary, and it does not
identify these endpoint coefficients with the faithful joint actions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06LocalGHYJointTransgression4D

set_option autoImplicit false
noncomputable section

open scoped Interval
open MeasureTheory Set
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D

/-- A joint carrier together with the measure used for its local density. -/
structure ProgramPT06MeasuredJointCarrier
    (JointPoint : Type*) [MeasurableSpace JointPoint] where
  measure : Measure JointPoint
  sFinite : SFinite measure

/-- Local data for a GHY-to-joint transgression.  The derivative identity is
an equality for the weighted density, before either fibre or joint
integration. -/
structure ProgramPT06LocalGHYJointTransgressionData
    (NullFace JointPoint : Type*) [MeasurableSpace JointPoint] where
  carrier : ProgramPT06MeasuredJointCarrier JointPoint
  interval : NullFace → OrientedNullInterval
  fiberWeight : NullFace → JointPoint → Real → Real
  localGHYDensity : NullFace → JointPoint → Real → Real
  primitive : NullFace → JointPoint → Real → Real
  primitive_hasDerivAt :
    ∀ face point parameter,
      HasDerivAt (primitive face point)
        (fiberWeight face point parameter *
          localGHYDensity face point parameter) parameter
  weightedDensity_intervalIntegrable :
    ∀ face point,
      IntervalIntegrable
        (fun parameter ↦
          fiberWeight face point parameter *
            localGHYDensity face point parameter)
        volume (interval face).initialParameter
          (interval face).finalParameter

/-- The local scalar density including its fibre weight. -/
def programPT06LocalGHYWeightedDensity
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) (point : JointPoint) (parameter : Real) : Real :=
  data.fiberWeight face point parameter *
    data.localGHYDensity face point parameter

/-- The two oriented local endpoint densities furnished by the primitive. -/
def programPT06LocalGHYJointEndpointDensity
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) : ProgramPT05NullJointEndpoint → JointPoint → Real
  | .initial, point =>
      -data.primitive face point (data.interval face).initialParameter
  | .final, point =>
      data.primitive face point (data.interval face).finalParameter

/-- Integrate each oriented endpoint density over the measured joint
carrier.  This lands in the reduced joint-coefficient type already used by
T05. -/
def programPT06LocalGHYJointCoefficient
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint) :
    ProgramPT05JointCoefficient NullFace :=
  fun face endpoint ↦
    ∫ point,
      programPT06LocalGHYJointEndpointDensity data face endpoint point
      ∂data.carrier.measure

/-- The weighted integral along one collar fibre. -/
def programPT06LocalGHYFiberIntegral
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) (point : JointPoint) : Real :=
  ∫ parameter in
      (data.interval face).initialParameter..
        (data.interval face).finalParameter,
    programPT06LocalGHYWeightedDensity data face point parameter

/-- Fibrewise FTOC: the transgression is derived from the stored derivative
and interval-integrability proofs. -/
theorem programPT06LocalGHYFiberIntegral_eq_primitive_sub
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) (point : JointPoint) :
    programPT06LocalGHYFiberIntegral data face point =
      data.primitive face point (data.interval face).finalParameter -
        data.primitive face point (data.interval face).initialParameter := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro parameter _
    exact data.primitive_hasDerivAt face point parameter
  · exact data.weightedDensity_intervalIntegrable face point

/-- The same fibrewise identity with the two orientation signs exposed. -/
theorem programPT06LocalGHYFiberIntegral_eq_jointEndpoints
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) (point : JointPoint) :
    programPT06LocalGHYFiberIntegral data face point =
      programPT06LocalGHYJointEndpointDensity data face .initial point +
        programPT06LocalGHYJointEndpointDensity data face .final point := by
  rw [programPT06LocalGHYFiberIntegral_eq_primitive_sub]
  simp [programPT06LocalGHYJointEndpointDensity]
  ring

/-- Product integral of a local weighted density over one ordered collar
and its measured joint carrier. -/
def programPT06LocalGHYJointProductIntegral
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace) : Real :=
  ∫ pair : JointPoint × Real,
    programPT06LocalGHYWeightedDensity data face pair.1 pair.2
    ∂(data.carrier.measure.prod
      (volume.restrict
        (uIoc (data.interval face).initialParameter
          (data.interval face).finalParameter)))

/-- Fubini and fibrewise FTOC identify the product density integral with the
sum of its two measured endpoint coefficients.  All analytic hypotheses are
explicit. -/
theorem programPT06LocalGHYJointProductIntegral_eq_coefficient
    {NullFace JointPoint : Type*} [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (face : NullFace)
    (hOrder : (data.interval face).initialParameter ≤
      (data.interval face).finalParameter)
    (hProduct : Integrable
      (fun pair : JointPoint × Real ↦
        programPT06LocalGHYWeightedDensity data face pair.1 pair.2)
      (data.carrier.measure.prod
        (volume.restrict
          (uIoc (data.interval face).initialParameter
            (data.interval face).finalParameter))))
    (hInitial : Integrable
      (fun point ↦
        data.primitive face point (data.interval face).initialParameter)
      data.carrier.measure)
    (hFinal : Integrable
      (fun point ↦
        data.primitive face point (data.interval face).finalParameter)
      data.carrier.measure) :
    programPT06LocalGHYJointProductIntegral data face =
      programPT06LocalGHYJointCoefficient data face .initial +
        programPT06LocalGHYJointCoefficient data face .final := by
  letI : SFinite data.carrier.measure := data.carrier.sFinite
  rw [programPT06LocalGHYJointProductIntegral, integral_prod _ hProduct]
  calc
    (∫ point, (∫ parameter,
        programPT06LocalGHYWeightedDensity data face point parameter
          ∂volume.restrict
            (uIoc (data.interval face).initialParameter
              (data.interval face).finalParameter))
      ∂data.carrier.measure) =
        ∫ point,
          (programPT06LocalGHYJointEndpointDensity data face .initial point +
            programPT06LocalGHYJointEndpointDensity data face .final point)
          ∂data.carrier.measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point ↦ by
        have hFiber :=
          programPT06LocalGHYFiberIntegral_eq_jointEndpoints data face point
        unfold programPT06LocalGHYFiberIntegral at hFiber
        rw [intervalIntegral.integral_of_le hOrder] at hFiber
        simpa [uIoc_of_le hOrder] using hFiber
    _ =
        (∫ point,
            programPT06LocalGHYJointEndpointDensity data face .initial point
            ∂data.carrier.measure) +
          ∫ point,
            programPT06LocalGHYJointEndpointDensity data face .final point
            ∂data.carrier.measure := by
      rw [integral_add]
      · exact hInitial.neg
      · exact hFinal
    _ = programPT06LocalGHYJointCoefficient data face .initial +
          programPT06LocalGHYJointCoefficient data face .final := by
      rfl

/-- Sum of the product integrals over a finite face carrier. -/
def programPT06LocalGHYJointTotalProductIntegral
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint) :
    Real :=
  ∑ face : NullFace, programPT06LocalGHYJointProductIntegral data face

/-- The finite integrated transgression lands exactly in T05's existing
joint-density integral. -/
theorem programPT06LocalGHYJointTotalProductIntegral_eq_geometricJoint
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    (data : ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint)
    (hOrder : ∀ face,
      (data.interval face).initialParameter ≤
        (data.interval face).finalParameter)
    (hProduct : ∀ face, Integrable
      (fun pair : JointPoint × Real ↦
        programPT06LocalGHYWeightedDensity data face pair.1 pair.2)
      (data.carrier.measure.prod
        (volume.restrict
          (uIoc (data.interval face).initialParameter
            (data.interval face).finalParameter))))
    (hInitial : ∀ face, Integrable
      (fun point ↦
        data.primitive face point (data.interval face).initialParameter)
      data.carrier.measure)
    (hFinal : ∀ face, Integrable
      (fun point ↦
        data.primitive face point (data.interval face).finalParameter)
      data.carrier.measure) :
    programPT06LocalGHYJointTotalProductIntegral data =
      programPT05GeometricJointDensityIntegral
        (programPT06LocalGHYJointCoefficient data) := by
  unfold programPT06LocalGHYJointTotalProductIntegral
    programPT05GeometricJointDensityIntegral
  apply Finset.sum_congr rfl
  intro face _
  exact programPT06LocalGHYJointProductIntegral_eq_coefficient data face
    (hOrder face) (hProduct face) (hInitial face) (hFinal face)

end
end P0EFTJanusProgramPT06LocalGHYJointTransgression4D
end JanusFormal
