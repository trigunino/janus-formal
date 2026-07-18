import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNullExpansionCountertermVariation

/-!
# One-dimensional null/joint reparametrization cancellation

This gate records a concrete null-generator model.  The screen area `A`
satisfies `A' = A * Theta`, a normalization change is represented by `sigma`,
and the inaffinity shifts by `sigma'`.  The resulting local face shift is the
actual derivative

`A * sigma' + A * Theta * sigma = (A * sigma)'`.

An oriented endpoint ledger then cancels the corresponding endpoint
transgression with two joint shifts.  The ledger does not construct an
integral or invoke a fundamental theorem of calculus.  A zero-expansion
counterterm prescription, geometric null hypersurfaces, corner orientations,
and global Einstein--Hilbert cancellation remain outside scope.
-/

namespace JanusFormal
namespace P0EFTJanusNullJointReparametrizationCancellation

set_option autoImplicit false

noncomputable section

/-- Differentiable data along one real null-generator parameter. -/
structure NullGeneratorReparametrizationData where
  area : ℝ → ℝ
  expansion : ℝ → ℝ
  inaffinity : ℝ → ℝ
  sigma : ℝ → ℝ
  sigmaDerivative : ℝ → ℝ
  area_hasDerivAt : ∀ parameter : ℝ,
    HasDerivAt area (area parameter * expansion parameter) parameter
  sigma_hasDerivAt : ∀ parameter : ℝ,
    HasDerivAt sigma (sigmaDerivative parameter) parameter

/-- Infinitesimal inaffinity transformation `kappa -> kappa + sigma'`. -/
def shiftedInaffinity
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) : ℝ :=
  data.inaffinity parameter + data.sigmaDerivative parameter

theorem shiftedInaffinity_sub_inaffinity
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) :
    shiftedInaffinity data parameter - data.inaffinity parameter =
      data.sigmaDerivative parameter := by
  simp [shiftedInaffinity]

/-- Area-weighted shift of the null-generator inaffinity density. -/
def inaffinityDensityShift
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) : ℝ :=
  data.area parameter *
    (shiftedInaffinity data parameter - data.inaffinity parameter)

theorem inaffinityDensityShift_eq
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) :
    inaffinityDensityShift data parameter =
      data.area parameter * data.sigmaDerivative parameter := by
  simp [inaffinityDensityShift, shiftedInaffinity]

/-- Expansion contribution accompanying the normalization change. -/
def expansionDensityShift
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) : ℝ :=
  data.area parameter * data.expansion parameter * data.sigma parameter

/-- Total local face shift in the one-dimensional model. -/
def localFaceShift
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) : ℝ :=
  inaffinityDensityShift data parameter + expansionDensityShift data parameter

/-- The local face shift is the actual derivative of `A * sigma`. -/
theorem area_mul_sigma_hasDerivAt
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) :
    HasDerivAt (fun x => data.area x * data.sigma x)
      (localFaceShift data parameter) parameter := by
  have hProduct :=
    (data.area_hasDerivAt parameter).mul
      (data.sigma_hasDerivAt parameter)
  refine hProduct.congr_deriv ?_
  simp [localFaceShift, inaffinityDensityShift, shiftedInaffinity,
    expansionDensityShift]
  ring

/-- Pointwise transgression formula
`A sigma' + A Theta sigma = (A sigma)'`. -/
theorem localFaceShift_eq_productDerivative
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) :
    localFaceShift data parameter =
      data.area parameter * data.sigmaDerivative parameter +
        data.area parameter * data.expansion parameter *
          data.sigma parameter := by
  simp [localFaceShift, inaffinityDensityShift, shiftedInaffinity,
    expansionDensityShift]

/-- Oriented parameter interval; no order or integration structure is assumed. -/
structure OrientedNullInterval where
  initialParameter : ℝ
  finalParameter : ℝ

/-- Reverse the orientation of a null-generator interval by exchanging its
two endpoint parameters. -/
def reverseOrientedNullInterval
    (interval : OrientedNullInterval) : OrientedNullInterval where
  initialParameter := interval.finalParameter
  finalParameter := interval.initialParameter

@[simp]
theorem reverseOrientedNullInterval_initialParameter
    (interval : OrientedNullInterval) :
    (reverseOrientedNullInterval interval).initialParameter =
      interval.finalParameter := by
  rfl

@[simp]
theorem reverseOrientedNullInterval_finalParameter
    (interval : OrientedNullInterval) :
    (reverseOrientedNullInterval interval).finalParameter =
      interval.initialParameter := by
  rfl

@[simp]
theorem reverseOrientedNullInterval_reverse
    (interval : OrientedNullInterval) :
    reverseOrientedNullInterval (reverseOrientedNullInterval interval) =
      interval := by
  cases interval
  rfl

/-- Endpoint primitive of the local transgression. -/
def endpointPrimitive
    (data : NullGeneratorReparametrizationData) (parameter : ℝ) : ℝ :=
  data.area parameter * data.sigma parameter

/-- Typed face/joint ledger for one oriented null-generator interval. -/
structure NullJointEndpointLedger where
  faceTransgression : ℝ
  initialJointShift : ℝ
  finalJointShift : ℝ

/-- Total normalization shift carried by the face and its two joints. -/
def NullJointEndpointLedger.totalShift
    (ledger : NullJointEndpointLedger) : ℝ :=
  ledger.faceTransgression + ledger.initialJointShift + ledger.finalJointShift

/-- Exact endpoint representative: the face carries the oriented primitive
difference, while the two joints carry its opposite endpoint values. -/
def exactEndpointLedger
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) : NullJointEndpointLedger :=
  { faceTransgression :=
      endpointPrimitive data interval.finalParameter -
        endpointPrimitive data interval.initialParameter
    initialJointShift := endpointPrimitive data interval.initialParameter
    finalJointShift := -endpointPrimitive data interval.finalParameter }

@[simp]
theorem exactEndpointLedger_faceTransgression
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data interval).faceTransgression =
      endpointPrimitive data interval.finalParameter -
        endpointPrimitive data interval.initialParameter := by
  rfl

/-- The oriented endpoint/joint shifts cancel the face transgression exactly. -/
theorem exactEndpointLedger_totalShift_zero
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data interval).totalShift = 0 := by
  simp [NullJointEndpointLedger.totalShift, exactEndpointLedger]

/-- Reversing the interval reverses the sign of the oriented face
transgression. -/
theorem exactEndpointLedger_reverse_faceTransgression
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data
        (reverseOrientedNullInterval interval)).faceTransgression =
      -(exactEndpointLedger data interval).faceTransgression := by
  simp [exactEndpointLedger]

/-- Under orientation reversal, the new initial joint is the negative of the
old final joint. -/
theorem exactEndpointLedger_reverse_initialJointShift
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data
        (reverseOrientedNullInterval interval)).initialJointShift =
      -(exactEndpointLedger data interval).finalJointShift := by
  simp [exactEndpointLedger]

/-- Under orientation reversal, the new final joint is the negative of the old
initial joint. -/
theorem exactEndpointLedger_reverse_finalJointShift
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data
        (reverseOrientedNullInterval interval)).finalJointShift =
      -(exactEndpointLedger data interval).initialJointShift := by
  simp [exactEndpointLedger]

/-- The full endpoint ledger is odd under reversal of interval orientation. -/
theorem exactEndpointLedger_reverse_totalShift
    (data : NullGeneratorReparametrizationData)
    (interval : OrientedNullInterval) :
    (exactEndpointLedger data
        (reverseOrientedNullInterval interval)).totalShift =
      -(exactEndpointLedger data interval).totalShift := by
  rw [exactEndpointLedger_totalShift_zero,
    exactEndpointLedger_totalShift_zero]
  simp

end

end P0EFTJanusNullJointReparametrizationCancellation
end JanusFormal
