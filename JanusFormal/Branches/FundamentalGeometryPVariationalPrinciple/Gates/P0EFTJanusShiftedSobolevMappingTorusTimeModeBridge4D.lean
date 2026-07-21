import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevLatticeLorentzGram
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusNontrivialFieldTimeAction4D

/-!
# One genuine mapping-torus field inside the shifted coefficient scale

This gate isolates the first temporal lattice mode in the completed shifted
coefficient space.  For every strictly positive target weight, its physical
amplitude is recovered by the existing weighted decoder.  The same amplitude
multiplies the genuine smooth cosine field on the effective D8 quotient.
Their one-dimensional ranges are linearly equivalent, and the quotient field
has the exact deck cocycle already supplied by smooth descent.

This is only a nonzero finite-mode bridge.  It is not an identification of the
full `Z^4` coefficient Hilbert space with intrinsic Sobolev sections, is not an
isometry, treats no spatial Fourier mode, and supplies no boundary theorem or
nontrivial physical bundle.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevMappingTorusTimeModeBridge4D

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusNontrivialFieldTimeAction4D
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram

/-- The lattice label of the first temporal mode and no spatial momentum. -/
def firstTemporalMode : LatticeMode :=
  fun index => if index = 0 then 1 else 0

theorem firstTemporalMode_ne_zero : firstTemporalMode ≠ 0 := by
  intro hZero
  have hEntry := congrFun hZero (0 : Fin 4)
  norm_num [firstTemporalMode] at hEntry

/-- Unit vector in the temporal potential coordinate. -/
def temporalPotentialUnit : PotentialFiber :=
  EuclideanSpace.single 0 1

theorem temporalPotentialUnit_ne_zero : temporalPotentialUnit ≠ 0 := by
  exact (EuclideanSpace.single_eq_zero_iff
    (i := (0 : Fin 4)) (a := (1 : Real))).not.mpr one_ne_zero

theorem shiftedSourceWeightPositive
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode) :
    ∀ mode, 0 < symbolShiftedSourceWeight targetWeight mode :=
  symbolShiftedSourceWeight_pos targetWeight hTargetWeight

/-- The weighted Hilbert coordinate of a physical amplitude in the first
temporal mode. -/
def physicalTemporalModeCoefficientLinearMap
    (targetWeight : LatticeMode → Real) :
    Real →ₗ[Real] ShiftedPotentialHilbert targetWeight where
  toFun := fun amplitude =>
    amplitude • lp.single 2 firstTemporalMode
      (Real.sqrt
          (symbolShiftedSourceWeight targetWeight firstTemporalMode) •
        temporalPotentialUnit)
  map_add' := by
    intro first second
    exact add_smul first second _
  map_smul' := by
    intro scalar amplitude
    exact mul_smul scalar amplitude _

/-- The existing weighted decoder recovers exactly the physical amplitude
stored in the selected mode and coordinate. -/
theorem decode_physicalTemporalModeCoefficient
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode)
    (amplitude : Real) :
    decodeWeightedPotential
        (symbolShiftedSourceWeight targetWeight)
        (shiftedSourceWeightPositive targetWeight hTargetWeight)
        (physicalTemporalModeCoefficientLinearMap targetWeight amplitude)
        firstTemporalMode 0 = amplitude := by
  change
    (amplitude *
        (Real.sqrt
          (symbolShiftedSourceWeight targetWeight firstTemporalMode) * 1)) /
      Real.sqrt
        (symbolShiftedSourceWeight targetWeight firstTemporalMode) = amplitude
  field_simp [Real.sqrt_ne_zero'.2
    (symbolShiftedSourceWeight_pos targetWeight hTargetWeight
      firstTemporalMode)]

theorem physicalTemporalModeCoefficientLinearMap_injective
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode) :
    Function.Injective
      (physicalTemporalModeCoefficientLinearMap targetWeight) := by
  intro first second hEqual
  have hDecoded := congrArg
    (fun coefficient : ShiftedPotentialHilbert targetWeight =>
      decodeWeightedPotential
          (symbolShiftedSourceWeight targetWeight)
          (shiftedSourceWeightPositive targetWeight hTargetWeight)
          coefficient firstTemporalMode 0)
    hEqual
  simpa only [decode_physicalTemporalModeCoefficient targetWeight
    hTargetWeight] using hDecoded

variable (period : Real) (hPeriod : period ≠ 0)

/-- The same physical amplitude realized as a genuine smooth scalar field on
the effective mapping-torus quotient. -/
def smoothTemporalModeLinearMap :
    Real →ₗ[Real] SmoothQuotientField period hPeriod Real where
  toFun := fun amplitude =>
    amplitude • periodicCosineQuotientField period hPeriod
  map_add' := by
    intro first second
    exact add_smul first second _
  map_smul' := by
    intro scalar amplitude
    exact mul_smul scalar amplitude _

theorem periodicCosineQuotientField_witness :
    periodicCosineQuotientField period hPeriod
        (timeFlowWitnessPoint period hPeriod) = 1 := by
  unfold timeFlowWitnessPoint
  simp

theorem smoothTemporalModeLinearMap_injective :
    Function.Injective (smoothTemporalModeLinearMap period hPeriod) := by
  intro first second hEqual
  have hValue := congrArg
    (fun field : SmoothQuotientField period hPeriod Real =>
      field (timeFlowWitnessPoint period hPeriod)) hEqual
  change
    first * periodicCosineQuotientField period hPeriod
        (timeFlowWitnessPoint period hPeriod) =
      second * periodicCosineQuotientField period hPeriod
        (timeFlowWitnessPoint period hPeriod) at hValue
  rw [periodicCosineQuotientField_witness period hPeriod,
    mul_one, mul_one] at hValue
  exact hValue

/-- The selected weighted-coordinate line. -/
def physicalTemporalModeCoefficientRange
    (targetWeight : LatticeMode → Real) :
    Submodule Real (ShiftedPotentialHilbert targetWeight) :=
  LinearMap.range (physicalTemporalModeCoefficientLinearMap targetWeight)

/-- The corresponding line of genuine smooth quotient fields. -/
def smoothTemporalModeRange :
    Submodule Real (SmoothQuotientField period hPeriod Real) :=
  LinearMap.range (smoothTemporalModeLinearMap period hPeriod)

def physicalTemporalModeCoefficientRangeEquiv
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode) :
    Real ≃ₗ[Real] physicalTemporalModeCoefficientRange targetWeight :=
  LinearEquiv.ofInjective
    (physicalTemporalModeCoefficientLinearMap targetWeight)
    (physicalTemporalModeCoefficientLinearMap_injective targetWeight
      hTargetWeight)

def smoothTemporalModeRangeEquiv :
    Real ≃ₗ[Real] smoothTemporalModeRange period hPeriod :=
  LinearEquiv.ofInjective
    (smoothTemporalModeLinearMap period hPeriod)
    (smoothTemporalModeLinearMap_injective period hPeriod)

/-- Honest finite-mode bridge: the selected line in the shifted coefficient
Hilbert space and the selected line of actual smooth D8 fields carry the same
physical amplitude. -/
def physicalCoefficientToSmoothTemporalModeEquiv
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode) :
    physicalTemporalModeCoefficientRange targetWeight ≃ₗ[Real]
      smoothTemporalModeRange period hPeriod :=
  (physicalTemporalModeCoefficientRangeEquiv targetWeight
      hTargetWeight).symm.trans
    (smoothTemporalModeRangeEquiv period hPeriod)

@[simp]
theorem physicalCoefficientToSmoothTemporalModeEquiv_amplitude
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode)
    (amplitude : Real) :
    physicalCoefficientToSmoothTemporalModeEquiv period hPeriod targetWeight
        hTargetWeight
        (physicalTemporalModeCoefficientRangeEquiv targetWeight
          hTargetWeight amplitude) =
      smoothTemporalModeRangeEquiv period hPeriod amplitude := by
  simp [physicalCoefficientToSmoothTemporalModeEquiv]

/-- Upstairs formula exhibiting the exact mapping-torus gluing field. -/
theorem smoothTemporalMode_lift_mk
    (amplitude : Real)
    (point : MappingTorusCover (reflectedSphereData period hPeriod)) :
    liftSmooth period hPeriod Real
        (smoothTemporalModeLinearMap period hPeriod amplitude) point =
      amplitude *
        Real.cos ((2 * Real.pi / period) * point.time) := by
  rfl

theorem smoothTemporalMode_lift_deck_invariant
    (amplitude : Real) (winding : Int)
    (point : MappingTorusCover (reflectedSphereData period hPeriod)) :
    liftSmooth period hPeriod Real
        (smoothTemporalModeLinearMap period hPeriod amplitude)
        (winding +ᵥ point) =
      liftSmooth period hPeriod Real
        (smoothTemporalModeLinearMap period hPeriod amplitude) point :=
  (liftSmooth period hPeriod Real
    (smoothTemporalModeLinearMap period hPeriod amplitude)).deck_invariant
      winding point

theorem shiftedSobolev_mappingTorus_timeMode_bridge4D
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode) :
    Function.Injective
        (physicalTemporalModeCoefficientLinearMap targetWeight) ∧
      Function.Injective (smoothTemporalModeLinearMap period hPeriod) ∧
      Nonempty
        (physicalTemporalModeCoefficientRange targetWeight ≃ₗ[Real]
          smoothTemporalModeRange period hPeriod) :=
  ⟨physicalTemporalModeCoefficientLinearMap_injective targetWeight
      hTargetWeight,
    smoothTemporalModeLinearMap_injective period hPeriod,
    ⟨physicalCoefficientToSmoothTemporalModeEquiv period hPeriod targetWeight
      hTargetWeight⟩⟩

end

end P0EFTJanusShiftedSobolevMappingTorusTimeModeBridge4D
end JanusFormal
