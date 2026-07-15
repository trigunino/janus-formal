import Mathlib.LinearAlgebra.Quotient.Bilinear
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusRelativeKineticSignNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackQuotientHessian

namespace JanusFormal
namespace P0EFTJanusReducedBimetricQuadraticFrechetSpectrum

set_option autoImplicit false

noncomputable section

open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusRelativeKineticSignNoGo
open P0EFTJanusFrechetPullbackQuotientHessian

/-- Two real homogeneous fluctuation amplitudes, packaged as the real and
imaginary coordinates of `ℂ` solely to use its canonical real normed-space
structure.  No physical complexification is asserted.  This remains only the
reduced tensor-amplitude sector, not the covariant Janus field space. -/
abbrev ReducedMode := ℂ

/-- Plus-sheet amplitude as a continuous linear functional. -/
def plusProjection : ReducedMode →L[ℝ] ℝ :=
  Complex.reCLM

/-- Minus-sheet amplitude as a continuous linear functional. -/
def minusProjection : ReducedMode →L[ℝ] ℝ :=
  Complex.imCLM

/-- Relative amplitude selected by the bimetric interaction. -/
def relativeProjection : ReducedMode →L[ℝ] ℝ :=
  plusProjection - minusProjection

@[simp]
theorem plusProjection_apply (mode : ReducedMode) :
    plusProjection mode = mode.re := rfl

@[simp]
theorem minusProjection_apply (mode : ReducedMode) :
    minusProjection mode = mode.im := rfl

@[simp]
theorem relativeProjection_apply (mode : ReducedMode) :
    relativeProjection mode = mode.re - mode.im := rfl

/-- Conditional positive-sign quadratic candidate.  The interaction
coefficient is exactly the reduced Fierz--Pauli coefficient already isolated
in the bimetric branch; the two kinetic signs remain explicit inputs. -/
def reducedQuadraticAction
  (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) : ℝ :=
  (1 / 2 : ℝ) *
    (plusKinetic * (plusProjection mode) ^ 2 +
      minusKinetic * (minusProjection mode) ^ 2 +
      relativeMass * (relativeProjection mode) ^ 2)

/-- Displayed Fréchet gradient of the reduced action. -/
def reducedQuadraticGradient
  (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) : ReducedMode →L[ℝ] ℝ :=
  (plusKinetic * plusProjection mode) • plusProjection +
    (minusKinetic * minusProjection mode) • minusProjection +
    (relativeMass * relativeProjection mode) • relativeProjection

/-- Constant Hessian of the reduced quadratic action. -/
def reducedQuadraticHessian
    (plusKinetic minusKinetic relativeMass : ℝ) :
    ReducedMode →L[ℝ] ReducedMode →L[ℝ] ℝ :=
  (plusKinetic • plusProjection).smulRight plusProjection +
    (minusKinetic • minusProjection).smulRight minusProjection +
    (relativeMass • relativeProjection).smulRight relativeProjection

@[simp]
theorem reducedQuadraticGradient_apply
    (plusKinetic minusKinetic relativeMass : ℝ)
    (mode direction : ReducedMode) :
    reducedQuadraticGradient plusKinetic minusKinetic relativeMass mode direction =
      plusKinetic * mode.re * direction.re +
      minusKinetic * mode.im * direction.im +
      relativeMass * (mode.re - mode.im) * (direction.re - direction.im) := by
  simp [reducedQuadraticGradient, plusProjection, minusProjection,
    relativeProjection, smul_eq_mul]

@[simp]
theorem reducedQuadraticHessian_apply
    (plusKinetic minusKinetic relativeMass : ℝ)
    (first second : ReducedMode) :
    reducedQuadraticHessian plusKinetic minusKinetic relativeMass first second =
      plusKinetic * first.re * second.re +
      minusKinetic * first.im * second.im +
      relativeMass * (first.re - first.im) * (second.re - second.im) := by
  simp [reducedQuadraticHessian, plusProjection, minusProjection,
    relativeProjection, smul_eq_mul]

/-- The candidate action has the displayed genuine Fréchet derivative. -/
theorem reducedQuadraticAction_hasFDerivAt
    (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) :
    HasFDerivAt
      (reducedQuadraticAction plusKinetic minusKinetic relativeMass)
      (reducedQuadraticGradient plusKinetic minusKinetic relativeMass mode)
      mode := by
  have hPlus :
      HasFDerivAt (fun x : ReducedMode => plusProjection x)
        plusProjection mode :=
    plusProjection.hasFDerivAt
  have hMinus :
      HasFDerivAt (fun x : ReducedMode => minusProjection x)
        minusProjection mode :=
    minusProjection.hasFDerivAt
  have hRelative :
      HasFDerivAt (fun x : ReducedMode => relativeProjection x)
        relativeProjection mode := by
    exact relativeProjection.hasFDerivAt
  have hCandidate :=
    (((hPlus.pow 2).const_mul plusKinetic).add
      ((hMinus.pow 2).const_mul minusKinetic)).add
      ((hRelative.pow 2).const_mul relativeMass)
  have hHalf := hCandidate.const_mul (1 / 2 : ℝ)
  change HasFDerivAt
    (fun x : ReducedMode =>
      (1 / 2 : ℝ) *
        (plusKinetic * (plusProjection x) ^ 2 +
          minusKinetic * (minusProjection x) ^ 2 +
          relativeMass * (relativeProjection x) ^ 2))
    (reducedQuadraticGradient plusKinetic minusKinetic relativeMass mode) mode
  apply hHalf.congr_fderiv
  ext direction
  simp [reducedQuadraticGradient, smul_eq_mul]
  ring

/-- The displayed gradient itself has the displayed genuine derivative. -/
theorem reducedQuadraticGradient_hasFDerivAt
    (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) :
    HasFDerivAt
      (reducedQuadraticGradient plusKinetic minusKinetic relativeMass)
      (reducedQuadraticHessian plusKinetic minusKinetic relativeMass)
      mode := by
  have hPlus :
      HasFDerivAt
        (fun x : ReducedMode =>
          (plusKinetic * plusProjection x) • plusProjection)
        ((plusKinetic • plusProjection).smulRight plusProjection) mode :=
    ((plusProjection.hasFDerivAt (x := mode)).const_mul plusKinetic).smul_const
      plusProjection
  have hMinus :
      HasFDerivAt
        (fun x : ReducedMode =>
          (minusKinetic * minusProjection x) • minusProjection)
        ((minusKinetic • minusProjection).smulRight minusProjection) mode :=
    ((minusProjection.hasFDerivAt (x := mode)).const_mul minusKinetic).smul_const
      minusProjection
  have hRelative :
      HasFDerivAt
        (fun x : ReducedMode =>
          (relativeMass * relativeProjection x) • relativeProjection)
        ((relativeMass • relativeProjection).smulRight relativeProjection)
        mode :=
    ((relativeProjection.hasFDerivAt (x := mode)).const_mul
      relativeMass).smul_const relativeProjection
  change HasFDerivAt
    (fun x : ReducedMode =>
      (plusKinetic * plusProjection x) • plusProjection +
        (minusKinetic * minusProjection x) • minusProjection +
        (relativeMass * relativeProjection x) • relativeProjection)
    ((plusKinetic • plusProjection).smulRight plusProjection +
      (minusKinetic • minusProjection).smulRight minusProjection +
      (relativeMass • relativeProjection).smulRight relativeProjection) mode
  exact (hPlus.add hMinus).add hRelative

/-- Exact first Fréchet derivative, not a symbolic gradient proxy. -/
theorem reducedQuadraticAction_fderiv
    (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) :
    fderiv ℝ (reducedQuadraticAction plusKinetic minusKinetic relativeMass) mode =
      reducedQuadraticGradient plusKinetic minusKinetic relativeMass mode :=
  (reducedQuadraticAction_hasFDerivAt
    plusKinetic minusKinetic relativeMass mode).fderiv

/-- Exact second Fréchet derivative of the reduced quadratic candidate. -/
theorem reducedQuadraticAction_second_fderiv
    (plusKinetic minusKinetic relativeMass : ℝ)
    (mode : ReducedMode) :
    fderiv ℝ
        (fun x => fderiv ℝ
          (reducedQuadraticAction plusKinetic minusKinetic relativeMass) x)
        mode =
      reducedQuadraticHessian plusKinetic minusKinetic relativeMass := by
  have hGradient :
      (fun x => fderiv ℝ
        (reducedQuadraticAction plusKinetic minusKinetic relativeMass) x) =
        reducedQuadraticGradient plusKinetic minusKinetic relativeMass := by
    funext x
    exact reducedQuadraticAction_fderiv
      plusKinetic minusKinetic relativeMass x
  rw [hGradient]
  exact (reducedQuadraticGradient_hasFDerivAt
    plusKinetic minusKinetic relativeMass mode).fderiv

/-- Diagonal and relative mode representatives. -/
def diagonalModeVector (amplitude : ℝ) : ReducedMode :=
  ⟨amplitude, amplitude⟩

def relativeModeVector (amplitude : ℝ) : ReducedMode :=
  ⟨amplitude, -amplitude⟩

def minusModeVector (amplitude : ℝ) : ReducedMode :=
  ⟨0, amplitude⟩

@[simp]
theorem relativeProjection_diagonalModeVector (amplitude : ℝ) :
    relativeProjection (diagonalModeVector amplitude) = 0 := by
  simp [relativeProjection, diagonalModeVector, plusProjection, minusProjection]

@[simp]
theorem relativeProjection_relativeModeVector (amplitude : ℝ) :
    relativeProjection (relativeModeVector amplitude) = 2 * amplitude := by
  simp [relativeProjection, relativeModeVector, plusProjection, minusProjection]
  ring

/-- Equal positive kinetic coefficients separate the diagonal massless mode
from the relative massive mode at the level of the actual Hessian. -/
theorem equal_kinetic_hessian_mode_values
    (kinetic relativeMass amplitude : ℝ) :
    reducedQuadraticHessian kinetic kinetic relativeMass
        (diagonalModeVector amplitude) (diagonalModeVector amplitude) =
        2 * kinetic * amplitude ^ 2 ∧
      reducedQuadraticHessian kinetic kinetic relativeMass
        (relativeModeVector amplitude) (relativeModeVector amplitude) =
        (2 * kinetic + 4 * relativeMass) * amplitude ^ 2 := by
  constructor <;>
    simp [reducedQuadraticHessian_apply, diagonalModeVector,
      relativeModeVector] <;>
    ring

/-- Under the safe conditional sign assumptions, the actual full Hessian is
positive in every nonzero reduced direction. -/
theorem conditional_reduced_hessian_positive
    (plusKinetic minusKinetic relativeMass : ℝ)
    (hPlus : 0 < plusKinetic)
    (hMinus : 0 < minusKinetic)
    (hMass : 0 ≤ relativeMass)
    (direction : ReducedMode)
    (hDirection : direction ≠ 0) :
    0 < reducedQuadraticHessian plusKinetic minusKinetic relativeMass
      direction direction := by
  have hComponents : direction.re ≠ 0 ∨ direction.im ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hDirection
    apply Complex.ext <;> simp [h]
  have hKinetic :
      0 < plusKinetic * direction.re ^ 2 +
        minusKinetic * direction.im ^ 2 := by
    rcases hComponents with hPlusDirection | hMinusDirection
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hPlus (sq_pos_of_ne_zero hPlusDirection))
        (mul_nonneg (le_of_lt hMinus) (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt hPlus) (sq_nonneg _))
        (mul_pos hMinus (sq_pos_of_ne_zero hMinusDirection))
  have hInteraction :
      0 ≤ relativeMass * (direction.re - direction.im) ^ 2 :=
    mul_nonneg hMass (sq_nonneg _)
  rw [reducedQuadraticHessian_apply]
  nlinarith [hKinetic, hInteraction]

/-- Interaction-only Hessian.  Its diagonal kernel is not the full gauge
kernel of covariant bimetric gravity; quotienting it only isolates the reduced
relative interaction sector. -/
def interactionHessian (relativeMass : ℝ) :
    ReducedMode →L[ℝ] ReducedMode →L[ℝ] ℝ :=
  reducedQuadraticHessian 0 0 relativeMass

/-- Exact diagonal kernel of the interaction Hessian for nonzero mass. -/
theorem interaction_hessian_kernel_is_diagonal
    (relativeMass : ℝ)
    (hMass : relativeMass ≠ 0)
    (mode : ReducedMode) :
    (∀ direction, interactionHessian relativeMass mode direction = 0) ↔
      relativeProjection mode = 0 := by
  constructor
  · intro hKernel
    have hSelf := hKernel mode
    simp [interactionHessian, reducedQuadraticHessian_apply] at hSelf
    rcases hSelf with hMassZero | hRelative
    · exact False.elim (hMass hMassZero)
    · simpa using hRelative
  · intro hDiagonal direction
    rw [relativeProjection_apply] at hDiagonal
    simp [interactionHessian, reducedQuadraticHessian_apply, hDiagonal]

/-- Algebraic diagonal submodule, exactly the interaction kernel. -/
def diagonalDirections : Submodule ℝ ReducedMode :=
  relativeProjection.ker

/-- Algebraic quotient isolating the relative interaction sector.  This is
not asserted to be the complete topological or gauge-reduced physical space. -/
abbrev RelativeSectorQuotient := ReducedMode ⧸ diagonalDirections

private theorem interactionHessian_vanishes_left
    (relativeMass : ℝ) :
    ∀ gauge ∈ diagonalDirections, ∀ direction,
      continuousHessianToLinear (interactionHessian relativeMass)
        gauge direction = 0 := by
  intro gauge hGauge direction
  have hRelative : relativeProjection gauge = 0 := hGauge
  rw [relativeProjection_apply] at hRelative
  simp [continuousHessianToLinear_apply, interactionHessian,
    reducedQuadraticHessian_apply, hRelative]

private theorem interactionHessian_vanishes_right
    (relativeMass : ℝ) :
    ∀ gauge ∈ diagonalDirections, ∀ direction,
      continuousHessianToLinear (interactionHessian relativeMass)
        direction gauge = 0 := by
  intro gauge hGauge direction
  have hRelative : relativeProjection gauge = 0 := hGauge
  rw [relativeProjection_apply] at hRelative
  simp [continuousHessianToLinear_apply, interactionHessian,
    reducedQuadraticHessian_apply, hRelative]

/-- Unique bilinear descent of the interaction Hessian to the relative-sector
quotient. -/
def relativeSectorHessian (relativeMass : ℝ) :
    RelativeSectorQuotient →ₗ[ℝ] RelativeSectorQuotient →ₗ[ℝ] ℝ :=
  quotientHessian
    (continuousHessianToLinear (interactionHessian relativeMass))
    diagonalDirections
    (interactionHessian_vanishes_left relativeMass)
    (interactionHessian_vanishes_right relativeMass)

@[simp]
theorem relativeSectorHessian_mkQ
    (relativeMass : ℝ)
    (first second : ReducedMode) :
    relativeSectorHessian relativeMass
        (diagonalDirections.mkQ first) (diagonalDirections.mkQ second) =
      relativeMass * relativeProjection first * relativeProjection second := by
  change interactionHessian relativeMass first second = _
  simp [interactionHessian, reducedQuadraticHessian_apply]

/-- Positive mass makes the descended relative-sector Hessian positive away
from the zero quotient class. -/
theorem relativeSectorHessian_positive
    (relativeMass : ℝ)
    (hMass : 0 < relativeMass)
    (modeClass : RelativeSectorQuotient)
    (hClass : modeClass ≠ 0) :
    0 < relativeSectorHessian relativeMass modeClass modeClass := by
  obtain ⟨mode, rfl⟩ := diagonalDirections.mkQ_surjective modeClass
  have hRelative : relativeProjection mode ≠ 0 := by
    intro hZero
    apply hClass
    have hMembership : mode ∈ diagonalDirections := by
      change relativeProjection mode = 0
      exact hZero
    apply LinearMap.mem_ker.mp
    simpa only [Submodule.ker_mkQ] using hMembership
  rw [relativeSectorHessian_mkQ]
  rw [mul_assoc]
  exact mul_pos hMass (mul_self_pos.mpr hRelative)

/-- The selected PT-flat cone supplies the positive coefficient needed for
the genuine quotient-Hessian theorem. -/
theorem pt_flat_relativeSectorHessian_positive
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (modeClass : RelativeSectorQuotient)
    (hClass : modeClass ≠ 0) :
    0 < relativeSectorHessian
      (fpMassCombination (ptFlatCoefficients beta1 beta2))
      modeClass modeClass :=
  relativeSectorHessian_positive
    (fpMassCombination (ptFlatCoefficients beta1 beta2))
    (pt_flat_fp_mass_positive beta1 beta2 hBeta1 hBeta2)
    modeClass hClass

/-- The relative Einstein--Hilbert sign used in the published-sign audit. -/
def publishedRelativeKappa : ℝ := -1

/-- Pure kinetic part with a positive plus coefficient and the published
relative factor `κ = -1`.  The interaction is omitted deliberately: it cannot
repair a negative principal kinetic direction. -/
def publishedSignKineticAction
    (plusKinetic : ℝ) (mode : ReducedMode) : ℝ :=
  (1 / 2 : ℝ) * kineticQuadraticForm
    plusKinetic (publishedRelativeKappa * plusKinetic) mode.re mode.im

/-- Its true second Fréchet derivative is the corresponding opposite-sign
kinetic Hessian. -/
theorem publishedSignKineticAction_second_fderiv
    (plusKinetic : ℝ)
    (mode : ReducedMode) :
    fderiv ℝ
        (fun x => fderiv ℝ (publishedSignKineticAction plusKinetic) x)
        mode =
      reducedQuadraticHessian plusKinetic (-plusKinetic) 0 := by
  have hAction : publishedSignKineticAction plusKinetic =
      reducedQuadraticAction plusKinetic (-plusKinetic) 0 := by
    funext x
    simp [publishedSignKineticAction, publishedRelativeKappa,
      kineticQuadraticForm, reducedQuadraticAction]
  rw [hAction]
  exact reducedQuadraticAction_second_fderiv
    plusKinetic (-plusKinetic) 0 mode

/-- No-go for the published relative kinetic sign in an ordinary positive
Hilbert interpretation: the actual Hessian has a strictly negative minus-sheet
direction.  Removing it requires a constraint, auxiliary-field reduction, or
a separately constructed non-Hilbert/PT completion. -/
theorem published_kappa_minus_one_has_negative_actual_hessian_direction
    (plusKinetic : ℝ)
    (hPlus : 0 < plusKinetic)
    (mode : ReducedMode) :
    fderiv ℝ
        (fun x => fderiv ℝ (publishedSignKineticAction plusKinetic) x)
        mode (minusModeVector 1) (minusModeVector 1) < 0 := by
  rw [publishedSignKineticAction_second_fderiv]
  simp [reducedQuadraticHessian_apply, minusModeVector]
  linarith

end

end P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
end JanusFormal
