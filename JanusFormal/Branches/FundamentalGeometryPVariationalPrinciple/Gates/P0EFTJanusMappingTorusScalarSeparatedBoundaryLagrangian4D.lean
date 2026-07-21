import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D

/-!
# Separated scalar boundary lines are Lagrangian

For a nonzero coefficient pair `(a,b)`, the scalar condition

`a * value + b * normalDerivative = 0`

defines a line in the two-dimensional boundary plane.  This file proves that
line is not only isotropic for the Green form but equal to its symplectic
orthogonal.  The result is then lifted pointwise to arbitrary boundary sections
and connected to the smooth Dirichlet/Neumann/Robin predicates constructed in
the preceding gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D
open P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The scalar boundary line cut out by `a * value + b * normal = 0`. -/
def canonicalScalarSeparatedBoundaryLine
    (valueCoefficient normalCoefficient : Real) :
    Submodule Real CanonicalScalarBoundaryDatum where
  carrier := {datum |
    valueCoefficient * datum.1 + normalCoefficient * datum.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second hFirst hSecond
    change valueCoefficient * (first.1 + second.1) +
      normalCoefficient * (first.2 + second.2) = 0
    change valueCoefficient * first.1 + normalCoefficient * first.2 = 0 at hFirst
    change valueCoefficient * second.1 + normalCoefficient * second.2 = 0 at hSecond
    linarith
  smul_mem' := by
    intro scalar datum hDatum
    change valueCoefficient * (scalar * datum.1) +
      normalCoefficient * (scalar * datum.2) = 0
    change valueCoefficient * datum.1 + normalCoefficient * datum.2 = 0 at hDatum
    calc
      valueCoefficient * (scalar * datum.1) +
          normalCoefficient * (scalar * datum.2) =
        scalar * (valueCoefficient * datum.1 + normalCoefficient * datum.2) := by
          ring
      _ = 0 := by rw [hDatum, mul_zero]

@[simp] theorem mem_canonicalScalarSeparatedBoundaryLine
    (valueCoefficient normalCoefficient : Real)
    (datum : CanonicalScalarBoundaryDatum) :
    datum ∈ canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient ↔
      valueCoefficient * datum.1 + normalCoefficient * datum.2 = 0 :=
  Iff.rfl

/-- Canonical spanning vector of the separated line. -/
def canonicalScalarSeparatedBoundaryGenerator
    (valueCoefficient normalCoefficient : Real) :
    CanonicalScalarBoundaryDatum :=
  (normalCoefficient, -valueCoefficient)

@[simp] theorem canonicalScalarSeparatedBoundaryGenerator_fst
    (valueCoefficient normalCoefficient : Real) :
    (canonicalScalarSeparatedBoundaryGenerator valueCoefficient normalCoefficient).1 =
      normalCoefficient :=
  rfl

@[simp] theorem canonicalScalarSeparatedBoundaryGenerator_snd
    (valueCoefficient normalCoefficient : Real) :
    (canonicalScalarSeparatedBoundaryGenerator valueCoefficient normalCoefficient).2 =
      -valueCoefficient :=
  rfl

/-- The canonical generator lies in its separated boundary line. -/
theorem canonicalScalarSeparatedBoundaryGenerator_mem
    (valueCoefficient normalCoefficient : Real) :
    canonicalScalarSeparatedBoundaryGenerator valueCoefficient normalCoefficient ∈
      canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient := by
  change valueCoefficient * normalCoefficient +
    normalCoefficient * (-valueCoefficient) = 0
  ring

/-- Any two points of one nondegenerate separated line have zero Green pairing. -/
theorem canonicalScalarBoundarySymplecticForm_eq_zero_of_mem_separated
    (valueCoefficient normalCoefficient : Real)
    (hNondegenerate : valueCoefficient ≠ 0 ∨ normalCoefficient ≠ 0)
    (first second : CanonicalScalarBoundaryDatum)
    (hFirst : first ∈
      canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient)
    (hSecond : second ∈
      canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient) :
    canonicalScalarBoundarySymplecticForm first second = 0 := by
  change valueCoefficient * first.1 + normalCoefficient * first.2 = 0 at hFirst
  change valueCoefficient * second.1 + normalCoefficient * second.2 = 0 at hSecond
  by_cases hNormalCoefficient : normalCoefficient = 0
  · have hValueCoefficient : valueCoefficient ≠ 0 :=
      hNondegenerate.resolve_right (fun h => h hNormalCoefficient)
    have hFirstValue : first.1 = 0 := by
      have h : valueCoefficient * first.1 = 0 := by
        simpa [hNormalCoefficient] using hFirst
      exact (mul_eq_zero.mp h).resolve_left hValueCoefficient
    have hSecondValue : second.1 = 0 := by
      have h : valueCoefficient * second.1 = 0 := by
        simpa [hNormalCoefficient] using hSecond
      exact (mul_eq_zero.mp h).resolve_left hValueCoefficient
    simp [canonicalScalarBoundarySymplecticForm, hFirstValue, hSecondValue]
  · have hMultiple : normalCoefficient *
        canonicalScalarBoundarySymplecticForm first second = 0 := by
      calc
        normalCoefficient * canonicalScalarBoundarySymplecticForm first second =
            first.1 *
                (valueCoefficient * second.1 + normalCoefficient * second.2) -
              second.1 *
                (valueCoefficient * first.1 + normalCoefficient * first.2) := by
          unfold canonicalScalarBoundarySymplecticForm
          ring
        _ = 0 := by rw [hFirst, hSecond]; ring
    exact (mul_eq_zero.mp hMultiple).resolve_left hNormalCoefficient

/-- Symplectic orthogonal of a boundary submodule. -/
def canonicalScalarBoundarySymplecticOrthogonal
    (subspace : Submodule Real CanonicalScalarBoundaryDatum) :
    Set CanonicalScalarBoundaryDatum :=
  {datum | ∀ test ∈ subspace,
    canonicalScalarBoundarySymplecticForm datum test = 0}

/-- A separated line is contained in its symplectic orthogonal. -/
theorem canonicalScalarSeparatedBoundaryLine_le_symplecticOrthogonal
    (valueCoefficient normalCoefficient : Real)
    (hNondegenerate : valueCoefficient ≠ 0 ∨ normalCoefficient ≠ 0) :
    (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient :
        Set CanonicalScalarBoundaryDatum) ⊆
      canonicalScalarBoundarySymplecticOrthogonal
        (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient) := by
  intro datum hDatum test hTest
  exact canonicalScalarBoundarySymplecticForm_eq_zero_of_mem_separated
    valueCoefficient normalCoefficient hNondegenerate datum test hDatum hTest

/-- Testing against the canonical generator shows that the symplectic
orthogonal is contained in the original separated line. -/
theorem canonicalScalarBoundarySymplecticOrthogonal_le_separatedLine
    (valueCoefficient normalCoefficient : Real) :
    canonicalScalarBoundarySymplecticOrthogonal
        (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient) ⊆
      (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient :
        Set CanonicalScalarBoundaryDatum) := by
  intro datum hDatum
  have hGenerator := hDatum
    (canonicalScalarSeparatedBoundaryGenerator valueCoefficient normalCoefficient)
    (canonicalScalarSeparatedBoundaryGenerator_mem
      valueCoefficient normalCoefficient)
  change valueCoefficient * datum.1 + normalCoefficient * datum.2 = 0
  unfold canonicalScalarBoundarySymplecticForm
    canonicalScalarSeparatedBoundaryGenerator at hGenerator
  dsimp at hGenerator
  linarith

/-- Every nondegenerate separated scalar boundary line is Lagrangian: it equals
its symplectic orthogonal. -/
theorem canonicalScalarSeparatedBoundaryLine_symplecticOrthogonal_eq
    (valueCoefficient normalCoefficient : Real)
    (hNondegenerate : valueCoefficient ≠ 0 ∨ normalCoefficient ≠ 0) :
    canonicalScalarBoundarySymplecticOrthogonal
        (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient) =
      (canonicalScalarSeparatedBoundaryLine valueCoefficient normalCoefficient :
        Set CanonicalScalarBoundaryDatum) := by
  apply Set.Subset.antisymm
  · exact canonicalScalarBoundarySymplecticOrthogonal_le_separatedLine
      valueCoefficient normalCoefficient
  · exact canonicalScalarSeparatedBoundaryLine_le_symplecticOrthogonal
      valueCoefficient normalCoefficient hNondegenerate

/-- Pointwise separated boundary sections with variable real coefficients. -/
def canonicalScalarSeparatedBoundarySectionSubmodule
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    Submodule Real CanonicalScalarBoundarySection where
  carrier := {section | ∀ base,
    section base ∈ canonicalScalarSeparatedBoundaryLine
      (valueCoefficient base) (normalCoefficient base)}
  zero_mem' := by
    intro base
    exact (canonicalScalarSeparatedBoundaryLine
      (valueCoefficient base) (normalCoefficient base)).zero_mem
  add_mem' := by
    intro first second hFirst hSecond base
    exact (canonicalScalarSeparatedBoundaryLine
      (valueCoefficient base) (normalCoefficient base)).add_mem
        (hFirst base) (hSecond base)
  smul_mem' := by
    intro scalar section hSection base
    exact (canonicalScalarSeparatedBoundaryLine
      (valueCoefficient base) (normalCoefficient base)).smul_mem scalar
        (hSection base)

@[simp] theorem mem_canonicalScalarSeparatedBoundarySectionSubmodule
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (section : CanonicalScalarBoundarySection) :
    section ∈ canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient ↔
      ∀ base,
        valueCoefficient base * (section base).1 +
          normalCoefficient base * (section base).2 = 0 := by
  rfl

/-- Pointwise symplectic orthogonal of a boundary-section submodule. -/
def canonicalScalarBoundarySectionPointwiseOrthogonal
    (subspace : Submodule Real CanonicalScalarBoundarySection) :
    Set CanonicalScalarBoundarySection :=
  {section | ∀ test ∈ subspace, ∀ base,
    canonicalScalarBoundarySymplecticForm (section base) (test base) = 0}

/-- The variable-coefficient separated section space is pointwise isotropic. -/
theorem canonicalScalarSeparatedBoundarySection_le_pointwiseOrthogonal
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0) :
    (canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient : Set CanonicalScalarBoundarySection) ⊆
      canonicalScalarBoundarySectionPointwiseOrthogonal
        (canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient) := by
  intro section hSection test hTest base
  exact canonicalScalarBoundarySymplecticForm_eq_zero_of_mem_separated
    (valueCoefficient base) (normalCoefficient base) (hNondegenerate base)
      (section base) (test base) (hSection base) (hTest base)

/-- The global generator section detects every datum outside the separated
section space. -/
theorem canonicalScalarBoundarySectionPointwiseOrthogonal_le_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarBoundarySectionPointwiseOrthogonal
        (canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient) ⊆
      (canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient : Set CanonicalScalarBoundarySection) := by
  intro section hSection
  let generator : CanonicalScalarBoundarySection := fun base =>
    canonicalScalarSeparatedBoundaryGenerator
      (valueCoefficient base) (normalCoefficient base)
  have hGenerator : generator ∈
      canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient := by
    intro base
    exact canonicalScalarSeparatedBoundaryGenerator_mem
      (valueCoefficient base) (normalCoefficient base)
  intro base
  have hAt := hSection generator hGenerator base
  change valueCoefficient base * (section base).1 +
    normalCoefficient base * (section base).2 = 0
  dsimp [generator, canonicalScalarSeparatedBoundaryGenerator] at hAt
  unfold canonicalScalarBoundarySymplecticForm at hAt
  linarith

/-- Variable nondegenerate separated boundary sections are maximally isotropic
for the pointwise Green form. -/
theorem canonicalScalarSeparatedBoundarySection_pointwiseOrthogonal_eq
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0) :
    canonicalScalarBoundarySectionPointwiseOrthogonal
        (canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient) =
      (canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient : Set CanonicalScalarBoundarySection) := by
  apply Set.Subset.antisymm
  · exact canonicalScalarBoundarySectionPointwiseOrthogonal_le_separated
      valueCoefficient normalCoefficient
  · exact canonicalScalarSeparatedBoundarySection_le_pointwiseOrthogonal
      valueCoefficient normalCoefficient hNondegenerate

/-- Membership of the smooth trace section is exactly the previously defined
separated boundary condition. -/
theorem canonicalLatitudeScalarSeparatedBoundaryCondition_iff_boundarySection_mem
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
        valueCoefficient normalCoefficient field ↔
      canonicalLatitudeScalarBoundarySection period hPeriod field ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient := by
  rfl

/-- The measured symplectic pairing vanishes on every common separated boundary
section. -/
theorem canonicalScalarBoundarySectionGreenPairing_eq_zero_of_mem_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (first second : CanonicalScalarBoundarySection)
    (hFirst : first ∈ canonicalScalarSeparatedBoundarySectionSubmodule
      valueCoefficient normalCoefficient)
    (hSecond : second ∈ canonicalScalarSeparatedBoundarySectionSubmodule
      valueCoefficient normalCoefficient) :
    canonicalScalarBoundarySectionGreenPairing period first second = 0 := by
  apply canonicalScalarBoundarySectionGreenPairing_eq_zero_of_pointwise
  intro base
  exact canonicalScalarBoundarySymplecticForm_eq_zero_of_mem_separated
    (valueCoefficient base) (normalCoefficient base) (hNondegenerate base)
      (first base) (second base) (hFirst base) (hSecond base)

/-- The exact two-sheet global pairing also vanishes on the separated section
space. -/
theorem canonicalScalarGlobalBoundarySectionGreenPairing_eq_zero_of_mem_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (first second : CanonicalScalarBoundarySection)
    (hFirst : first ∈ canonicalScalarSeparatedBoundarySectionSubmodule
      valueCoefficient normalCoefficient)
    (hSecond : second ∈ canonicalScalarSeparatedBoundarySectionSubmodule
      valueCoefficient normalCoefficient) :
    canonicalScalarGlobalBoundarySectionGreenPairing period first second = 0 := by
  rw [canonicalScalarGlobalBoundarySectionGreenPairing,
    canonicalScalarBoundarySectionGreenPairing_eq_zero_of_mem_separated
      period valueCoefficient normalCoefficient hNondegenerate
        first second hFirst hSecond]
  ring

/-- The smooth separated condition is therefore a genuine Lagrangian boundary
condition, not merely an isotropic test. -/
theorem canonicalLatitudeScalarSeparatedBoundary_lagrangian_certificate
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    (CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
        valueCoefficient normalCoefficient field ↔
      canonicalLatitudeScalarBoundarySection period hPeriod field ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient) ∧
      canonicalScalarBoundarySectionPointwiseOrthogonal
          (canonicalScalarSeparatedBoundarySectionSubmodule
            valueCoefficient normalCoefficient) =
        (canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient : Set CanonicalScalarBoundarySection) := by
  exact ⟨canonicalLatitudeScalarSeparatedBoundaryCondition_iff_boundarySection_mem
      period hPeriod valueCoefficient normalCoefficient field,
    canonicalScalarSeparatedBoundarySection_pointwiseOrthogonal_eq
      valueCoefficient normalCoefficient hNondegenerate⟩

end
end P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D
end JanusFormal
