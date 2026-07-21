import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D

/-!
# Concrete scalar Cauchy trace on the oriented cut boundary

The physical normal derivative does not descend as an ordinary scalar on the
one-sided throat: the mapping-torus generator reverses the normal.  It does
descend to the orientation-double boundary produced by cutting the throat.

Rather than repeating the complete quotient descent, the normal trace is
extracted canonically from the already descended Green current by pairing with
the constant unit field.  On the first latitude sheet this is exactly the
canonical latitude derivative.  The value trace is deck-even, the normal trace
is deck-odd, and their pointwise symplectic pairing is exactly the descended
scalar Green current.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D.cutThroatBoundaryChartedSpace
    period hPeriod

local instance cutBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D.cutThroatBoundary_isManifold
    period hPeriod

/-- Constant unit scalar on the physical quotient. -/
def canonicalScalarUnitField :
    SmoothQuotientField period hPeriod Real where
  toFun := fun _ => 1
  contMDiff_toFun := contMDiff_const

@[simp] theorem canonicalScalarUnitField_apply
    (point) : canonicalScalarUnitField period hPeriod point = 1 :=
  rfl

/-- Every point of the connected orientation-double boundary has a latitude
first-sheet representative.  The time coordinate is not restricted here; the
quotient performs the doubled-period identification. -/
theorem canonicalLatitudeCutBoundaryFirstLift_surjective :
    Function.Surjective
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod) := by
  intro boundary
  refine Quotient.inductionOn boundary ?_
  intro representative
  refine ⟨(equatorialTwoSphereHomeomorph representative.fiber,
      representative.time), ?_⟩
  apply congrArg
    (mappingTorusMk (orientationDoubleData period hPeriod))
  apply MappingTorusCover.ext
  · simp [canonicalLatitudeCutBoundaryFirstLift]
  · rfl

/-- Boundary value trace on the exact oriented cut boundary. -/
def cutBoundaryScalarValueTrace
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  field (cutThroatBoundaryToBulk period hPeriod boundary)

/-- The normal trace is the Green current against the constant unit scalar.
The sign is chosen so that the first sheet gives the increasing latitude
normal derivative. -/
def cutBoundaryScalarNormalTrace
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  -cutBoundaryScalarCurrent period hPeriod field
    (canonicalScalarUnitField period hPeriod) boundary

/-- The value trace on the first sheet is the canonical latitude value. -/
theorem cutBoundaryScalarValueTrace_firstLift
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutBoundaryScalarValueTrace period hPeriod field
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) =
      canonicalLatitudeValue period hPeriod field base 0 := by
  rw [canonicalLatitudeValue_zero]
  rfl

/-- The canonical latitude derivative is additive in the smooth scalar field. -/
theorem canonicalLatitudeDerivative_add
    (first second : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod (first + second) base normal =
      canonicalLatitudeDerivative period hPeriod first base normal +
        canonicalLatitudeDerivative period hPeriod second base normal := by
  have hTarget := canonicalLatitudeValue_hasDerivAt period hPeriod
    (first + second) base normal
  have hSum :=
    (canonicalLatitudeValue_hasDerivAt period hPeriod first base normal).add
      (canonicalLatitudeValue_hasDerivAt period hPeriod second base normal)
  have hFunction :
      canonicalLatitudeValue period hPeriod (first + second) base =
        fun current =>
          canonicalLatitudeValue period hPeriod first base current +
            canonicalLatitudeValue period hPeriod second base current :=
    rfl
  rw [hFunction] at hTarget
  exact hTarget.unique hSum

/-- The canonical latitude derivative is homogeneous in the smooth scalar
field. -/
theorem canonicalLatitudeDerivative_smul
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod (scalar • field) base normal =
      scalar • canonicalLatitudeDerivative period hPeriod field base normal := by
  have hTarget := canonicalLatitudeValue_hasDerivAt period hPeriod
    (scalar • field) base normal
  have hScaled :=
    (canonicalLatitudeValue_hasDerivAt period hPeriod field base normal).const_mul
      scalar
  have hFunction :
      canonicalLatitudeValue period hPeriod (scalar • field) base =
        fun current =>
          scalar * canonicalLatitudeValue period hPeriod field base current :=
    rfl
  rw [hFunction] at hTarget
  simpa [smul_eq_mul] using hTarget.unique hScaled

/-- The normal trace on the first sheet is the genuine canonical latitude
normal derivative. -/
theorem cutBoundaryScalarNormalTrace_firstLift
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutBoundaryScalarNormalTrace period hPeriod field
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) =
      canonicalLatitudeDerivative period hPeriod field base 0 := by
  rw [cutBoundaryScalarNormalTrace,
    cutBoundaryScalarCurrent_firstLift]
  unfold canonicalLatitudeScalarGreenCurrent
  simp [canonicalScalarUnitField, canonicalLatitudeValue,
    canonicalLatitudeDerivative, canonicalNormalSlice]

/-- The value trace is additive. -/
theorem cutBoundaryScalarValueTrace_add
    (first second : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarValueTrace period hPeriod (first + second) boundary =
      cutBoundaryScalarValueTrace period hPeriod first boundary +
        cutBoundaryScalarValueTrace period hPeriod second boundary :=
  rfl

/-- The value trace is homogeneous. -/
theorem cutBoundaryScalarValueTrace_smul
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarValueTrace period hPeriod (scalar • field) boundary =
      scalar • cutBoundaryScalarValueTrace period hPeriod field boundary :=
  rfl

/-- The normal trace is additive. -/
theorem cutBoundaryScalarNormalTrace_add
    (first second : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarNormalTrace period hPeriod (first + second) boundary =
      cutBoundaryScalarNormalTrace period hPeriod first boundary +
        cutBoundaryScalarNormalTrace period hPeriod second boundary := by
  obtain ⟨base, rfl⟩ :=
    canonicalLatitudeCutBoundaryFirstLift_surjective period hPeriod boundary
  rw [cutBoundaryScalarNormalTrace_firstLift,
    cutBoundaryScalarNormalTrace_firstLift,
    cutBoundaryScalarNormalTrace_firstLift,
    canonicalLatitudeDerivative_add]

/-- The normal trace is homogeneous. -/
theorem cutBoundaryScalarNormalTrace_smul
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarNormalTrace period hPeriod (scalar • field) boundary =
      scalar • cutBoundaryScalarNormalTrace period hPeriod field boundary := by
  obtain ⟨base, rfl⟩ :=
    canonicalLatitudeCutBoundaryFirstLift_surjective period hPeriod boundary
  rw [cutBoundaryScalarNormalTrace_firstLift,
    cutBoundaryScalarNormalTrace_firstLift,
    canonicalLatitudeDerivative_smul]

/-- The boundary value trace is continuous. -/
theorem cutBoundaryScalarValueTrace_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBoundaryScalarValueTrace period hPeriod field) :=
  field.contMDiff_toFun.continuous.comp
    (continuous_cutThroatBoundaryToBulk period hPeriod)

/-- The boundary normal trace is continuous. -/
theorem cutBoundaryScalarNormalTrace_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBoundaryScalarNormalTrace period hPeriod field) := by
  exact (cutBoundaryScalarCurrent_contMDiff period hPeriod field
    (canonicalScalarUnitField period hPeriod)).continuous.neg

/-- Value trace as a linear map into continuous boundary functions. -/
def cutBoundaryScalarValueTraceContinuousMap :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      C(CutThroatBoundary period hPeriod, Real) where
  toFun field :=
    ⟨cutBoundaryScalarValueTrace period hPeriod field,
      cutBoundaryScalarValueTrace_continuous period hPeriod field⟩
  map_add' first second := by
    ext boundary
    exact cutBoundaryScalarValueTrace_add period hPeriod first second boundary
  map_smul' scalar field := by
    ext boundary
    exact cutBoundaryScalarValueTrace_smul period hPeriod scalar field boundary

/-- Normal trace as a linear map into continuous boundary functions. -/
def cutBoundaryScalarNormalTraceContinuousMap :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      C(CutThroatBoundary period hPeriod, Real) where
  toFun field :=
    ⟨cutBoundaryScalarNormalTrace period hPeriod field,
      cutBoundaryScalarNormalTrace_continuous period hPeriod field⟩
  map_add' first second := by
    ext boundary
    exact cutBoundaryScalarNormalTrace_add period hPeriod first second boundary
  map_smul' scalar field := by
    ext boundary
    exact cutBoundaryScalarNormalTrace_smul period hPeriod scalar field boundary

/-- Boundary values are invariant under the residual deck involution. -/
theorem cutBoundaryScalarValueTrace_deck
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarValueTrace period hPeriod field
        (orientationDeck period hPeriod boundary) =
      cutBoundaryScalarValueTrace period hPeriod field boundary := by
  unfold cutBoundaryScalarValueTrace
  rw [cutThroatBoundaryToBulk_deck]

/-- Boundary normal derivatives are odd under the residual deck involution. -/
theorem cutBoundaryScalarNormalTrace_deck
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarNormalTrace period hPeriod field
        (orientationDeck period hPeriod boundary) =
      -cutBoundaryScalarNormalTrace period hPeriod field boundary := by
  unfold cutBoundaryScalarNormalTrace
  rw [cutBoundaryScalarCurrent_deck]
  ring

/-- The descended Green current is exactly the pointwise symplectic pairing of
value and normal traces. -/
theorem cutBoundaryScalarCurrent_eq_cauchyPairing
    (field test : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarCurrent period hPeriod field test boundary =
      cutBoundaryScalarValueTrace period hPeriod field boundary *
          cutBoundaryScalarNormalTrace period hPeriod test boundary -
        cutBoundaryScalarNormalTrace period hPeriod field boundary *
          cutBoundaryScalarValueTrace period hPeriod test boundary := by
  obtain ⟨base, rfl⟩ :=
    canonicalLatitudeCutBoundaryFirstLift_surjective period hPeriod boundary
  rw [cutBoundaryScalarCurrent_firstLift,
    cutBoundaryScalarValueTrace_firstLift,
    cutBoundaryScalarValueTrace_firstLift,
    cutBoundaryScalarNormalTrace_firstLift,
    cutBoundaryScalarNormalTrace_firstLift]
  rfl

/-- Concrete Cauchy-trace certificate on the exact oriented boundary. -/
theorem cutBoundaryScalarCauchyTrace_certificate
    (field test : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBoundaryScalarValueTrace period hPeriod field) ∧
      Continuous (cutBoundaryScalarNormalTrace period hPeriod field) ∧
      (∀ boundary,
        cutBoundaryScalarCurrent period hPeriod field test boundary =
          cutBoundaryScalarValueTrace period hPeriod field boundary *
              cutBoundaryScalarNormalTrace period hPeriod test boundary -
            cutBoundaryScalarNormalTrace period hPeriod field boundary *
              cutBoundaryScalarValueTrace period hPeriod test boundary) ∧
      (∀ boundary,
        cutBoundaryScalarValueTrace period hPeriod field
            (orientationDeck period hPeriod boundary) =
          cutBoundaryScalarValueTrace period hPeriod field boundary) ∧
      (∀ boundary,
        cutBoundaryScalarNormalTrace period hPeriod field
            (orientationDeck period hPeriod boundary) =
          -cutBoundaryScalarNormalTrace period hPeriod field boundary) :=
  ⟨cutBoundaryScalarValueTrace_continuous period hPeriod field,
    cutBoundaryScalarNormalTrace_continuous period hPeriod field,
    cutBoundaryScalarCurrent_eq_cauchyPairing period hPeriod field test,
    cutBoundaryScalarValueTrace_deck period hPeriod field,
    cutBoundaryScalarNormalTrace_deck period hPeriod field⟩

end
end P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D
end JanusFormal
