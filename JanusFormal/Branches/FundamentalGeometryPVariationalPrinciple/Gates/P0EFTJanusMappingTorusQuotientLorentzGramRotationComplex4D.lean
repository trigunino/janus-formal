import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientDirection4D

/-!
# A concrete quotient `R/J` rotation subcomplex

The three descended spatial-rotation directions are genuine smooth
bundle-hom sections on the effective D8 quotient.  This gate pulls an
arbitrary such quotient section back through the quotient projection, writes
it in the same one-jet coordinates as the actual cover immersion, and applies
the genuine Frechet derivative of a Lorentz--Gram component.

For the sections on which that pullback is smooth and deck invariant, the
result descends to a smooth scalar field on the true quotient.  The three
concrete rotation sections lie in this domain, and their image is proved zero
by the already computed pointwise Frechet kernel identity.  Thus the displayed
statement is literally `J ∘ R = 0` for these quotient sections, rather than a
separately descended scalar field known in advance to be zero.

This is componentwise and restricted to the three spatial rotations.  It is
not the full global `K/J` complex, a Sobolev extension, or an exactness result.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusQuotientLorentzGramRotationComplex4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientDirection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev RotationAmbientCoordinates := ModelProd EuclideanR4 Real

private instance rotationAmbientNormedAddCommGroup :
    NormedAddCommGroup RotationAmbientCoordinates :=
  inferInstanceAs (NormedAddCommGroup (EuclideanR4 × Real))

private instance rotationAmbientNormedSpace :
    NormedSpace Real RotationAmbientCoordinates :=
  inferInstanceAs (NormedSpace Real (EuclideanR4 × Real))

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev CoverTangent
    (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev QuotientTangent
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev QuotientAmbientFiber :=
  Bundle.Trivial (EffectiveQuotient period hPeriod) RotationAmbientCoordinates

private abbrev QuotientAmbientHomFiber
    (point : EffectiveQuotient period hPeriod) :=
  QuotientTangent period hPeriod point →L[Real]
    QuotientAmbientFiber period hPeriod point

/-- Smooth quotient sections on the same ambient bundle-hom fiber as the
descended rotation directions. -/
abbrev QuotientLorentzGramAmbientHomSection :=
  ContMDiffSection coverModelWithCorners
    (CoverCoordinates →L[Real] RotationAmbientCoordinates) ∞
    (QuotientAmbientHomFiber period hPeriod)

/-- The concrete quotient rotation operator `R`. -/
def quotientLorentzGramRotationOperator (axis : Fin 3) :
    QuotientLorentzGramAmbientHomSection period hPeriod :=
  smoothQuotientLorentzGramRotationHom period hPeriod axis

/-- Pull a quotient bundle-hom section back to the cover and express it in
the fixed one-jet coordinates used by the Frechet Gram map. -/
def quotientLorentzGramSectionPullbackJet
    (homSection : QuotientLorentzGramAmbientHomSection period hPeriod)
    (point : EffectiveCover period hPeriod) : CoverLorentzOneJet :=
  (((homSection (mappingTorusMk (sphereData period hPeriod) point)).comp
      (mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod)) point)).comp
    ((trivializationAt CoverCoordinates
      (CoverTangent period hPeriod) point).symmL Real point))

/-- The pullback one-jet of `R` is exactly the already computed infinitesimal
rotation of the actual immersion one-jet. -/
theorem quotientLorentzGramRotationOperator_pullbackJet
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    quotientLorentzGramSectionPullbackJet period hPeriod
        (quotientLorentzGramRotationOperator period hPeriod axis) point =
      coverLorentzGramRotationDirection axis
        (coverAmbientDerivativeCoordinates period hPeriod point) := by
  unfold quotientLorentzGramSectionPullbackJet
  unfold quotientLorentzGramRotationOperator
  rw [smoothQuotientLorentzGramRotationHom_pullback]
  apply ContinuousLinearMap.ext
  intro vector
  rfl

/-- Pullback formula for the genuine component Jacobian `J`, applied to an
arbitrary smooth quotient ambient-hom section. -/
def quotientLorentzGramJacobianPullback
    (first second : CoverCoordinates)
    (homSection : QuotientLorentzGramAmbientHomSection period hPeriod)
    (point : EffectiveCover period hPeriod) : Real :=
  coverLorentzGramComponentLinearization first second
    (coverAmbientDerivativeCoordinates period hPeriod point)
    (quotientLorentzGramSectionPullbackJet period hPeriod homSection point)

/-- Exact kernel calculation for the composite pullback `J ∘ R`. -/
theorem quotientLorentzGramJacobianPullback_rotation_zero
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveCover period hPeriod) :
    quotientLorentzGramJacobianPullback period hPeriod first second
        (quotientLorentzGramRotationOperator period hPeriod axis) point = 0 := by
  unfold quotientLorentzGramJacobianPullback
  rw [quotientLorentzGramRotationOperator_pullbackJet]
  exact actualCoverLorentzGramLinearization_rotation_zero period hPeriod
    axis point first second

/-- Domain on which the pullback formula for `J` genuinely defines a smooth
deck-invariant scalar field and hence descends to the quotient. -/
def QuotientLorentzGramJacobianAdmissible
    (first second : CoverCoordinates)
    (homSection : QuotientLorentzGramAmbientHomSection period hPeriod) : Prop :=
  ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (quotientLorentzGramJacobianPullback period hPeriod first second homSection) ∧
    ∀ (winding : Int) (point : EffectiveCover period hPeriod),
      quotientLorentzGramJacobianPullback period hPeriod first second homSection
          (winding +ᵥ point) =
        quotientLorentzGramJacobianPullback period hPeriod first second homSection
          point

/-- Admissible quotient sections for one displayed Lorentz--Gram component. -/
abbrev QuotientLorentzGramJacobianDomain
    (first second : CoverCoordinates) :=
  { candidate : QuotientLorentzGramAmbientHomSection period hPeriod //
    QuotientLorentzGramJacobianAdmissible period hPeriod first second candidate }

/-- Each concrete rotation section is in the actual descent domain of `J`. -/
theorem quotientLorentzGramRotationOperator_admissible
    (axis : Fin 3) (first second : CoverCoordinates) :
    QuotientLorentzGramJacobianAdmissible period hPeriod first second
      (quotientLorentzGramRotationOperator period hPeriod axis) := by
  constructor
  · have hZero :
        quotientLorentzGramJacobianPullback period hPeriod first second
            (quotientLorentzGramRotationOperator period hPeriod axis) =
          fun _ => 0 := by
      funext point
      exact quotientLorentzGramJacobianPullback_rotation_zero period hPeriod
        axis first second point
    rw [hZero]
    exact contMDiff_const
  · intro winding point
    rw [quotientLorentzGramJacobianPullback_rotation_zero,
      quotientLorentzGramJacobianPullback_rotation_zero]

/-- `R`, now valued in the genuine quotient domain of the component
Jacobian. -/
def quotientLorentzGramRotationIntoJacobianDomain
    (first second : CoverCoordinates) (axis : Fin 3) :
    QuotientLorentzGramJacobianDomain period hPeriod first second :=
  ⟨quotientLorentzGramRotationOperator period hPeriod axis,
    quotientLorentzGramRotationOperator_admissible period hPeriod axis
      first second⟩

/-- The scalar cover field obtained by applying the true Gram Jacobian
formula to an admissible quotient section. -/
def quotientLorentzGramJacobianCoverField
    (first second : CoverCoordinates)
    (homSection : QuotientLorentzGramJacobianDomain period hPeriod first second) :
    SmoothDeckInvariantField period hPeriod Real where
  toFun := quotientLorentzGramJacobianPullback period hPeriod first second
    homSection.1
  contMDiff_toFun := homSection.2.1
  deck_invariant := homSection.2.2

/-- The genuine quotient component Jacobian `J` on its descent domain. -/
def quotientLorentzGramJacobianOperator
    (first second : CoverCoordinates)
    (homSection : QuotientLorentzGramJacobianDomain period hPeriod first second) :
    SmoothQuotientField period hPeriod Real :=
  descendSmooth period hPeriod Real
    (quotientLorentzGramJacobianCoverField period hPeriod first second homSection)

/-- Literal componentwise `J ∘ R = 0` as a smooth scalar field on the true
D8 quotient. -/
theorem quotientLorentzGramJacobian_comp_rotation_eq_zero
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod) :
    quotientLorentzGramJacobianOperator period hPeriod first second
        (quotientLorentzGramRotationIntoJacobianDomain period hPeriod
          first second axis) point = 0 := by
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  change quotientLorentzGramJacobianPullback period hPeriod first second
      (quotientLorentzGramRotationOperator period hPeriod axis) coverPoint = 0
  exact quotientLorentzGramJacobianPullback_rotation_zero period hPeriod
    axis first second coverPoint

end

end P0EFTJanusMappingTorusQuotientLorentzGramRotationComplex4D
end JanusFormal
