import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-!
# PT-symmetrized differential LL weak action on the actual throat

The partition-of-unity tangent generators used by the differential LL energy
are not canonically PT-equivariant.  Instead of assuming such equivariance,
this gate performs the standard finite-group average of the entire global
functional over the actual throat PT involution.  The resulting action is
exactly PT invariant for every measure (hence in particular for every
PT-invariant finite Borel measure).

The affine flux variation commutes with PT pullback.  This yields an exact
quadratic action expansion, its actual first derivative, a PT-covariant weak
Euler pairing, and invariance of the weak solution space.  This is covariance
of the averaged weak model; it does not turn the generator energy into an
intrinsic Lorentzian inverse-metric contraction or supply a strong divergence
equation and boundary flux theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- PT pullback of a smooth LL flux test field. -/
def differentialLLFluxDirectionPT
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  throatPTPullback period hPeriod LLFieldFiber direction

/-- PT pullback of an auxiliary-metric test field. -/
def differentialLLAuxMetricDirectionPT
    (direction : SmoothThroatField period hPeriod LLMetricFiber) :
    SmoothThroatField period hPeriod LLMetricFiber :=
  throatPTPullback period hPeriod LLMetricFiber direction

@[simp]
theorem differentialLLFluxDirectionPT_involutive
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    differentialLLFluxDirectionPT period hPeriod
        (differentialLLFluxDirectionPT period hPeriod direction) = direction :=
  throatPTPullback_involutive period hPeriod LLFieldFiber direction

@[simp]
theorem differentialLLAuxMetricDirectionPT_involutive
    (direction : SmoothThroatField period hPeriod LLMetricFiber) :
    differentialLLAuxMetricDirectionPT period hPeriod
        (differentialLLAuxMetricDirectionPT period hPeriod direction) = direction :=
  throatPTPullback_involutive period hPeriod LLMetricFiber direction

private theorem throatPTPullback_add
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    throatPTPullback period hPeriod LLFieldFiber (first + second) =
      throatPTPullback period hPeriod LLFieldFiber first +
        throatPTPullback period hPeriod LLFieldFiber second := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  rfl

private theorem throatPTPullback_smul
    (scalar : Real)
    (field : SmoothThroatField period hPeriod LLFieldFiber) :
    throatPTPullback period hPeriod LLFieldFiber (scalar • field) =
      scalar • throatPTPullback period hPeriod LLFieldFiber field := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  rfl

/-- The actual affine LL flux curve commutes with the throat PT pullback. -/
theorem llPTPullback_differentialLLFluxCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) :
    llPTPullback period hPeriod
        (differentialLLFluxCurve period hPeriod fields direction epsilon) =
      differentialLLFluxCurve period hPeriod
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod direction) epsilon := by
  cases fields
  simp only [llPTPullback, differentialLLFluxCurve,
    differentialLLFluxDirectionPT]
  rw [throatPTPullback_add, throatPTPullback_smul]

/-- Finite-group average of the differential LL action over the actual throat
PT involution. -/
def globalPTSymmetricDifferentialLLAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    (globalDifferentialLLAction period hPeriod frame fields mu +
      globalDifferentialLLAction period hPeriod frame
        (llPTPullback period hPeriod fields) mu)

/-- Exact PT invariance of the averaged differential action.  No
measure-preservation hypothesis is needed because the complete functional,
not merely its integration variable, is averaged over the finite orbit. -/
theorem globalPTSymmetricDifferentialLLAction_pt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (llPTPullback period hPeriod fields) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu := by
  unfold globalPTSymmetricDifferentialLLAction
  rw [llPTPullback_involutive]
  ring

/-- PT-averaged weak Euler pairing. -/
def globalPTSymmetricDifferentialLLFluxFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    (globalDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu +
      globalDifferentialLLFluxFirstVariation period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod direction) mu)

/-- Public quadratic coefficient recovered from the exact raw action curve at
unit parameter.  This avoids exposing the implementation-private coefficient
of the preceding gate. -/
def globalDifferentialLLFluxQuadraticCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalDifferentialLLAction period hPeriod frame
      (differentialLLFluxCurve period hPeriod fields direction 1) mu -
    globalDifferentialLLAction period hPeriod frame fields mu -
    globalDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu

/-- The recovered coefficient gives the same exact raw quadratic expansion. -/
theorem globalDifferentialLLAction_fluxCurve_quadratic_public
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu =
      globalDifferentialLLAction period hPeriod frame fields mu +
        epsilon * globalDifferentialLLFluxFirstVariation period hPeriod
          frame fields direction mu +
        epsilon ^ 2 * globalDifferentialLLFluxQuadraticCoefficient period hPeriod
          frame fields direction mu := by
  have hEpsilon := globalDifferentialLLAction_fluxCurve_quadratic
    period hPeriod frame fields direction mu epsilon
  have hOne := globalDifferentialLLAction_fluxCurve_quadratic
    period hPeriod frame fields direction mu 1
  unfold globalDifferentialLLFluxQuadraticCoefficient
  rw [hEpsilon, hOne]
  ring

private def globalPTSymmetricDifferentialLLFluxSecondCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
  (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    (globalDifferentialLLFluxQuadraticCoefficient period hPeriod
        frame fields direction mu +
      globalDifferentialLLFluxQuadraticCoefficient period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod direction) mu)

/-- Exact quadratic expansion of the PT-averaged action along the original
global affine flux curve. -/
theorem globalPTSymmetricDifferentialLLAction_fluxCurve_quadratic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu +
        epsilon *
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
            frame fields direction mu +
        epsilon ^ 2 *
          globalPTSymmetricDifferentialLLFluxSecondCoefficient period hPeriod
            frame fields direction mu := by
  unfold globalPTSymmetricDifferentialLLAction
  rw [llPTPullback_differentialLLFluxCurve period hPeriod
    fields direction epsilon]
  rw [globalDifferentialLLAction_fluxCurve_quadratic_public period hPeriod
    frame fields direction mu epsilon]
  rw [globalDifferentialLLAction_fluxCurve_quadratic_public period hPeriod frame
    (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod direction) mu epsilon]
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
    globalPTSymmetricDifferentialLLFluxSecondCoefficient
  ring

private theorem quadratic_scalar_hasDerivAt
    (base linear quadratic : Real) :
    HasDerivAt
      (fun epsilon : Real => base + epsilon * linear + epsilon ^ 2 * quadratic)
      linear 0 := by
  have hAffine : HasDerivAt
      (fun epsilon : Real => base + epsilon * linear) linear 0 := by
    have h := (hasDerivAt_id (0 : Real)).mul_const linear |>.const_add base
    exact h.congr_deriv (one_mul linear)
  have hSquare : HasDerivAt (fun epsilon : Real => epsilon * epsilon) 0 0 := by
    have h := (hasDerivAt_id (0 : Real)).mul (hasDerivAt_id (0 : Real))
    exact h.congr_deriv (by norm_num)
  have hQuadratic : HasDerivAt
      (fun epsilon : Real => epsilon * epsilon * quadratic) 0 0 := by
    exact (hSquare.mul_const quadratic).congr_deriv (by ring)
  have hTotal := hAffine.add hQuadratic
  exact (hTotal.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun epsilon => by
      simp only [Pi.add_apply]
      ring)

/-- Actual first derivative of the averaged action. -/
theorem globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (differentialLLFluxCurve period hPeriod
            fields direction epsilon) mu)
      (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu) 0 := by
  rw [show (fun epsilon : Real =>
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod
          fields direction epsilon) mu) =
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu +
          epsilon *
            globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
              frame fields direction mu +
          epsilon ^ 2 *
            globalPTSymmetricDifferentialLLFluxSecondCoefficient period hPeriod
              frame fields direction mu) from by
      funext epsilon
      exact globalPTSymmetricDifferentialLLAction_fluxCurve_quadratic
        period hPeriod frame fields direction mu epsilon]
  exact quadratic_scalar_hasDerivAt
    (globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu)
    (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu)
    (globalPTSymmetricDifferentialLLFluxSecondCoefficient period hPeriod
      frame fields direction mu)

/-- The averaged first variation transforms covariantly with both the field
and its test direction. -/
theorem globalPTSymmetricDifferentialLLFluxFirstVariation_pt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod direction) mu =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        fields direction mu := by
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
  rw [llPTPullback_involutive,
    differentialLLFluxDirectionPT_involutive]
  ring

/-- PT-covariant weak first-order Euler equation of the averaged model. -/
def SatisfiesPTSymmetricWeakDifferentialLLEquation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu = 0

theorem satisfiesPTSymmetricWeakDifferentialLLEquation_pt_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod frame
        (llPTPullback period hPeriod fields) mu ↔
      SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod frame
        fields mu := by
  constructor
  · intro hPT direction
    have hValue := hPT
      (differentialLLFluxDirectionPT period hPeriod direction)
    rw [globalPTSymmetricDifferentialLLFluxFirstVariation_pt period hPeriod
      frame fields direction mu] at hValue
    exact hValue
  · intro h direction
    have hValue := h
      (differentialLLFluxDirectionPT period hPeriod direction)
    have hCovariance :=
      globalPTSymmetricDifferentialLLFluxFirstVariation_pt period hPeriod
        frame fields
          (differentialLLFluxDirectionPT period hPeriod direction) mu
    rw [differentialLLFluxDirectionPT_involutive] at hCovariance
    rw [hCovariance]
    exact hValue

/-- Actual stationarity of the averaged functional. -/
def PTSymmetricDifferentialLLFluxStationary
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    HasDerivAt
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (differentialLLFluxCurve period hPeriod
            fields direction epsilon) mu)
      0 0

theorem ptSymmetricDifferentialLLFluxStationary_iff_weakEquation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    PTSymmetricDifferentialLLFluxStationary period hPeriod frame fields mu ↔
      SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        frame fields mu := by
  constructor
  · intro hStationary direction
    have hDerived :=
      globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt
        period hPeriod frame fields direction mu
    exact hDerived.unique (hStationary direction)
  · intro hWeak direction
    simpa [hWeak direction] using
      (globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt
        period hPeriod frame fields direction mu)

/-- PT preserves the actual stationary solution space, not merely the written
weak equation. -/
theorem ptSymmetricDifferentialLLFluxStationary_pt_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    PTSymmetricDifferentialLLFluxStationary period hPeriod frame
        (llPTPullback period hPeriod fields) mu ↔
      PTSymmetricDifferentialLLFluxStationary period hPeriod frame fields mu := by
  rw [ptSymmetricDifferentialLLFluxStationary_iff_weakEquation,
    ptSymmetricDifferentialLLFluxStationary_iff_weakEquation]
  exact satisfiesPTSymmetricWeakDifferentialLLEquation_pt_iff
    period hPeriod frame fields mu

/-- Compact unconditional closure on the previously constructed finite smooth
spanning family of the actual compact throat. -/
theorem actual_throat_pt_symmetric_differential_ll_closure
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod)
          (llPTPullback period hPeriod fields) mu =
        globalPTSymmetricDifferentialLLAction period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu ∧
      (PTSymmetricDifferentialLLFluxStationary period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu ↔
        SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu) ∧
      (SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod)
          (llPTPullback period hPeriod fields) mu ↔
        SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu) := by
  exact ⟨globalPTSymmetricDifferentialLLAction_pt period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu,
    ptSymmetricDifferentialLLFluxStationary_iff_weakEquation period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu,
    satisfiesPTSymmetricWeakDifferentialLLEquation_pt_iff period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu⟩

end

end P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
end JanusFormal
