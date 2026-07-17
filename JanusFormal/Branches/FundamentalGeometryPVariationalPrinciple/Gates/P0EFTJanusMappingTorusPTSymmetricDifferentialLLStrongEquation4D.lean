import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.MeasureTheory.Measure.OpenPos
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

/-!
# Strong PT-symmetric differential LL equation on the actual throat

The existing differential LL action uses the actual finite smooth spanning
family of the throat tangent bundle and the positive scalar coefficient
`1 + ‖llAuxMetric‖²`.  This gate constructs the corresponding weighted frame
flux, its frame divergence, the raw strong Euler field and its PT average.

The current `LLMetricFiber` is only an unconstrained Euclidean `3 x 3` array:
there is no symmetric, nondegenerate inverse-metric API from which a genuine
`gamma^{ab}` contraction could honestly be formed.  Consequently this module
uses exactly the scalar auxiliary-metric weight already present in the action;
it does not claim an inverse-metric upgrade.

The only contracted geometry is the global integration-by-parts formula and
its boundary flux.  Smooth tests detect a smooth residual pointwise for every
finite full-support measure, which is proved here rather than assumed.  Under
the zero-flux boundary condition, the existing weak Euler equation is then
equivalent to the pointwise strong PDE.  No ambient LL embedding, null rigging
or Stokes theorem is assumed silently.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Topology
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
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact analytic regularity missing from the current manifold-derivative
API.  Mathlib proves the frame derivative is `C∞`, but `SmoothThroatField`
currently means analytic (`ω`), so no invalid `C∞ → ω` promotion is made.
This single witness realizes each LL frame derivative analytically and may be
used twice to construct the weighted flux and its divergence. -/
structure LLStrongAnalyticRegularityContract
    (frame : SmoothThroatGeneratingFrame period hPeriod) where
  derivativeComponent :
    SmoothThroatField period hPeriod LLFieldFiber →
      Fin frame.count → SmoothThroatField period hPeriod LLFieldFiber
  derivativeComponent_apply :
    ∀ (field : SmoothThroatField period hPeriod LLFieldFiber)
      (index : Fin frame.count) (point : EffectiveThroat period hPeriod),
      derivativeComponent field index point =
        throatFrameDerivative period hPeriod LLFieldFiber frame
          field point index

/-- Analytic representative supplied for one genuine LL frame derivative. -/
def throatFrameDerivativeComponent
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (index : Fin frame.count) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  regularity.derivativeComponent field index

@[simp]
theorem throatFrameDerivativeComponent_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (index : Fin frame.count) (point : EffectiveThroat period hPeriod) :
    throatFrameDerivativeComponent period hPeriod frame regularity
        field index point =
      throatFrameDerivative period hPeriod LLFieldFiber frame
        field point index :=
  regularity.derivativeComponent_apply field index point

/-- Divergence associated with the finite smooth spanning family, assembled
from the analytic derivative representatives supplied by `regularity`. -/
def throatFrameDivergence
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (flux : Fin frame.count →
      SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod LLFieldFiber where
  toFun point :=
    ∑ index : Fin frame.count,
      throatFrameDerivativeComponent period hPeriod frame regularity
        (flux index) index point
  contMDiff_toFun := by
    apply contMDiff_finsetSum
    intro index _
    exact (throatFrameDerivativeComponent period hPeriod frame regularity
      (flux index) index).contMDiff_toFun

@[simp]
theorem throatFrameDivergence_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (flux : Fin frame.count →
      SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatFrameDivergence period hPeriod frame regularity flux point =
      ∑ index : Fin frame.count,
        throatFrameDerivative period hPeriod LLFieldFiber frame
          (flux index) point index := by
  simp [throatFrameDivergence]

/-- Smooth realization of the scalar auxiliary-metric coefficient used by the
unchanged differential LL action. -/
def smoothLLAuxiliaryKineticWeight
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun point :=
    1 + inner Real (fields.llAuxMetric point) (fields.llAuxMetric point)
  contMDiff_toFun := by
    have hPair :
        ContMDiff throatCoverModelWithCorners
          𝓘(Real, LLMetricFiber × LLMetricFiber) ω
          (fun point =>
            (fields.llAuxMetric point, fields.llAuxMetric point)) := by
      rw [contMDiff_prod_module_iff]
      exact ⟨fields.llAuxMetric.contMDiff_toFun,
        fields.llAuxMetric.contMDiff_toFun⟩
    have hInner :
        ContDiff Real ω
          (fun pair : LLMetricFiber × LLMetricFiber =>
            inner Real pair.1 pair.2) :=
      contDiff_inner
    exact contMDiff_const.add (hInner.contMDiff.comp hPair)

@[simp]
theorem smoothLLAuxiliaryKineticWeight_apply
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothLLAuxiliaryKineticWeight period hPeriod fields point =
      llAuxiliaryKineticWeight period hPeriod fields point := by
  simp only [smoothLLAuxiliaryKineticWeight, llAuxiliaryKineticWeight]
  rw [real_inner_self_eq_norm_sq]

/-- Frame flux `w D_i Phi` selected by the current differential LL action. -/
def scalarWeightedLLFrameFlux
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (index : Fin frame.count) :
    SmoothThroatField period hPeriod LLFieldFiber where
  toFun point :=
    smoothLLAuxiliaryKineticWeight period hPeriod fields point •
      throatFrameDerivativeComponent period hPeriod frame regularity
        fields.llField index point
  contMDiff_toFun :=
    (smoothLLAuxiliaryKineticWeight period hPeriod fields).contMDiff_toFun.smul
      (throatFrameDerivativeComponent period hPeriod frame regularity
        fields.llField index).contMDiff_toFun

@[simp]
theorem scalarWeightedLLFrameFlux_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (index : Fin frame.count) (point : EffectiveThroat period hPeriod) :
    scalarWeightedLLFrameFlux period hPeriod frame regularity
        fields index point =
      smoothLLAuxiliaryKineticWeight period hPeriod fields point •
        throatFrameDerivative period hPeriod LLFieldFiber frame
          fields.llField point index := by
  simp [scalarWeightedLLFrameFlux]

/-- The constructed weighted frame flux contracts with a test derivative to
exactly the kinetic pairing already present in the weak action. -/
theorem scalarWeightedLLFrameFlux_contracts_to_action
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    (∑ index : Fin frame.count,
      inner Real (scalarWeightedLLFrameFlux period hPeriod
        frame regularity fields index point)
        (throatFrameDerivative period hPeriod LLFieldFiber frame
          direction point index)) =
      llAuxiliaryKineticWeight period hPeriod fields point *
        throatDerivativePairing period hPeriod frame fields.llField
          direction point := by
  simp_rw [scalarWeightedLLFrameFlux_apply,
    smoothLLAuxiliaryKineticWeight_apply,
    real_inner_smul_left]
  simp [throatDerivativePairing, Finset.mul_sum]

/-- Weighted frame Laplacian/divergence `sum_i D_i (w D_i Phi)`. -/
def scalarWeightedLLFrameLaplacian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  throatFrameDivergence period hPeriod frame regularity
    (scalarWeightedLLFrameFlux period hPeriod frame regularity fields)

/-- Algebraic contribution `2 rho Phi` to the strong flux equation. -/
def algebraicLLStrongEulerField
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber where
  toFun point :=
    (2 * fields.llMeasure point) • fields.llField point
  contMDiff_toFun :=
    (contMDiff_const.mul fields.llMeasure.contMDiff_toFun).smul
      fields.llField.contMDiff_toFun

/-- Raw strong Euler field `-div_F(w D_F Phi) + 2 rho Phi`. -/
def strongDifferentialLLEulerField
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  -scalarWeightedLLFrameLaplacian period hPeriod frame regularity fields +
    algebraicLLStrongEulerField period hPeriod fields

theorem strongDifferentialLLEulerField_pairing
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    inner Real
        (strongDifferentialLLEulerField period hPeriod frame regularity
          fields point)
        (direction point) =
      -inner Real
          (scalarWeightedLLFrameLaplacian period hPeriod frame regularity
            fields point)
          (direction point) +
        2 * fields.llMeasure point *
          inner Real (fields.llField point) (direction point) := by
  change inner Real
      (-scalarWeightedLLFrameLaplacian period hPeriod frame regularity
          fields point +
        (2 * fields.llMeasure point) • fields.llField point)
      (direction point) = _
  simp only [inner_add_left, inner_neg_left,
    real_inner_smul_left]

/-- Pointwise strong residual of the PT-averaged action.  The second raw
residual is pulled back after it is formed, so no false PT-equivariance of the
finite generating frame is assumed. -/
def ptSymmetricStrongDifferentialLLEulerField
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  (1 / 2 : Real) •
    (strongDifferentialLLEulerField period hPeriod frame regularity fields +
      differentialLLFluxDirectionPT period hPeriod
        (strongDifferentialLLEulerField period hPeriod frame regularity
          (llPTPullback period hPeriod fields)))

@[simp]
theorem ptSymmetricStrongDifferentialLLEulerField_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricStrongDifferentialLLEulerField period hPeriod frame regularity
        fields point =
      (1 / 2 : Real) •
        (strongDifferentialLLEulerField period hPeriod frame regularity
            fields point +
          strongDifferentialLLEulerField period hPeriod frame regularity
            (llPTPullback period hPeriod fields)
              (fixedThroatPT period hPeriod point)) := by
  rfl

/-- A finite full-support measure and all smooth test fields detect a smooth
LL residual pointwise.  Thus test separation is analytic infrastructure, not
an additional geometric assumption. -/
theorem smoothLLField_pairing_detects_pointwise_zero
    (residual : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure] :
    (∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
        (∫ point,
          inner Real (residual point) (direction point) ∂mu) = 0) ↔
      ∀ point : EffectiveThroat period hPeriod, residual point = 0 := by
  constructor
  · intro hPairing
    have hSelf := hPairing residual
    have hSquareIntegral :
        (∫ point, ‖residual point‖ ^ 2 ∂mu) = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hSelf
    have hSquareIntegrable :
        Integrable (fun point => ‖residual point‖ ^ 2) mu :=
      (residual.contMDiff_toFun.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hSquareZero :
        (fun point => ‖residual point‖ ^ 2) =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun point => sq_nonneg ‖residual point‖)
        hSquareIntegrable).mp hSquareIntegral
    have hResidualZero :
        residual.toFun =ᵐ[mu]
          (fun _ : EffectiveThroat period hPeriod => (0 : LLFieldFiber)) := by
      filter_upwards [hSquareZero] with point hPoint
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hPoint)
    have hFunctionZero :
        residual.toFun =
          (fun _ : EffectiveThroat period hPeriod => (0 : LLFieldFiber)) :=
      (Continuous.ae_eq_iff_eq mu residual.contMDiff_toFun.continuous
        continuous_const).mp hResidualZero
    exact fun point => congrFun hFunctionZero point
  · intro hPointwise direction
    have hIntegrand :
        (fun point => inner Real (residual point) (direction point)) = 0 := by
      funext point
      rw [hPointwise point]
      simp
    rw [hIntegrand]
    simp

/-- Full-support proposition for the canonical throat measure. -/
def CanonicalThroatVolumeHasFullSupport : Prop :=
  Measure.IsOpenPosMeasure
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem canonicalThroatVolume_hasFullSupport :
    CanonicalThroatVolumeHasFullSupport period hPeriod :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Minimal residual geometric contract: only the global
integration-by-parts formula and its actual boundary flux remain geometric. -/
structure PTSymmetricLLIntegrationByPartsContract
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) where
  boundaryFlux : SmoothThroatField period hPeriod LLFieldFiber → Real
  integrationByParts :
    ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          frame fields direction mu =
        (∫ point,
          inner Real
            (ptSymmetricStrongDifferentialLLEulerField period hPeriod
              frame regularity fields point)
            (direction point) ∂mu) +
          boundaryFlux direction

/-- Boundary flux selected by the integration-by-parts contract. -/
def ptSymmetricLLBoundaryFlux
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    {fields : IndependentFields period hPeriod}
    {mu : Measure (EffectiveThroat period hPeriod)}
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      frame regularity fields mu)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  contract.boundaryFlux direction

/-- The exact global IPP formula, exposing bulk strong residual and boundary
flux in separate terms. -/
theorem globalPTSymmetricDifferentialLLFluxFirstVariation_eq_strong_add_flux
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      frame regularity fields mu)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu =
      (∫ point,
        inner Real
          (ptSymmetricStrongDifferentialLLEulerField period hPeriod
            frame regularity fields point)
          (direction point) ∂mu) +
        ptSymmetricLLBoundaryFlux period hPeriod contract direction :=
  contract.integrationByParts direction

/-- Natural zero-flux condition associated with the constructed strong
operator. -/
def SatisfiesPTSymmetricLLNaturalBoundaryCondition
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    {fields : IndependentFields period hPeriod}
    {mu : Measure (EffectiveThroat period hPeriod)}
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      frame regularity fields mu) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    ptSymmetricLLBoundaryFlux period hPeriod contract direction = 0

/-- Pointwise strong PT-symmetric LL PDE. -/
def SatisfiesPTSymmetricStrongDifferentialLLEquation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ point : EffectiveThroat period hPeriod,
    ptSymmetricStrongDifferentialLLEulerField period hPeriod
      frame regularity fields point = 0

/-- Under the exact zero-flux boundary condition, the existing weak Euler
equation is equivalent to the pointwise strong PDE. -/
theorem satisfiesPTSymmetricWeakDifferentialLLEquation_iff_strong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure]
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      frame regularity fields mu)
    (hBoundary :
      SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod contract) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        frame fields mu ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        frame regularity fields := by
  constructor
  · intro hWeak
    apply (smoothLLField_pairing_detects_pointwise_zero period hPeriod
      (ptSymmetricStrongDifferentialLLEulerField period hPeriod
        frame regularity fields) mu).mp
    intro direction
    have hIPP := contract.integrationByParts direction
    have hFlux : contract.boundaryFlux direction = 0 := hBoundary direction
    rw [hWeak direction, hFlux, add_zero] at hIPP
    exact hIPP.symm
  · intro hStrong direction
    have hFlux : contract.boundaryFlux direction = 0 := hBoundary direction
    rw [contract.integrationByParts, hFlux, add_zero]
    have hPointwise :
        (fun point =>
          inner Real
            (ptSymmetricStrongDifferentialLLEulerField period hPeriod
              frame regularity fields point)
            (direction point)) = 0 := by
      funext point
      rw [hStrong point]
      simp
    rw [hPointwise]
    simp

/-- Actual stationarity of the unchanged PT-symmetric action is equivalent to
the strong PDE under the same geometric and zero-flux contract. -/
theorem ptSymmetricDifferentialLLFluxStationary_iff_strong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure]
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      frame regularity fields mu)
    (hBoundary :
      SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod contract) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod frame fields mu ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        frame regularity fields := by
  rw [ptSymmetricDifferentialLLFluxStationary_iff_weakEquation]
  exact satisfiesPTSymmetricWeakDifferentialLLEquation_iff_strong
    period hPeriod frame regularity fields mu contract hBoundary

/-- Specialization to the actual finite smooth tangent-generating family
already constructed on the compact throat. -/
theorem actualFiniteFrame_ptSymmetricDifferentialLLStationary_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure]
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields mu)
    (hBoundary :
      SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod contract) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields :=
  ptSymmetricDifferentialLLFluxStationary_iff_strong period hPeriod
    (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields mu
    contract hBoundary

/-- Canonical-measure specialization.  Full support is now unconditional;
the explicit remaining geometric input is the zero-flux/Stokes conclusion. -/
theorem canonicalThroat_ptSymmetricDifferentialLLStationary_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (contract : PTSymmetricLLIntegrationByPartsContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (hBoundary :
      SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod contract) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  exact actualFiniteFrame_ptSymmetricDifferentialLLStationary_iff_strong
    period hPeriod fields regularity
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      contract hBoundary

end

end P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
end JanusFormal
