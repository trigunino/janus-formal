import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusCommonMatterActionVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The eight scalar coordinates of a genuine pair of matter variations. -/
def matterVariationComponentFamily
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    MatterComponentFamily period hPeriod :=
  fun component =>
    { toFun := fun point => EuclideanSpace.proj component.2
        (if component.1 = 0 then direction.1 point else direction.2 point)
      contMDiff_toFun := by
        by_cases hSector : component.1 = 0
        · simp only [hSector, if_true]
          exact (EuclideanSpace.proj component.2).contDiff.contMDiff.comp
            direction.1.contMDiff_toFun
        · simp only [hSector, if_false]
          exact (EuclideanSpace.proj component.2).contDiff.contMDiff.comp
            direction.2.contMDiff_toFun }

/-- Faithful matter-only direction in the common Program-P variation space. -/
def matterOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    IndependentFieldVariation period hPeriod where
  metrics := zeroSmoothDiagonalMetricVariation period hPeriod
  matter := direction
  gauge := 0
  ghosts := 0
  auxiliaries := 0
  llAuxMetric := 0
  llMeasure := 0
  llField := 0

theorem matterOnlyIndependentVariation_injective :
    Function.Injective (matterOnlyIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.matter hEqual

/-- Extracting the eight matter scalars from the simultaneous common-field
curve gives exactly their componentwise affine curve. -/
theorem independentMatterComponentFamily_independentFieldCurve_matterOnly
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (epsilon : Real) :
    independentMatterComponentFamily period hPeriod
        (independentFieldCurve period hPeriod fields
          (matterOnlyIndependentVariation period hPeriod direction) epsilon) =
      matterMultipletAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction) epsilon := by
  funext component
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases component with ⟨sector, component⟩
  fin_cases sector <;>
    simp [independentMatterComponentFamily, independentMatterScalar,
      selectMatterField, independentFieldCurve, matterOnlyIndependentVariation,
      matterMultipletAffineCurve, matterVariationComponentFamily,
      scalarAffineCurve] <;> rfl

/-- The actual eight-component action derivative transports to the genuine
common `IndependentFieldVariation` curve. -/
theorem globalIndependentMatterAction_matterOnlyCurve_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    HasDerivAt
      (fun epsilon : Real => globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (matterOnlyIndependentVariation period hPeriod direction) epsilon))
      (globalMatterMultipletEuler period hPeriod data
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction)) 0 := by
  rw [show (fun epsilon : Real => globalIndependentMatterAction period hPeriod
      data (independentFieldCurve period hPeriod fields
        (matterOnlyIndependentVariation period hPeriod direction) epsilon)) =
      (fun epsilon : Real => globalMatterMultipletAction period hPeriod data
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod direction) epsilon)) from by
    funext epsilon
    unfold globalIndependentMatterAction
    rw [independentMatterComponentFamily_independentFieldCurve_matterOnly
      period hPeriod fields direction epsilon]]
  exact globalMatterMultipletAction_hasDerivAt period hPeriod data
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod direction)

/-- D9's matter slot is exactly the throat trace of the selected matter-only
direction. -/
theorem d9MatterCoefficient_matterOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (matterOnlyIndependentVariation period hPeriod direction) sector point =
      throatTrace period hPeriod MatterFiber
        (match sector with | .plus => direction.1 | .minus => direction.2) point := by
  cases sector <;> rfl

theorem d9GaugeOneForm_matterOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (matterOnlyIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  cases sector <;> ext <;> rfl

theorem d9U1Ghost_matterOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (matterOnlyIndependentVariation period hPeriod direction)
        sector column point = 0 := by
  cases sector <;> rfl

theorem d9MetricPerturbation_matterOnlyIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (matterOnlyIndependentVariation period hPeriod direction)
        sector point = zeroSymmetric := by
  have hZero : ∀ index : Fin 4,
      (0 : SmoothQuotientField period hPeriod (Fin 4 → Real))
          (fixedThroatQuotientInclusion period hPeriod point) index = 0 :=
    fun _ => rfl
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity,
      metricMagnitudeVelocityAt, matterOnlyIndependentVariation,
      zeroSmoothDiagonalMetricVariation, lorentzMetric, zeroSymmetric,
      selectSector, hZero]

end

end P0EFTJanusCommonMatterActionVariation4D
end JanusFormal
