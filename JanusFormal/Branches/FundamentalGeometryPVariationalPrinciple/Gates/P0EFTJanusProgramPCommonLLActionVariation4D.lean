import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusProgramPCommonLLActionVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

/-- The genuine zero direction in the nonlinear positive-diagonal metric
chart used by the common Program-P variation type. -/
def zeroSmoothDiagonalMetricVariation :
    SmoothDiagonalMetricVariation period hPeriod where
  plusLogDirection := 0
  minusLogDirection := 0

theorem metricCurve_zeroSmoothDiagonalMetricVariation
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (parameter : Real) :
    metricCurve period hPeriod metrics
        (zeroSmoothDiagonalMetricVariation period hPeriod) parameter = metrics := by
  apply SmoothPositiveDiagonalMetricPair.ext
  · apply SmoothQuotientField.ext period hPeriod _
    intro point
    funext index
    change (Real.sqrt (metrics.plusMagnitude point index) *
      Real.exp (parameter * 0)) ^ 2 = metrics.plusMagnitude point index
    simpa using Real.sq_sqrt (le_of_lt (metrics.plus_pos point index))
  · apply SmoothQuotientField.ext period hPeriod _
    intro point
    funext index
    change (Real.sqrt (metrics.minusMagnitude point index) *
      Real.exp (parameter * 0)) ^ 2 = metrics.minusMagnitude point index
    simpa using Real.sq_sqrt (le_of_lt (metrics.minus_pos point index))

/-- Injection of an LL-field direction into the actual simultaneous
`IndependentFieldVariation` used by the Program-P/D9 bridge. -/
def llFluxIndependentVariation
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    IndependentFieldVariation period hPeriod where
  metrics := zeroSmoothDiagonalMetricVariation period hPeriod
  matter := 0
  gauge := 0
  ghosts := 0
  auxiliaries := 0
  llAuxMetric := 0
  llMeasure := 0
  llField := direction

/-- The embedding of the LL direction into the common variation space loses
no information before applying the D9 projections. -/
theorem llFluxIndependentVariation_injective :
    Function.Injective (llFluxIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.llField hEqual

/-- The LL-only curve used to derive the reduced action Hessian is exactly the
restriction of the full Program-P independent-field curve to the injected
variation. -/
theorem independentFieldCurve_llFluxIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (parameter : Real) :
    independentFieldCurve period hPeriod fields
        (llFluxIndependentVariation period hPeriod direction) parameter =
      differentialLLFluxCurve period hPeriod fields direction parameter := by
  apply IndependentFields.ext
  · exact metricCurve_zeroSmoothDiagonalMetricVariation period hPeriod
      fields.metrics parameter
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · simp [independentFieldCurve, differentialLLFluxCurve,
      llFluxIndependentVariation]
  · rfl

/-- On any common geometric domain, the action/Hessian LL curve therefore
uses the same stored configuration and the same variation type as D9. -/
theorem commonDomain_independentFieldCurve_llFlux
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (parameter : Real) :
    independentFieldCurve period hPeriod domain.configuration
        (llFluxIndependentVariation period hPeriod direction) parameter =
      differentialLLFluxCurve period hPeriod domain.operatorData.fields
        direction parameter := by
  rw [domain.operator_fields_eq period hPeriod]
  exact independentFieldCurve_llFluxIndependentVariation period hPeriod
    domain.configuration direction parameter

/-- The actual first variation of the unchanged PT-averaged LL action can be
read directly on the full Program-P independent-field curve. -/
theorem globalPTSymmetricDifferentialLLAction_independentFieldCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (independentFieldCurve period hPeriod fields
            (llFluxIndependentVariation period hPeriod direction) parameter) mu)
      (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        fields direction mu) 0 := by
  rw [show (fun parameter : Real =>
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (llFluxIndependentVariation period hPeriod direction) parameter) mu) =
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields direction parameter) mu) from by
    funext parameter
    rw [independentFieldCurve_llFluxIndependentVariation period hPeriod]]
  exact globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt period
    hPeriod frame fields direction mu

/-- Its mixed Hessian is likewise the derivative along the same genuine
Program-P variation type. -/
theorem globalPTSymmetricDifferentialLLFirstVariation_independentFieldCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (independentFieldCurve period hPeriod fields
            (llFluxIndependentVariation period hPeriod first) parameter)
          second mu)
      (globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
        first second mu) 0 := by
  rw [show (fun parameter : Real =>
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (llFluxIndependentVariation period hPeriod first) parameter)
        second mu) =
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first parameter)
          second mu) from by
    funext parameter
    rw [independentFieldCurve_llFluxIndependentVariation period hPeriod]]
  exact globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
    period hPeriod frame fields first second mu

/-- Specialization to the stored common-domain configuration: action, Hessian,
and D9 now consume the same base configuration and variation type in the LL
direction. -/
theorem commonDomain_LLAction_independentFieldCurve_hasDerivAt
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    HasDerivAt
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (independentFieldCurve period hPeriod domain.configuration
            (llFluxIndependentVariation period hPeriod direction) parameter)
          domain.operatorData.mu)
      (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        domain.configuration direction domain.operatorData.mu) 0 := by
  letI : IsFiniteMeasure domain.operatorData.mu :=
    domain.operatorData.finiteMeasure
  exact globalPTSymmetricDifferentialLLAction_independentFieldCurve_hasDerivAt
    period hPeriod frame domain.configuration direction domain.operatorData.mu

/-- The present D9 gauge-one-form projection is blind to an LL-only action
direction. -/
theorem d9GaugeOneForm_llFluxIndependentVariation
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (llFluxIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  cases sector <;> ext <;> rfl

/-- Its current U(1)-ghost projection is likewise zero. -/
theorem d9U1Ghost_llFluxIndependentVariation
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (llFluxIndependentVariation period hPeriod direction)
        sector column point = 0 := by
  cases sector <;> rfl

/-- Its current matter projection is also zero. -/
theorem d9MatterCoefficient_llFluxIndependentVariation
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (llFluxIndependentVariation period hPeriod direction)
        sector point = 0 := by
  cases sector <;> rfl

/-- Finally, the diagonal metric projection is zero because the injected LL
direction has exactly zero logarithmic metric velocity. -/
theorem d9MetricPerturbation_llFluxIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (llFluxIndependentVariation period hPeriod direction)
        sector point = zeroSymmetric := by
  have hZero : ∀ index : Fin 4,
      (0 : SmoothQuotientField period hPeriod (Fin 4 → Real))
          (fixedThroatQuotientInclusion period hPeriod point) index = 0 :=
    fun _ => rfl
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity,
      metricMagnitudeVelocityAt, llFluxIndependentVariation,
      zeroSmoothDiagonalMetricVariation, lorentzMetric, zeroSymmetric,
      selectSector, hZero]

/-- All currently supplied D9 slots identify every pair of faithfully
embedded LL directions.  Thus the loss occurs in the D9 projection, not in
the common variation-space embedding. -/
theorem d9ProvidedSlots_identify_llFluxIndependentVariations
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    (∀ (sector : Sector) (column : Fin 2)
        (point : MappingTorus (fixedEquatorData period hPeriod)),
      d9GaugeOneForm period hPeriod
          (llFluxIndependentVariation period hPeriod first)
          sector column point =
        d9GaugeOneForm period hPeriod
          (llFluxIndependentVariation period hPeriod second)
          sector column point) ∧
    (∀ (sector : Sector) (column : Fin 2)
        (point : MappingTorus (fixedEquatorData period hPeriod)),
      d9U1Ghost period hPeriod
          (llFluxIndependentVariation period hPeriod first)
          sector column point =
        d9U1Ghost period hPeriod
          (llFluxIndependentVariation period hPeriod second)
          sector column point) ∧
    (∀ (sector : Sector)
        (point : MappingTorus (fixedEquatorData period hPeriod)),
      d9MatterCoefficient period hPeriod
          (llFluxIndependentVariation period hPeriod first) sector point =
        d9MatterCoefficient period hPeriod
          (llFluxIndependentVariation period hPeriod second) sector point) ∧
    (∀ (sector : Sector)
        (point : MappingTorus (fixedEquatorData period hPeriod)),
      d9MetricPerturbation period hPeriod fields
          (llFluxIndependentVariation period hPeriod first) sector point =
        d9MetricPerturbation period hPeriod fields
          (llFluxIndependentVariation period hPeriod second) sector point) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sector column point
    rw [d9GaugeOneForm_llFluxIndependentVariation,
      d9GaugeOneForm_llFluxIndependentVariation]
  · intro sector column point
    rw [d9U1Ghost_llFluxIndependentVariation,
      d9U1Ghost_llFluxIndependentVariation]
  · intro sector point
    rw [d9MatterCoefficient_llFluxIndependentVariation,
      d9MatterCoefficient_llFluxIndependentVariation]
  · intro sector point
    rw [d9MetricPerturbation_llFluxIndependentVariation,
      d9MetricPerturbation_llFluxIndependentVariation]

end

end P0EFTJanusProgramPCommonLLActionVariation4D
end JanusFormal
