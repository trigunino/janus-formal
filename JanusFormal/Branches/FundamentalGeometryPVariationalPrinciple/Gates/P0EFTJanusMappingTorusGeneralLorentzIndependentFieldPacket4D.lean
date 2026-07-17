import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentPTBoundaryAction4D

/-!
# General-Lorentz independent-field packet and PT boundary action

This gate replaces the diagonal metric pair by two arbitrary smooth Lorentz
metrics while retaining every present non-metric independent field.  A fixed
flat diagonal scaffold lets the already proved complete coefficient-field and
boundary PT laws be reused without reintroducing a diagonal metric degree of
freedom.  The boundary packet deliberately contains only non-metric data:
restriction of an arbitrary general Lorentz metric to the throat is not yet
part of the formal API.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Complete present independent-field packet with genuinely general Lorentz
metrics in both sectors. -/
@[ext]
structure GeneralLorentzIndependentFields where
  metrics : SmoothGeneralLorentzMetric period hPeriod ×
    SmoothGeneralLorentzMetric period hPeriod
  matter : SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber
  gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber
  ghosts : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  auxiliaries : SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real
  llField : SmoothThroatField period hPeriod LLFieldFiber

/-- The old diagonal package used only as a proof scaffold for the unchanged
non-metric sectors.  Its metric is the fixed flat PT-invariant pair. -/
def diagonalScaffold
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    IndependentFields period hPeriod where
  metrics := flatPositiveMetricPair period hPeriod
  matter := fields.matter
  gauge := fields.gauge
  ghosts := fields.ghosts
  auxiliaries := fields.auxiliaries
  llAuxMetric := fields.llAuxMetric
  llMeasure := fields.llMeasure
  llField := fields.llField

/-- Simultaneous analytic PT pullback and exchange on the two general metrics
and on every current non-metric independent sector. -/
def generalLorentzIndependentExchange
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    GeneralLorentzIndependentFields period hPeriod where
  metrics := smoothGeneralLorentzMetricPTExchange period hPeriod fields.metrics
  matter := sectorExchange period hPeriod MatterFiber fields.matter
  gauge := sectorExchange period hPeriod GaugeFiber fields.gauge
  ghosts := sectorExchange period hPeriod GhostFiber fields.ghosts
  auxiliaries := sectorExchange period hPeriod AuxiliaryFiber fields.auxiliaries
  llAuxMetric := throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric
  llMeasure := throatPTPullback period hPeriod Real fields.llMeasure
  llField := throatPTPullback period hPeriod LLFieldFiber fields.llField

@[simp] theorem generalLorentzIndependentExchange_metrics
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).metrics =
      smoothGeneralLorentzMetricPTExchange period hPeriod fields.metrics := rfl

@[simp] theorem generalLorentzIndependentExchange_matter
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).matter =
      sectorExchange period hPeriod MatterFiber fields.matter := rfl

@[simp] theorem generalLorentzIndependentExchange_gauge
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).gauge =
      sectorExchange period hPeriod GaugeFiber fields.gauge := rfl

@[simp] theorem generalLorentzIndependentExchange_ghosts
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).ghosts =
      sectorExchange period hPeriod GhostFiber fields.ghosts := rfl

@[simp] theorem generalLorentzIndependentExchange_auxiliaries
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).auxiliaries =
      sectorExchange period hPeriod AuxiliaryFiber fields.auxiliaries := rfl

@[simp] theorem generalLorentzIndependentExchange_llAuxMetric
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).llAuxMetric =
      throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric := rfl

@[simp] theorem generalLorentzIndependentExchange_llMeasure
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).llMeasure =
      throatPTPullback period hPeriod Real fields.llMeasure := rfl

@[simp] theorem generalLorentzIndependentExchange_llField
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentExchange period hPeriod fields).llField =
      throatPTPullback period hPeriod LLFieldFiber fields.llField := rfl

/-- The scaffold exactly intertwines the new action with the old complete
independent-field action. -/
theorem diagonalScaffold_exchange
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    diagonalScaffold period hPeriod
        (generalLorentzIndependentExchange period hPeriod fields) =
      independentExchange period hPeriod
        (diagonalScaffold period hPeriod fields) := by
  apply IndependentFields.ext
  · exact (flatPositiveMetricPair_pt_fixed period hPeriod).symm
  all_goals rfl

/-- Exact involution on the unified general-metric packet.  The metric part
uses the general tensor theorem; all other components are inherited from the
already closed independent-field action. -/
@[simp]
theorem generalLorentzIndependentExchange_involutive
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    generalLorentzIndependentExchange period hPeriod
        (generalLorentzIndependentExchange period hPeriod fields) = fields := by
  have hScaffold := independentExchange_involutive period hPeriod
    (diagonalScaffold period hPeriod fields)
  rw [← diagonalScaffold_exchange] at hScaffold
  apply GeneralLorentzIndependentFields.ext
  · exact smoothGeneralLorentzMetricPTExchange_involutive
      period hPeriod fields.metrics
  · exact congrArg IndependentFields.matter hScaffold
  · exact congrArg IndependentFields.gauge hScaffold
  · exact congrArg IndependentFields.ghosts hScaffold
  · exact congrArg IndependentFields.auxiliaries hScaffold
  · exact congrArg IndependentFields.llAuxMetric hScaffold
  · exact congrArg IndependentFields.llMeasure hScaffold
  · exact congrArg IndependentFields.llField hScaffold

/-- The unified PT/exchange is an exact self-equivalence. -/
def generalLorentzIndependentExchangeEquiv :
    GeneralLorentzIndependentFields period hPeriod ≃
      GeneralLorentzIndependentFields period hPeriod where
  toFun := generalLorentzIndependentExchange period hPeriod
  invFun := generalLorentzIndependentExchange period hPeriod
  left_inv := generalLorentzIndependentExchange_involutive period hPeriod
  right_inv := generalLorentzIndependentExchange_involutive period hPeriod

/-- Boundary values for every retained non-metric sector.  No boundary value
for a general Lorentz metric is asserted here. -/
@[ext]
structure GeneralLorentzIndependentBoundaryData where
  matter : SmoothThroatField period hPeriod MatterFiber ×
    SmoothThroatField period hPeriod MatterFiber
  gauge : SmoothThroatField period hPeriod GaugeFiber ×
    SmoothThroatField period hPeriod GaugeFiber
  ghosts : SmoothThroatField period hPeriod GhostFiber ×
    SmoothThroatField period hPeriod GhostFiber
  auxiliaries : SmoothThroatField period hPeriod AuxiliaryFiber ×
    SmoothThroatField period hPeriod AuxiliaryFiber
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real
  llField : SmoothThroatField period hPeriod LLFieldFiber

/-- Fixed metric boundary component used only to embed the non-metric packet
into the previous boundary theorem. -/
def flatDiagonalMetricBoundary :
    SmoothThroatField period hPeriod Coefficients4 ×
      SmoothThroatField period hPeriod Coefficients4 :=
  (throatTrace period hPeriod Coefficients4
      (flatPositiveMetricPair period hPeriod).plusMagnitude,
    throatTrace period hPeriod Coefficients4
      (flatPositiveMetricPair period hPeriod).minusMagnitude)

theorem flatDiagonalMetricBoundary_exchange :
    throatSectorExchange period hPeriod Coefficients4
        (flatDiagonalMetricBoundary period hPeriod) =
      flatDiagonalMetricBoundary period hPeriod := by
  apply Prod.ext
  · apply SmoothThroatField.ext period hPeriod Coefficients4
    intro point
    rfl
  · apply SmoothThroatField.ext period hPeriod Coefficients4
    intro point
    rfl

/-- Inject the non-metric datum into the previous complete diagonal boundary
package using the fixed, non-dynamical flat metric trace. -/
def boundaryScaffold
    (boundary : GeneralLorentzIndependentBoundaryData period hPeriod) :
    IndependentBoundaryData period hPeriod where
  metrics := flatDiagonalMetricBoundary period hPeriod
  matter := boundary.matter
  gauge := boundary.gauge
  ghosts := boundary.ghosts
  auxiliaries := boundary.auxiliaries
  llAuxMetric := boundary.llAuxMetric
  llMeasure := boundary.llMeasure
  llField := boundary.llField

theorem boundaryScaffold_injective :
    Function.Injective (boundaryScaffold period hPeriod) := by
  intro first second hEqual
  apply GeneralLorentzIndependentBoundaryData.ext
  · exact congrArg IndependentBoundaryData.matter hEqual
  · exact congrArg IndependentBoundaryData.gauge hEqual
  · exact congrArg IndependentBoundaryData.ghosts hEqual
  · exact congrArg IndependentBoundaryData.auxiliaries hEqual
  · exact congrArg IndependentBoundaryData.llAuxMetric hEqual
  · exact congrArg IndependentBoundaryData.llMeasure hEqual
  · exact congrArg IndependentBoundaryData.llField hEqual

/-- Restriction of all spacetime non-metric fields; LL fields are already
supported on the throat. -/
def generalLorentzIndependentBoundaryTrace
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    GeneralLorentzIndependentBoundaryData period hPeriod where
  matter :=
    (throatTrace period hPeriod MatterFiber fields.matter.1,
      throatTrace period hPeriod MatterFiber fields.matter.2)
  gauge :=
    (throatTrace period hPeriod GaugeFiber fields.gauge.1,
      throatTrace period hPeriod GaugeFiber fields.gauge.2)
  ghosts :=
    (throatTrace period hPeriod GhostFiber fields.ghosts.1,
      throatTrace period hPeriod GhostFiber fields.ghosts.2)
  auxiliaries :=
    (throatTrace period hPeriod AuxiliaryFiber fields.auxiliaries.1,
      throatTrace period hPeriod AuxiliaryFiber fields.auxiliaries.2)
  llAuxMetric := fields.llAuxMetric
  llMeasure := fields.llMeasure
  llField := fields.llField

theorem boundaryScaffold_trace
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    boundaryScaffold period hPeriod
        (generalLorentzIndependentBoundaryTrace period hPeriod fields) =
      independentBoundaryTrace period hPeriod
        (diagonalScaffold period hPeriod fields) :=
  rfl

/-- PT/exchange on every available non-metric boundary component. -/
def generalLorentzIndependentBoundaryExchange
    (boundary : GeneralLorentzIndependentBoundaryData period hPeriod) :
    GeneralLorentzIndependentBoundaryData period hPeriod where
  matter := throatSectorExchange period hPeriod MatterFiber boundary.matter
  gauge := throatSectorExchange period hPeriod GaugeFiber boundary.gauge
  ghosts := throatSectorExchange period hPeriod GhostFiber boundary.ghosts
  auxiliaries :=
    throatSectorExchange period hPeriod AuxiliaryFiber boundary.auxiliaries
  llAuxMetric :=
    throatPTPullback period hPeriod LLMetricFiber boundary.llAuxMetric
  llMeasure := throatPTPullback period hPeriod Real boundary.llMeasure
  llField := throatPTPullback period hPeriod LLFieldFiber boundary.llField

theorem boundaryScaffold_exchange
    (boundary : GeneralLorentzIndependentBoundaryData period hPeriod) :
    boundaryScaffold period hPeriod
        (generalLorentzIndependentBoundaryExchange period hPeriod boundary) =
      independentBoundaryExchange period hPeriod
        (boundaryScaffold period hPeriod boundary) := by
  apply IndependentBoundaryData.ext
  · exact (flatDiagonalMetricBoundary_exchange period hPeriod).symm
  all_goals rfl

/-- Exact involution on all presently available non-metric boundary data. -/
@[simp]
theorem generalLorentzIndependentBoundaryExchange_involutive
    (boundary : GeneralLorentzIndependentBoundaryData period hPeriod) :
    generalLorentzIndependentBoundaryExchange period hPeriod
        (generalLorentzIndependentBoundaryExchange period hPeriod boundary) =
      boundary := by
  apply boundaryScaffold_injective period hPeriod
  rw [boundaryScaffold_exchange, boundaryScaffold_exchange]
  exact independentBoundaryExchange_involutive period hPeriod
    (boundaryScaffold period hPeriod boundary)

/-- The non-metric boundary trace intertwines the exact PT actions.  This is
the previous complete trace theorem transported through the fixed scaffold. -/
theorem generalLorentzIndependentBoundaryTrace_exchange
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    generalLorentzIndependentBoundaryTrace period hPeriod
        (generalLorentzIndependentExchange period hPeriod fields) =
      generalLorentzIndependentBoundaryExchange period hPeriod
        (generalLorentzIndependentBoundaryTrace period hPeriod fields) := by
  apply boundaryScaffold_injective period hPeriod
  rw [boundaryScaffold_trace, diagonalScaffold_exchange,
    boundaryScaffold_exchange, boundaryScaffold_trace]
  exact independentBoundaryTrace_exchange period hPeriod
    (diagonalScaffold period hPeriod fields)

/-- Componentwise Dirichlet condition on precisely the available non-metric
boundary sectors. -/
def SatisfiesGeneralLorentzIndependentBoundary
    (boundary : GeneralLorentzIndependentBoundaryData period hPeriod)
    (fields : GeneralLorentzIndependentFields period hPeriod) : Prop :=
  generalLorentzIndependentBoundaryTrace period hPeriod fields = boundary

/-- Simultaneous PT/exchange preserves every available non-metric Dirichlet
condition. -/
theorem satisfiesGeneralLorentzIndependentBoundary_exchange
    {boundary : GeneralLorentzIndependentBoundaryData period hPeriod}
    {fields : GeneralLorentzIndependentFields period hPeriod}
    (hBoundary : SatisfiesGeneralLorentzIndependentBoundary
      period hPeriod boundary fields) :
    SatisfiesGeneralLorentzIndependentBoundary period hPeriod
      (generalLorentzIndependentBoundaryExchange period hPeriod boundary)
      (generalLorentzIndependentExchange period hPeriod fields) := by
  have hScaffold : SatisfiesIndependentBoundary period hPeriod
      (boundaryScaffold period hPeriod boundary)
      (diagonalScaffold period hPeriod fields) := by
    unfold SatisfiesIndependentBoundary
    rw [← boundaryScaffold_trace, hBoundary]
  have hExchanged := satisfiesIndependentBoundary_exchange period hPeriod hScaffold
  unfold SatisfiesGeneralLorentzIndependentBoundary
  apply boundaryScaffold_injective period hPeriod
  unfold SatisfiesIndependentBoundary at hExchanged
  rw [boundaryScaffold_trace, diagonalScaffold_exchange,
    boundaryScaffold_exchange]
  exact hExchanged

/-- Closure certificate for the general-metric field packet together with all
currently formalized non-metric boundary data. -/
theorem general_lorentz_independent_field_packet4D_closed :
    (∀ fields : GeneralLorentzIndependentFields period hPeriod,
      generalLorentzIndependentExchange period hPeriod
          (generalLorentzIndependentExchange period hPeriod fields) = fields) ∧
    (∀ fields : GeneralLorentzIndependentFields period hPeriod,
      SatisfiesGeneralLorentzIndependentBoundary period hPeriod
        (generalLorentzIndependentBoundaryTrace period hPeriod fields) fields) := by
  exact ⟨generalLorentzIndependentExchange_involutive period hPeriod,
    fun _ => rfl⟩

end

end P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
end JanusFormal
