import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

/-!
# Simultaneous PT action on independent fields and smooth boundary data

This gate extends the existing PT/exchange involution to the smooth throat
boundary values of every sector in the current independent-field package.
It proves exact trace equivariance and preservation of the full componentwise
Dirichlet condition. General tensor metrics and BV antifields remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentPTBoundaryAction4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

variable (period : Real) (hPeriod : period ≠ 0)

universe u

/-- PT pullback followed by exchange on a pair of smooth throat fields. -/
def throatSectorExchange
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (fields : SmoothThroatField period hPeriod Fiber ×
      SmoothThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber ×
      SmoothThroatField period hPeriod Fiber :=
  (throatPTPullback period hPeriod Fiber fields.2,
    throatPTPullback period hPeriod Fiber fields.1)

@[simp]
theorem throatSectorExchange_involutive
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (fields : SmoothThroatField period hPeriod Fiber ×
      SmoothThroatField period hPeriod Fiber) :
    throatSectorExchange period hPeriod Fiber
        (throatSectorExchange period hPeriod Fiber fields) = fields := by
  apply Prod.ext
  · exact throatPTPullback_involutive period hPeriod Fiber fields.1
  · exact throatPTPullback_involutive period hPeriod Fiber fields.2

/-- Boundary values for every component of the current independent-field
package. The LL blocks already live on the throat. -/
@[ext]
structure IndependentBoundaryData where
  metrics : SmoothThroatField period hPeriod Coefficients4 ×
    SmoothThroatField period hPeriod Coefficients4
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

/-- Smooth restriction of all spacetime components, together with the three
already-throat-supported LL components. -/
def independentBoundaryTrace
    (fields : IndependentFields period hPeriod) :
    IndependentBoundaryData period hPeriod where
  metrics :=
    (throatTrace period hPeriod Coefficients4 fields.metrics.plusMagnitude,
      throatTrace period hPeriod Coefficients4 fields.metrics.minusMagnitude)
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

/-- PT/exchange on every component of the boundary package. -/
def independentBoundaryExchange
    (boundary : IndependentBoundaryData period hPeriod) :
    IndependentBoundaryData period hPeriod where
  metrics := throatSectorExchange period hPeriod Coefficients4 boundary.metrics
  matter := throatSectorExchange period hPeriod MatterFiber boundary.matter
  gauge := throatSectorExchange period hPeriod GaugeFiber boundary.gauge
  ghosts := throatSectorExchange period hPeriod GhostFiber boundary.ghosts
  auxiliaries :=
    throatSectorExchange period hPeriod AuxiliaryFiber boundary.auxiliaries
  llAuxMetric :=
    throatPTPullback period hPeriod LLMetricFiber boundary.llAuxMetric
  llMeasure := throatPTPullback period hPeriod Real boundary.llMeasure
  llField := throatPTPullback period hPeriod LLFieldFiber boundary.llField

@[simp]
theorem independentBoundaryExchange_involutive
    (boundary : IndependentBoundaryData period hPeriod) :
    independentBoundaryExchange period hPeriod
        (independentBoundaryExchange period hPeriod boundary) = boundary := by
  ext <;> simp [independentBoundaryExchange]

/-- Restriction to the throat intertwines the simultaneous field and boundary
PT actions exactly. -/
theorem independentBoundaryTrace_exchange
    (fields : IndependentFields period hPeriod) :
    independentBoundaryTrace period hPeriod
        (independentExchange period hPeriod fields) =
      independentBoundaryExchange period hPeriod
        (independentBoundaryTrace period hPeriod fields) := by
  ext point <;>
    simp [independentBoundaryTrace, independentBoundaryExchange,
      independentExchange, throatSectorExchange, ptExchange,
      sectorExchange, throatTrace_pt_equivariant]

/-- Componentwise smooth Dirichlet condition for the complete current field
package. -/
def SatisfiesIndependentBoundary
    (boundary : IndependentBoundaryData period hPeriod)
    (fields : IndependentFields period hPeriod) : Prop :=
  independentBoundaryTrace period hPeriod fields = boundary

/-- The full Dirichlet condition is preserved by simultaneous PT/exchange. -/
theorem satisfiesIndependentBoundary_exchange
    {boundary : IndependentBoundaryData period hPeriod}
    {fields : IndependentFields period hPeriod}
    (hBoundary :
      SatisfiesIndependentBoundary period hPeriod boundary fields) :
    SatisfiesIndependentBoundary period hPeriod
      (independentBoundaryExchange period hPeriod boundary)
      (independentExchange period hPeriod fields) := by
  unfold SatisfiesIndependentBoundary at hBoundary ⊢
  rw [independentBoundaryTrace_exchange, hBoundary]

/-- Every current independent-field package supplies an exact, hence nonempty,
compatible smooth Dirichlet datum. -/
def inducedIndependentBoundaryPair
    (fields : IndependentFields period hPeriod) :
    IndependentBoundaryData period hPeriod × IndependentFields period hPeriod :=
  (independentBoundaryTrace period hPeriod fields, fields)

theorem inducedIndependentBoundaryPair_satisfies
    (fields : IndependentFields period hPeriod) :
    SatisfiesIndependentBoundary period hPeriod
      (inducedIndependentBoundaryPair period hPeriod fields).1
      (inducedIndependentBoundaryPair period hPeriod fields).2 :=
  rfl

/-- Exact closure statement for the present diagonal metric, matter, gauge,
ghost, auxiliary and LL/throat sectors. -/
theorem independent_pt_boundary_action4D_closed :
    (∀ boundary : IndependentBoundaryData period hPeriod,
      independentBoundaryExchange period hPeriod
          (independentBoundaryExchange period hPeriod boundary) = boundary) ∧
    (∀ fields : IndependentFields period hPeriod,
      SatisfiesIndependentBoundary period hPeriod
        (independentBoundaryTrace period hPeriod fields) fields) := by
  exact ⟨independentBoundaryExchange_involutive period hPeriod,
    inducedIndependentBoundaryPair_satisfies period hPeriod⟩

end

end P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
end JanusFormal
