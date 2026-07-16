import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothThroatTrace4D

/-!
# Global smooth field configuration on the effective D8 quotient

This gate packages independent diagonal metrics, two matter multiplets,
gauge-coordinate fields, ghosts, auxiliaries and throat/LL coefficient data on
the actual smooth quotient. Induced metric/root/trace fields are computed from
the independent data and are unique by construction. The fields live in
explicit trivial coefficient bundles; BRST, tensorial gauge covariance and LL
PDEs remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

abbrev MatterFiber := EuclideanSpace Real (Fin 4)
abbrev GaugeFiber := EuclideanSpace Real (Fin 4 × Fin 2)
abbrev GhostFiber := EuclideanSpace Real (Fin 2)
abbrev AuxiliaryFiber := EuclideanSpace Real (Fin 2)
abbrev LLMetricFiber := EuclideanSpace Real (Fin 3 × Fin 3)
abbrev LLFieldFiber := EuclideanSpace Real (Fin 4)

universe u

/-- Constant smooth spacetime coefficient field. -/
def constantSmoothField
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (value : Fiber) : SmoothQuotientField period hPeriod Fiber where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

/-- Constant smooth throat coefficient field. -/
def constantSmoothThroatField
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (value : Fiber) : SmoothThroatField period hPeriod Fiber where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

private def unitCoefficients : Coefficients4 := fun _ => 1

/-- Nonempty PT-fixed positive diagonal metric domain. -/
def flatPositiveMetricPair :
    SmoothPositiveDiagonalMetricPair period hPeriod where
  plusMagnitude := constantSmoothField period hPeriod Coefficients4 unitCoefficients
  minusMagnitude := constantSmoothField period hPeriod Coefficients4 unitCoefficients
  plus_pos := by intro point index; simp [constantSmoothField, unitCoefficients]
  minus_pos := by intro point index; simp [constantSmoothField, unitCoefficients]

theorem flatPositiveMetricPair_pt_fixed :
    ptExchange period hPeriod (flatPositiveMetricPair period hPeriod) =
      flatPositiveMetricPair period hPeriod := by
  apply SmoothPositiveDiagonalMetricPair.ext
  · apply SmoothQuotientField.ext period hPeriod Coefficients4
    intro point
    rfl
  · apply SmoothQuotientField.ext period hPeriod Coefficients4
    intro point
    rfl

/-- All independent smooth coefficient fields used by the current global
configuration frontier. -/
@[ext]
structure IndependentFields where
  metrics : SmoothPositiveDiagonalMetricPair period hPeriod
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

/-- Exact PT matching imposed only on independent variables. -/
def PTMatchedIndependent (fields : IndependentFields period hPeriod) : Prop :=
  ptExchange period hPeriod fields.metrics = fields.metrics ∧
  PTMatched period hPeriod MatterFiber fields.matter ∧
  PTMatched period hPeriod GaugeFiber fields.gauge ∧
  PTMatched period hPeriod GhostFiber fields.ghosts ∧
  PTMatched period hPeriod AuxiliaryFiber fields.auxiliaries ∧
  throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric = fields.llAuxMetric ∧
  throatPTPullback period hPeriod Real fields.llMeasure = fields.llMeasure ∧
  throatPTPullback period hPeriod LLFieldFiber fields.llField = fields.llField

/-- PT/exchange acting simultaneously on every independent field currently
present in the global configuration package. -/
def independentExchange
    (fields : IndependentFields period hPeriod) :
    IndependentFields period hPeriod where
  metrics := ptExchange period hPeriod fields.metrics
  matter := sectorExchange period hPeriod MatterFiber fields.matter
  gauge := sectorExchange period hPeriod GaugeFiber fields.gauge
  ghosts := sectorExchange period hPeriod GhostFiber fields.ghosts
  auxiliaries := sectorExchange period hPeriod AuxiliaryFiber fields.auxiliaries
  llAuxMetric := throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric
  llMeasure := throatPTPullback period hPeriod Real fields.llMeasure
  llField := throatPTPullback period hPeriod LLFieldFiber fields.llField

@[simp]
theorem independentExchange_involutive
    (fields : IndependentFields period hPeriod) :
    independentExchange period hPeriod
        (independentExchange period hPeriod fields) = fields := by
  ext <;> simp [independentExchange, ptExchange_involutive,
    sectorExchange_involutive, throatPTPullback_involutive]

/-- The whole independent field package with its exact PT involution. -/
def independentExchangeEquiv :
    IndependentFields period hPeriod ≃ IndependentFields period hPeriod where
  toFun := independentExchange period hPeriod
  invFun := independentExchange period hPeriod
  left_inv := independentExchange_involutive period hPeriod
  right_inv := independentExchange_involutive period hPeriod

/-- Componentwise PT matching is exactly the fixed-point locus of the
simultaneous exchange on the independent field package. -/
theorem ptMatchedIndependent_iff_fixed_exchange
    (fields : IndependentFields period hPeriod) :
    PTMatchedIndependent period hPeriod fields ↔
      independentExchange period hPeriod fields = fields := by
  constructor
  · rintro ⟨hMetrics, hMatter, hGauge, hGhosts, hAuxiliaries,
      hLLAuxMetric, hLLMeasure, hLLField⟩
    apply IndependentFields.ext
    · exact hMetrics
    · exact (ptMatched_iff_fixed_exchange period hPeriod MatterFiber _).1 hMatter
    · exact (ptMatched_iff_fixed_exchange period hPeriod GaugeFiber _).1 hGauge
    · exact (ptMatched_iff_fixed_exchange period hPeriod GhostFiber _).1 hGhosts
    · exact (ptMatched_iff_fixed_exchange period hPeriod AuxiliaryFiber _).1
        hAuxiliaries
    · exact hLLAuxMetric
    · exact hLLMeasure
    · exact hLLField
  · intro hFixed
    have hMetrics := congrArg IndependentFields.metrics hFixed
    have hMatter := congrArg IndependentFields.matter hFixed
    have hGauge := congrArg IndependentFields.gauge hFixed
    have hGhosts := congrArg IndependentFields.ghosts hFixed
    have hAuxiliaries := congrArg IndependentFields.auxiliaries hFixed
    have hLLAuxMetric := congrArg IndependentFields.llAuxMetric hFixed
    have hLLMeasure := congrArg IndependentFields.llMeasure hFixed
    have hLLField := congrArg IndependentFields.llField hFixed
    exact ⟨hMetrics,
      (ptMatched_iff_fixed_exchange period hPeriod MatterFiber _).2 hMatter,
      (ptMatched_iff_fixed_exchange period hPeriod GaugeFiber _).2 hGauge,
      (ptMatched_iff_fixed_exchange period hPeriod GhostFiber _).2 hGhosts,
      (ptMatched_iff_fixed_exchange period hPeriod AuxiliaryFiber _).2 hAuxiliaries,
      hLLAuxMetric, hLLMeasure, hLLField⟩

/-- Metrics, principal root and throat matter traces induced from the
independent fields; none is varied as an extra independent variable. -/
structure InducedFields where
  plusMetric : SmoothQuotientField period hPeriod Matrix4
  minusMetric : SmoothQuotientField period hPeriod Matrix4
  principalRoot : SmoothQuotientField period hPeriod Matrix4
  plusMatterTrace : SmoothThroatField period hPeriod MatterFiber
  minusMatterTrace : SmoothThroatField period hPeriod MatterFiber

def induce (fields : IndependentFields period hPeriod) :
    InducedFields period hPeriod where
  plusMetric := plusLorentzMetricField period hPeriod fields.metrics
  minusMetric := minusLorentzMetricField period hPeriod fields.metrics
  principalRoot := principalRootField period hPeriod fields.metrics
  plusMatterTrace := throatTrace period hPeriod MatterFiber fields.matter.1
  minusMatterTrace := throatTrace period hPeriod MatterFiber fields.matter.2

/-- The induced package is uniquely fixed by the independent package. -/
theorem existsUnique_induced (fields : IndependentFields period hPeriod) :
    ∃! induced : InducedFields period hPeriod,
      induced = induce period hPeriod fields := by
  exact ⟨induce period hPeriod fields, rfl, fun candidate hCandidate => hCandidate⟩

/-- Exact square equation for the induced principal root, using the same
independent metric pair. -/
theorem induced_root_square
    (fields : IndependentFields period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (induce period hPeriod fields).principalRoot point *
        (induce period hPeriod fields).principalRoot point =
      lorentzMetricInverse (fields.metrics.plusMagnitude point) *
        (induce period hPeriod fields).minusMetric point :=
  principalRootField_square period hPeriod fields.metrics point

/-- A fully populated nonempty smooth configuration, with zero matter/gauge/
ghost/auxiliary/LL coefficients and positive flat diagonal metrics. -/
def zeroMatchedIndependentFields : IndependentFields period hPeriod :=
  let matterZero := constantSmoothField period hPeriod MatterFiber 0
  let gaugeZero := constantSmoothField period hPeriod GaugeFiber 0
  let ghostZero := constantSmoothField period hPeriod GhostFiber 0
  let auxiliaryZero := constantSmoothField period hPeriod AuxiliaryFiber 0
  { metrics := flatPositiveMetricPair period hPeriod
    matter := matchedPair period hPeriod MatterFiber matterZero
    gauge := matchedPair period hPeriod GaugeFiber gaugeZero
    ghosts := matchedPair period hPeriod GhostFiber ghostZero
    auxiliaries := matchedPair period hPeriod AuxiliaryFiber auxiliaryZero
    llAuxMetric := constantSmoothThroatField period hPeriod LLMetricFiber 0
    llMeasure := constantSmoothThroatField period hPeriod Real 0
    llField := constantSmoothThroatField period hPeriod LLFieldFiber 0 }

theorem zeroMatchedIndependentFields_ptMatched :
    PTMatchedIndependent period hPeriod
      (zeroMatchedIndependentFields period hPeriod) := by
  refine ⟨flatPositiveMetricPair_pt_fixed period hPeriod,
    matchedPair_ptMatched period hPeriod MatterFiber _,
    matchedPair_ptMatched period hPeriod GaugeFiber _,
    matchedPair_ptMatched period hPeriod GhostFiber _,
    matchedPair_ptMatched period hPeriod AuxiliaryFiber _, ?_, ?_, ?_⟩
  all_goals
    apply SmoothThroatField.ext period hPeriod _
    intro point
    rfl

end

end P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
end JanusFormal
