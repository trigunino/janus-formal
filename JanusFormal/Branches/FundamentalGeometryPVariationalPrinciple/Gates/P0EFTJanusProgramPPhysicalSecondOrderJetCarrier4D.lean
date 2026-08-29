import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusActualStructuredJetExtraction

/-!
# Physical second-order jet carriers for Program P

This gate only fixes typed, framed carriers for the current physical field
content.  Bulk and throat jets remain separate because their base manifolds
and model tangent spaces are different.  The bridge to
`ActualJanusLocalJetData` is exact for each outer sector and Abelian column.

No construction from a global field configuration, overlap law, groupoid
action, invariant-theory exhaustion or local-functional classification is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

variable (period : Real) (hPeriod : period ≠ 0)

/-- Four-dimensional physical bulk base. -/
abbrev ProgramPBulkJetBase :=
  MappingTorus (reflectedSphereData period hPeriod)

/-- Three-dimensional physical throat base. -/
abbrev ProgramPThroatJetBase :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- A raw second jet in a fixed local frame.  Symmetry refers only to the two
derivative arguments; tensor-slot symmetries belong to the relevant carrier. -/
structure FramedSecondOrderJet
    (Domain Fiber : Type*)
    [NormedAddCommGroup Domain] [NormedSpace Real Domain]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  value : Fiber
  firstDerivative : Domain →L[Real] Fiber
  secondDerivative : Domain →L[Real] Domain →L[Real] Fiber
  secondDerivative_symmetric :
    ∀ first second,
      secondDerivative first second = secondDerivative second first

/-- Covector model in a selected tangent frame. -/
abbrev FramedCovector
    (Tangent : Type*)
    [NormedAddCommGroup Tangent] [NormedSpace Real Tangent] :=
  Tangent →L[Real] Real

/-- Covariant two-tensor model in a selected tangent frame. -/
abbrev FramedCovariantTwoTensor
    (Tangent : Type*)
    [NormedAddCommGroup Tangent] [NormedSpace Real Tangent] :=
  Tangent →L[Real] Tangent →L[Real] Real

/-- Sector-indexed structured-background jet.  The geometric data are selected
together with one paired physical Abelian connection column in each sector. -/
structure StructuredBackgroundSecondJet
    (Tangent : Type*)
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent] where
  tangentialQuadratic :
    Sector → ContinuousTangentialQuadratic Tangent
  normalQuadratic :
    Sector →
      ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Real)
  gaugeConnection :
    Sector → Fin 2 →
      FramedSecondOrderJet Tangent (FramedCovector Tangent)
  physicalNormal : Sector → Real
  tangentialQuadratic_symmetric :
    ∀ sector first second,
      tangentialQuadratic sector first second =
        tangentialQuadratic sector second first
  normalQuadratic_symmetric :
    ∀ sector first second,
      normalQuadratic sector first second =
        normalQuadratic sector second first

/-- Exact projection of one sector and paired connection column to the already
installed actual local structured-jet interface. -/
def StructuredBackgroundSecondJet.toActualJanusLocalJetData
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    ActualJanusLocalJetData (Tangent := Tangent) (Normal := Real) where
  tangentialQuadratic := jet.tangentialQuadratic sector
  normalQuadratic := jet.normalQuadratic sector
  connectionValue := (jet.gaugeConnection sector column).value
  connectionDerivative :=
    (jet.gaugeConnection sector column).firstDerivative
  physicalNormal := jet.physicalNormal sector
  tangentialQuadratic_symmetric :=
    jet.tangentialQuadratic_symmetric sector
  normalQuadratic_symmetric := jet.normalQuadratic_symmetric sector

@[simp]
theorem StructuredBackgroundSecondJet.toActualJanusLocalJetData_tangentialQuadratic
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toActualJanusLocalJetData sector column).tangentialQuadratic =
      jet.tangentialQuadratic sector :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toActualJanusLocalJetData_normalQuadratic
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toActualJanusLocalJetData sector column).normalQuadratic =
      jet.normalQuadratic sector :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toActualJanusLocalJetData_connectionValue
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toActualJanusLocalJetData sector column).connectionValue =
      (jet.gaugeConnection sector column).value :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toActualJanusLocalJetData_connectionDerivative
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toActualJanusLocalJetData sector column).connectionDerivative =
      (jet.gaugeConnection sector column).firstDerivative :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toActualJanusLocalJetData_physicalNormal
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toActualJanusLocalJetData sector column).physicalNormal =
      jet.physicalNormal sector :=
  rfl

/-- Structured-jet projection for one sector and physical Abelian column. -/
def StructuredBackgroundSecondJet.toStructuredJet
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    SmoothLowOrderStructuredJet Tangent Real :=
  (jet.toActualJanusLocalJetData sector column).toStructuredJet

@[simp]
theorem StructuredBackgroundSecondJet.toStructuredJet_tangentialQuadratic
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toStructuredJet sector column).1.1 =
      jet.tangentialQuadratic sector :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toStructuredJet_normalQuadratic
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toStructuredJet sector column).1.2 =
      jet.normalQuadratic sector :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toStructuredJet_connectionValue
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toStructuredJet sector column).2.1 =
      (jet.gaugeConnection sector column).value :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toStructuredJet_connectionDerivative
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toStructuredJet sector column).2.2 =
      (jet.gaugeConnection sector column).firstDerivative :=
  rfl

/-- Reduced `(II,F)` projection for one sector and physical Abelian column. -/
def StructuredBackgroundSecondJet.toReducedJet
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    SmoothLowOrderReducedJet (Tangent := Tangent) (Normal := Real) :=
  (jet.toActualJanusLocalJetData sector column).toReducedJet

@[simp]
theorem StructuredBackgroundSecondJet.toReducedJet_secondFundamental
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toReducedJet sector column).1 = jet.normalQuadratic sector :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toReducedJet_gaugeCurvature_apply
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2)
    (first second : Tangent) :
    (jet.toReducedJet sector column).2 first second =
      (jet.gaugeConnection sector column).firstDerivative first second -
        (jet.gaugeConnection sector column).firstDerivative second first := by
  exact
    (jet.toActualJanusLocalJetData sector column).toReducedJet_curvature_apply
      first second

theorem StructuredBackgroundSecondJet.toReducedJet_isGeometric
    {Tangent : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (jet.toReducedJet sector column).IsGeometric := by
  simpa [StructuredBackgroundSecondJet.toReducedJet] using
    (jet.toActualJanusLocalJetData sector column).toReducedJet_isGeometric

/-- Bulk framed jets.  The obsolete legacy matter and legacy nonminimal slots
are absent; the typed nonminimal fields are represented explicitly. -/
structure BulkPhysicalSecondOrderJet
    (_configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPBulkJetBase period hPeriod
  background : StructuredBackgroundSecondJet EuclideanR4
  metric :
    Sector → FramedSecondOrderJet CoverCoordinates
      (FramedCovariantTwoTensor CoverCoordinates)
  abelianGhost :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra
  abelianAntighost :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra
  abelianNakanishiLautrup :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra
  diffeomorphismGhost :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates
  diffeomorphismAntighost :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates
  diffeomorphismNakanishiLautrup :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates

/-- Throat framed jets.  Primitive SpinC and LL fields remain on their actual
three-dimensional base. -/
structure ThroatPhysicalSecondOrderJet
    (_configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPThroatJetBase period hPeriod
  background : StructuredBackgroundSecondJet EuclideanR3
  inducedMetric :
    Sector → FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovariantTwoTensor ThroatCoverCoordinates)
  spinCMatter :
    Sector → FramedSecondOrderJet ThroatCoverCoordinates
      D9DoubledMatterFiber
  llAuxMetric :
    FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber
  llMeasure :
    FramedSecondOrderJet ThroatCoverCoordinates Real
  llField :
    FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber

/-- Local physical jets are stratified by the base on which their fields
live.  This is deliberately a sum rather than an artificial mixed-base jet. -/
inductive ProgramPPhysicalSecondOrderJetCarrier
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) where
  | bulk
      (jet : BulkPhysicalSecondOrderJet period hPeriod configuration)
  | throat
      (jet : ThroatPhysicalSecondOrderJet period hPeriod configuration)

end
end P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
end JanusFormal
