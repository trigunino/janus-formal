import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostCorrectedGlobalKoszul4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Linear full-field extension of the corrected D8 BRST differential

The unconditional corrected differential is extended componentwise to every
linear spacetime coefficient sector currently present in `IndependentFields`:
matter, gauge coordinates, internal gauge ghosts and auxiliaries.  Each square
is proved separately and then on their product.

The independent LL fields live on the throat.  The repository currently has
their discrete PT pullback, but no infinitesimal throat action of the three D8
rotation ghosts.  `LLThroatBRSTCompletion` isolates exactly that missing map;
given it, the LL metric coordinates, measure and LL field also form a
componentwise square-zero complex and combine with the unconditional
spacetime complex.

Positive metrics are deliberately excluded because their domain is nonlinear
and no tensorial ghost Lie derivative has been constructed.  Antifields and a
BV antibracket are not present in the current field package and remain outside
this gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D
open P0EFTJanusMappingTorusD8NonabelianGhostCorrectedGlobalKoszul4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev Scalar := CInfinityScalarField period hPeriod
private abbrev Coefficient := GhostCoefficientExterior
private abbrev Total := ThreeGeneratorExteriorScalarAlgebra period hPeriod

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

/-- The corrected scalar BRST differential applied independently at every
coordinate of a finite or infinite linear multiplet. -/
def componentwiseCorrectedBRST (Index : Type*) :
    (Index → Total period hPeriod) →ₗ[Real]
      (Index → Total period hPeriod) :=
  LinearMap.pi fun index =>
    (unconditionalCorrectedGlobalKoszulDifferential period hPeriod).toLinearMap.comp
      (LinearMap.proj index)

@[simp]
theorem componentwiseCorrectedBRST_apply
    (Index : Type*) (field : Index → Total period hPeriod) (index : Index) :
    componentwiseCorrectedBRST period hPeriod Index field index =
      (unconditionalCorrectedGlobalKoszulDifferential period hPeriod).toLinearMap
        (field index) :=
  rfl

theorem componentwiseCorrectedBRST_square_zero
    (Index : Type*) (field : Index → Total period hPeriod) :
    componentwiseCorrectedBRST period hPeriod Index
        (componentwiseCorrectedBRST period hPeriod Index field) = 0 := by
  funext index
  exact (unconditionalCorrectedGlobalKoszulDifferential period hPeriod).square_zero
    (field index)

abbrev MatterCoordinate := Fin 2 × Fin 4
abbrev GaugeCoordinate := Fin 2 × (Fin 4 × Fin 2)
abbrev GaugeGhostCoordinate := Fin 2 × Fin 2
abbrev AuxiliaryCoordinate := Fin 2 × Fin 2

abbrev MatterBRSTSector :=
  MatterCoordinate → Total period hPeriod

abbrev GaugeCoordinateBRSTSector :=
  GaugeCoordinate → Total period hPeriod

abbrev GaugeGhostBRSTSector :=
  GaugeGhostCoordinate → Total period hPeriod

abbrev AuxiliaryBRSTSector :=
  AuxiliaryCoordinate → Total period hPeriod

/-- All currently available linear spacetime sectors.  The product is nested
to keep the carrier an ordinary real module. -/
abbrev SpacetimeLinearFullFieldBRST :=
  MatterBRSTSector period hPeriod ×
    (GaugeCoordinateBRSTSector period hPeriod ×
      (GaugeGhostBRSTSector period hPeriod ×
        AuxiliaryBRSTSector period hPeriod))

/-- Componentwise corrected BRST map on matter, gauge-coordinate, internal
ghost and auxiliary sectors. -/
def correctedSpacetimeLinearFullFieldBRST :
    SpacetimeLinearFullFieldBRST period hPeriod →ₗ[Real]
      SpacetimeLinearFullFieldBRST period hPeriod :=
  (componentwiseCorrectedBRST period hPeriod MatterCoordinate).prodMap
    ((componentwiseCorrectedBRST period hPeriod GaugeCoordinate).prodMap
      ((componentwiseCorrectedBRST period hPeriod GaugeGhostCoordinate).prodMap
        (componentwiseCorrectedBRST period hPeriod AuxiliaryCoordinate)))

@[simp]
theorem correctedSpacetimeLinearFullFieldBRST_matter
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod fields).1 =
      componentwiseCorrectedBRST period hPeriod MatterCoordinate fields.1 :=
  rfl

@[simp]
theorem correctedSpacetimeLinearFullFieldBRST_gauge
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod fields).2.1 =
      componentwiseCorrectedBRST period hPeriod GaugeCoordinate fields.2.1 :=
  rfl

@[simp]
theorem correctedSpacetimeLinearFullFieldBRST_gaugeGhost
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod fields).2.2.1 =
      componentwiseCorrectedBRST period hPeriod GaugeGhostCoordinate
        fields.2.2.1 :=
  rfl

@[simp]
theorem correctedSpacetimeLinearFullFieldBRST_auxiliary
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod fields).2.2.2 =
      componentwiseCorrectedBRST period hPeriod AuxiliaryCoordinate
        fields.2.2.2 :=
  rfl

theorem correctedSpacetimeLinearFullFieldBRST_square_zero_matter
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod
      (correctedSpacetimeLinearFullFieldBRST period hPeriod fields)).1 = 0 :=
  componentwiseCorrectedBRST_square_zero period hPeriod MatterCoordinate fields.1

theorem correctedSpacetimeLinearFullFieldBRST_square_zero_gauge
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod
      (correctedSpacetimeLinearFullFieldBRST period hPeriod fields)).2.1 = 0 :=
  componentwiseCorrectedBRST_square_zero period hPeriod GaugeCoordinate fields.2.1

theorem correctedSpacetimeLinearFullFieldBRST_square_zero_gaugeGhost
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod
      (correctedSpacetimeLinearFullFieldBRST period hPeriod fields)).2.2.1 = 0 :=
  componentwiseCorrectedBRST_square_zero period hPeriod GaugeGhostCoordinate
    fields.2.2.1

theorem correctedSpacetimeLinearFullFieldBRST_square_zero_auxiliary
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    (correctedSpacetimeLinearFullFieldBRST period hPeriod
      (correctedSpacetimeLinearFullFieldBRST period hPeriod fields)).2.2.2 = 0 :=
  componentwiseCorrectedBRST_square_zero period hPeriod AuxiliaryCoordinate
    fields.2.2.2

theorem correctedSpacetimeLinearFullFieldBRST_square_zero
    (fields : SpacetimeLinearFullFieldBRST period hPeriod) :
    correctedSpacetimeLinearFullFieldBRST period hPeriod
        (correctedSpacetimeLinearFullFieldBRST period hPeriod fields) = 0 := by
  apply Prod.ext
  · exact correctedSpacetimeLinearFullFieldBRST_square_zero_matter
      period hPeriod fields
  · apply Prod.ext
    · exact correctedSpacetimeLinearFullFieldBRST_square_zero_gauge
        period hPeriod fields
    · apply Prod.ext
      · exact correctedSpacetimeLinearFullFieldBRST_square_zero_gaugeGhost
          period hPeriod fields
      · exact correctedSpacetimeLinearFullFieldBRST_square_zero_auxiliary
          period hPeriod fields

/-- A smooth Euclidean multiplet component as a genuine `C∞` scalar. -/
def smoothEuclideanCoordinate
    {Index : Type*} [Fintype Index]
    (field : SmoothQuotientField period hPeriod (EuclideanSpace Real Index))
    (index : Index) : Scalar period hPeriod :=
  analyticScalarToCInfinity period hPeriod
    { toFun := fun point => field point index
      contMDiff_toFun :=
        (EuclideanSpace.proj index).contMDiff.comp field.contMDiff_toFun }

/-- Even embedding of an existing smooth multiplet into its BRST coordinate
family. -/
def evenSmoothEuclideanCoordinates
    {Index : Type*} [Fintype Index]
    (field : SmoothQuotientField period hPeriod (EuclideanSpace Real Index)) :
    Index → Total period hPeriod :=
  fun index => (1 : Coefficient) ⊗ₜ[Real]
    smoothEuclideanCoordinate period hPeriod field index

private def selectSheet {A : Type*} (pair : A × A) (sheet : Fin 2) : A :=
  if sheet = 0 then pair.1 else pair.2

/-- Canonical even embedding of the four linear spacetime sectors of the
current independent-field package. -/
def independentSpacetimeLinearBRSTFields
    (fields : IndependentFields period hPeriod) :
    SpacetimeLinearFullFieldBRST period hPeriod :=
  (fun index => evenSmoothEuclideanCoordinates period hPeriod
      (selectSheet fields.matter index.1) index.2,
    (fun index => evenSmoothEuclideanCoordinates period hPeriod
        (selectSheet fields.gauge index.1) index.2,
      (fun index => evenSmoothEuclideanCoordinates period hPeriod
          (selectSheet fields.ghosts index.1) index.2,
        fun index => evenSmoothEuclideanCoordinates period hPeriod
          (selectSheet fields.auxiliaries index.1) index.2)))

theorem independentSpacetimeLinearBRSTFields_square_zero
    (fields : IndependentFields period hPeriod) :
    correctedSpacetimeLinearFullFieldBRST period hPeriod
        (correctedSpacetimeLinearFullFieldBRST period hPeriod
          (independentSpacetimeLinearBRSTFields period hPeriod fields)) = 0 :=
  correctedSpacetimeLinearFullFieldBRST_square_zero period hPeriod _

/-- The exterior CE ghost sector itself remains square-zero independently of
all matter coordinates. -/
theorem correctedDiffeomorphismGhostCoefficient_square_zero
    (coefficient : Coefficient) :
    (unconditionalCorrectedGlobalKoszulDifferential period hPeriod).toLinearMap
        ((unconditionalCorrectedGlobalKoszulDifferential period hPeriod).toLinearMap
          (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod))) = 0 :=
  (unconditionalCorrectedGlobalKoszulDifferential period hPeriod).square_zero _

/-- Genuine smooth scalar algebra on the fixed throat quotient. -/
abbrev CInfinityThroatScalarField :=
  C^∞⟮throatCoverModelWithCorners,
    EffectiveThroat period hPeriod; Real⟯

/-- Exterior-valued throat scalars used by the LL BRST completion. -/
abbrev LLThroatExteriorScalarAlgebra :=
  GhostCoefficientExterior ⊗[Real]
    CInfinityThroatScalarField period hPeriod

abbrev LLMetricCoordinate := Fin 3 × Fin 3
abbrev LLMeasureCoordinate := Unit
abbrev LLFieldCoordinate := Fin 4

abbrev LLThroatLinearBRST :=
  (LLMetricCoordinate → LLThroatExteriorScalarAlgebra period hPeriod) ×
    ((LLMeasureCoordinate → LLThroatExteriorScalarAlgebra period hPeriod) ×
      (LLFieldCoordinate → LLThroatExteriorScalarAlgebra period hPeriod))

/-- Existing analytic throat scalars canonically enter the smooth algebra. -/
def analyticThroatScalarToCInfinity
    (field : SmoothThroatField period hPeriod Real) :
    CInfinityThroatScalarField period hPeriod :=
  ⟨field.toFun, field.contMDiff_toFun.of_le (by simp)⟩

/-- Smooth coordinate extraction for an existing Euclidean throat field. -/
def smoothThroatEuclideanCoordinate
    {Index : Type*} [Fintype Index]
    (field : SmoothThroatField period hPeriod (EuclideanSpace Real Index))
    (index : Index) : CInfinityThroatScalarField period hPeriod :=
  ⟨fun point => field point index,
    ((EuclideanSpace.proj index).contMDiff.comp field.contMDiff_toFun).of_le
      (by simp)⟩

def evenSmoothThroatEuclideanCoordinates
    {Index : Type*} [Fintype Index]
    (field : SmoothThroatField period hPeriod (EuclideanSpace Real Index)) :
    Index → LLThroatExteriorScalarAlgebra period hPeriod :=
  fun index => (1 : Coefficient) ⊗ₜ[Real]
    smoothThroatEuclideanCoordinate period hPeriod field index

/-- The three independent LL/throat sectors of the current field package,
embedded in even ghost degree. -/
def independentLLThroatLinearBRSTFields
    (fields : IndependentFields period hPeriod) :
    LLThroatLinearBRST period hPeriod :=
  (evenSmoothThroatEuclideanCoordinates period hPeriod fields.llAuxMetric,
    (fun _ => (1 : Coefficient) ⊗ₜ[Real]
        analyticThroatScalarToCInfinity period hPeriod fields.llMeasure,
      evenSmoothThroatEuclideanCoordinates period hPeriod fields.llField))

/-- Exact missing completion for the throat sectors.  A valid completion must
extend the already fixed CE differential on constant scalar coefficients and
be square-zero.  Constructing it requires the absent infinitesimal throat
rotation action; the existing discrete PT pullback alone does not supply it. -/
structure LLThroatBRSTCompletion where
  toLinearMap : LLThroatExteriorScalarAlgebra period hPeriod →ₗ[Real]
    LLThroatExteriorScalarAlgebra period hPeriod
  coefficient_rule : ∀ coefficient : Coefficient,
    toLinearMap
        (coefficient ⊗ₜ[Real]
          (1 : CInfinityThroatScalarField period hPeriod)) =
      (unconditionalClosedThreeGeneratorGhostKoszulData period hPeriod).coefficientDifferential
          coefficient ⊗ₜ[Real]
        (1 : CInfinityThroatScalarField period hPeriod)
  square_zero : ∀ element, toLinearMap (toLinearMap element) = 0

def componentwiseLLThroatBRST
    (completion : LLThroatBRSTCompletion period hPeriod) (Index : Type*) :
    (Index → LLThroatExteriorScalarAlgebra period hPeriod) →ₗ[Real]
      (Index → LLThroatExteriorScalarAlgebra period hPeriod) :=
  LinearMap.pi fun index => completion.toLinearMap.comp (LinearMap.proj index)

theorem componentwiseLLThroatBRST_square_zero
    (completion : LLThroatBRSTCompletion period hPeriod) (Index : Type*)
    (field : Index → LLThroatExteriorScalarAlgebra period hPeriod) :
    componentwiseLLThroatBRST period hPeriod completion Index
        (componentwiseLLThroatBRST period hPeriod completion Index field) = 0 := by
  funext index
  exact completion.square_zero (field index)

def correctedLLThroatLinearBRST
    (completion : LLThroatBRSTCompletion period hPeriod) :
    LLThroatLinearBRST period hPeriod →ₗ[Real]
      LLThroatLinearBRST period hPeriod :=
  (componentwiseLLThroatBRST period hPeriod completion LLMetricCoordinate).prodMap
    ((componentwiseLLThroatBRST period hPeriod completion LLMeasureCoordinate).prodMap
      (componentwiseLLThroatBRST period hPeriod completion LLFieldCoordinate))

theorem correctedLLThroatLinearBRST_square_zero_metric
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : LLThroatLinearBRST period hPeriod) :
    (correctedLLThroatLinearBRST period hPeriod completion
      (correctedLLThroatLinearBRST period hPeriod completion fields)).1 = 0 :=
  componentwiseLLThroatBRST_square_zero period hPeriod completion
    LLMetricCoordinate fields.1

theorem correctedLLThroatLinearBRST_square_zero_measure
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : LLThroatLinearBRST period hPeriod) :
    (correctedLLThroatLinearBRST period hPeriod completion
      (correctedLLThroatLinearBRST period hPeriod completion fields)).2.1 = 0 :=
  componentwiseLLThroatBRST_square_zero period hPeriod completion
    LLMeasureCoordinate fields.2.1

theorem correctedLLThroatLinearBRST_square_zero_field
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : LLThroatLinearBRST period hPeriod) :
    (correctedLLThroatLinearBRST period hPeriod completion
      (correctedLLThroatLinearBRST period hPeriod completion fields)).2.2 = 0 :=
  componentwiseLLThroatBRST_square_zero period hPeriod completion
    LLFieldCoordinate fields.2.2

theorem correctedLLThroatLinearBRST_square_zero
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : LLThroatLinearBRST period hPeriod) :
    correctedLLThroatLinearBRST period hPeriod completion
        (correctedLLThroatLinearBRST period hPeriod completion fields) = 0 := by
  apply Prod.ext
  · exact correctedLLThroatLinearBRST_square_zero_metric
      period hPeriod completion fields
  · apply Prod.ext
    · exact correctedLLThroatLinearBRST_square_zero_measure
        period hPeriod completion fields
    · exact correctedLLThroatLinearBRST_square_zero_field
        period hPeriod completion fields

abbrev LinearFullFieldBRST :=
  SpacetimeLinearFullFieldBRST period hPeriod × LLThroatLinearBRST period hPeriod

/-- The complete linear projection of the current independent package. -/
def independentLinearFullFieldBRSTFields
    (fields : IndependentFields period hPeriod) :
    LinearFullFieldBRST period hPeriod :=
  (independentSpacetimeLinearBRSTFields period hPeriod fields,
    independentLLThroatLinearBRSTFields period hPeriod fields)

/-- Full linear product differential once the precisely isolated throat action
has been supplied. -/
def correctedLinearFullFieldBRST
    (completion : LLThroatBRSTCompletion period hPeriod) :
    LinearFullFieldBRST period hPeriod →ₗ[Real]
      LinearFullFieldBRST period hPeriod :=
  (correctedSpacetimeLinearFullFieldBRST period hPeriod).prodMap
    (correctedLLThroatLinearBRST period hPeriod completion)

theorem correctedLinearFullFieldBRST_square_zero
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : LinearFullFieldBRST period hPeriod) :
    correctedLinearFullFieldBRST period hPeriod completion
        (correctedLinearFullFieldBRST period hPeriod completion fields) = 0 := by
  apply Prod.ext
  · exact correctedSpacetimeLinearFullFieldBRST_square_zero
      period hPeriod fields.1
  · exact correctedLLThroatLinearBRST_square_zero
      period hPeriod completion fields.2

theorem independentLinearFullFieldBRSTFields_square_zero
    (completion : LLThroatBRSTCompletion period hPeriod)
    (fields : IndependentFields period hPeriod) :
    correctedLinearFullFieldBRST period hPeriod completion
        (correctedLinearFullFieldBRST period hPeriod completion
          (independentLinearFullFieldBRSTFields period hPeriod fields)) = 0 :=
  correctedLinearFullFieldBRST_square_zero period hPeriod completion _

/-- Explicit ledger of sectors not claimed by this linear gate. -/
inductive DeferredBRSTSector
  | positiveMetrics
  | throatInfinitesimalRotationAction
  | antifields
  | bvAntibracket
  deriving DecidableEq

end

end P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
end JanusFormal
