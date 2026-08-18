import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAZeroModeSector4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D

/-!
# Candidate-A five-sector orthogonal product coordinates

This file specializes the generic orthogonal product resolution to the actual
D10-free Candidate-A Hilbert space.  The input is one effective inner-product
preserving coordinate map into five Hilbert factors.  From it we construct the
metric/diffeomorphism, Abelian gauge, primitive SpinC matter, longitudinal/LL
and boundary/finite-BV projectors.

The projectors are then applied to the genuine canonical principal operator
`A_BRST-SpinC-LL`.  Its 25 blocks, five diagonal blocks and ten symmetric cross
blocks are definitions, and their exact sum is the original operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 2000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace
  commonHilbertNormedAddCommGroup
  commonHilbertInnerProductSpace
  commonHilbertNormedSpace
  commonHilbertModule
  commonHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private def CandidateAFiveSectorHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateAFiveSectorNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAFiveSectorHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAFiveSectorInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAFiveSectorHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAFiveSectorNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAFiveSectorHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAFiveSectorModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAFiveSectorHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAFiveSectorCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateAFiveSectorHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Canonical identification of the public Candidate-A sector names with the
generic five product coordinates. -/
def candidateAZeroModeSectorToFiveSectorSlot :
    CandidateAZeroModeSector → FiveSectorSlot
  | .metricDiffeomorphism => .metricDiffeomorphism
  | .abelianGauge => .abelianGauge
  | .primitiveSpinCMatter => .primitiveSpinCMatter
  | .longitudinalLL => .longitudinalLL
  | .boundaryFiniteBV => .boundaryFiniteBV

/-- One effective five-factor orthogonal coordinate system on the actual
Candidate-A Hilbert space. -/
structure GlobalCandidateAFiveSectorOrthogonalProductData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*)
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV] where
  decomposition :
    GlobalCandidateAFiveSectorCompletionHilbert4D period hPeriod configuration data analysis ≃L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV
  inner_map : ∀ first second,
    fiveSectorProductInner (decomposition first) (decomposition second) =
      inner Real first second

/-- Forget the Candidate-A names and obtain the generic orthogonal resolution. -/
def GlobalCandidateAFiveSectorOrthogonalProductData4D.toGeneric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    FiveSectorOrthogonalProductDecomposition
      (E := GlobalCandidateAFiveSectorCompletionHilbert4D period hPeriod configuration data analysis)
      (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV) where
  decomposition := resolution.decomposition
  inner_map := resolution.inner_map

/-- Actual Candidate-A sector projector generated by the one product
coordinate system. -/
def globalCandidateAFiveSectorOrthogonalProjection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)
    (sector : CandidateAZeroModeSector) :=
  resolution.toGeneric.projection
    (candidateAZeroModeSectorToFiveSectorSlot sector)

/-- Exact principal block `P_s A P_t` of the real BRST--SpinC--LL operator. -/
def globalCandidateAFiveSectorPrincipalBlock
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)
    (row column : CandidateAZeroModeSector) :=
  fiveSectorProjectedOperatorBlock resolution.toGeneric
    (globalCandidateACanonicalStableReferenceOperator period hPeriod
      configuration data analysis)
    (candidateAZeroModeSectorToFiveSectorSlot row)
    (candidateAZeroModeSectorToFiveSectorSlot column)

/-- Five diagonal blocks of the genuine principal operator. -/
def globalCandidateAFiveSectorPrincipalDiagonalBlock
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)
    (sector : CandidateAZeroModeSector) :=
  globalCandidateAFiveSectorPrincipalBlock period hPeriod resolution sector sector

/-- Symmetric cross block of the genuine principal operator. -/
def globalCandidateAFiveSectorPrincipalCrossBlock
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)
    (first second : CandidateAZeroModeSector) :=
  globalCandidateAFiveSectorPrincipalBlock period hPeriod resolution first second +
    globalCandidateAFiveSectorPrincipalBlock period hPeriod resolution second first

/-- Public Candidate-A orthogonal coordinate checkpoint. -/
theorem global_candidateA_five_sector_orthogonal_product_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    (∀ sector state,
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          sector
          (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
            resolution sector state) =
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          sector state) ∧
      (∀ sector first second,
        inner Real
            (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
              resolution sector first) second =
          inner Real first
            (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
              resolution sector second)) ∧
      (∀ state,
        ∑ sector : CandidateAZeroModeSector,
          globalCandidateAFiveSectorOrthogonalProjection period hPeriod
            resolution sector state = state) := by
  constructor
  · intro sector state
    exact resolution.toGeneric.projection_idempotent
      (candidateAZeroModeSectorToFiveSectorSlot sector) state
  constructor
  · intro sector first second
    exact resolution.toGeneric.projection_selfAdjoint
      (candidateAZeroModeSectorToFiveSectorSlot sector) first second
  · intro state
    have hUniv : (Finset.univ : Finset CandidateAZeroModeSector) =
        {.metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
          .longitudinalLL, .boundaryFiniteBV} := by
      ext sector
      cases sector <;> simp
    have hSlot : (Finset.univ : Finset FiveSectorSlot) =
        {.metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
          .longitudinalLL, .boundaryFiniteBV} := by
      ext sector
      cases sector <;> simp
    have hSum := resolution.toGeneric.sum_projection_apply state
    rw [hSlot] at hSum
    rw [hUniv]
    simpa [globalCandidateAFiveSectorOrthogonalProjection,
      candidateAZeroModeSectorToFiveSectorSlot, add_assoc] using
      hSum

/-- The actual principal operator is exactly the sum of its 25 sector blocks. -/
theorem globalCandidateACanonicalStableReferenceOperator_eq_fiveSectorBlocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*}
    [NormedAddCommGroup MetricDiffeomorphism]
    [InnerProductSpace Real MetricDiffeomorphism]
    [NormedAddCommGroup AbelianGauge]
    [InnerProductSpace Real AbelianGauge]
    [NormedAddCommGroup PrimitiveSpinCMatter]
    [InnerProductSpace Real PrimitiveSpinCMatter]
    [NormedAddCommGroup LongitudinalLL]
    [InnerProductSpace Real LongitudinalLL]
    [NormedAddCommGroup BoundaryFiniteBV]
    [InnerProductSpace Real BoundaryFiniteBV]
    (resolution : GlobalCandidateAFiveSectorOrthogonalProductData4D period
      hPeriod configuration data analysis MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    globalCandidateACanonicalStableReferenceOperator period hPeriod configuration
        data analysis =
      ∑ row : CandidateAZeroModeSector,
        ∑ column : CandidateAZeroModeSector,
          globalCandidateAFiveSectorPrincipalBlock period hPeriod resolution row
            column := by
  apply ContinuousLinearMap.ext
  intro state
  change
    globalCandidateACanonicalStableReferenceOperator period hPeriod
        configuration data analysis state =
      ∑ row : CandidateAZeroModeSector,
        ∑ column : CandidateAZeroModeSector,
          fiveSectorProjectedOperatorBlock resolution.toGeneric
            (globalCandidateACanonicalStableReferenceOperator period hPeriod
              configuration data analysis)
            (candidateAZeroModeSectorToFiveSectorSlot row)
            (candidateAZeroModeSectorToFiveSectorSlot column) state
  have hGeneric := fiveSectorProjectedOperatorBlock_sum resolution.toGeneric
    (globalCandidateACanonicalStableReferenceOperator period hPeriod
      configuration data analysis) state
  have hUniv : (Finset.univ : Finset CandidateAZeroModeSector) =
      {.metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV} := by
    ext sector
    cases sector <;> simp
  have hSlot : (Finset.univ : Finset FiveSectorSlot) =
      {.metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV} := by
    ext sector
    cases sector <;> simp
  rw [hSlot] at hGeneric
  rw [hUniv]
  exact hGeneric.symm

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
end JanusFormal
