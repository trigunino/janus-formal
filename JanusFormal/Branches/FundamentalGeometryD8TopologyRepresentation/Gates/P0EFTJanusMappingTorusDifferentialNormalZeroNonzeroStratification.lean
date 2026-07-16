import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence

/-!
# Intrinsic stratification of the differential normal bundle

The available differential normal data canonically distinguish the zero
section from its nonzero complement.  This gate proves that the zero stratum
is closed, the nonzero stratum is open, and the analytic total comparison
transports both strata exactly.

No Lorentzian quadratic form has been constructed on this normal bundle, so
no null/non-null, causal, or joint stratification is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialNormalZeroNonzeroStratification

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev NormalTotalModel :=
  throatCoverModelWithCorners.prod 𝓘(Real, Real)

/-- Zero stratum in the genuine sign-clutched normal bundle. -/
def fixedThroatNormalZeroStratum :
    Set (Bundle.TotalSpace Real (FixedThroatNormalFiber period hPeriod)) :=
  {normal | normal.2 = 0}

/-- Nonzero stratum in the genuine sign-clutched normal bundle. -/
def fixedThroatNormalNonzeroStratum :
    Set (Bundle.TotalSpace Real (FixedThroatNormalFiber period hPeriod)) :=
  {normal | normal.2 ≠ 0}

/-- Zero stratum in the differential normal bundle. -/
def differentialNormalZeroStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | normal.2 = 0}

/-- Nonzero stratum in the differential normal bundle. -/
def differentialNormalNonzeroStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | normal.2 ≠ 0}

@[simp] theorem differentialNormalNonzeroStratum_eq_compl :
    differentialNormalNonzeroStratum period hPeriod =
      (differentialNormalZeroStratum period hPeriod)ᶜ := by
  ext normal
  simp [differentialNormalZeroStratum,
    differentialNormalNonzeroStratum]

theorem differentialNormalStrata_disjoint :
    Disjoint (differentialNormalZeroStratum period hPeriod)
      (differentialNormalNonzeroStratum period hPeriod) := by
  rw [differentialNormalNonzeroStratum_eq_compl]
  exact disjoint_compl_right

theorem differentialNormalStrata_cover :
    differentialNormalZeroStratum period hPeriod ∪
        differentialNormalNonzeroStratum period hPeriod = univ := by
  rw [differentialNormalNonzeroStratum_eq_compl]
  exact union_compl_self _

/-- The set-theoretic zero stratum is precisely the range of the canonical
zero section of the transported vector bundle. -/
theorem differentialNormalZeroStratum_eq_range_zeroSection :
    differentialNormalZeroStratum period hPeriod =
      Set.range
        (Bundle.zeroSection Real (DifferentialNormalFiber period hPeriod)) := by
  ext normal
  constructor
  · rcases normal with ⟨point, normal⟩
    intro hZero
    change normal = 0 at hZero
    subst normal
    exact ⟨point, rfl⟩
  · rintro ⟨point, rfl⟩
    simp [differentialNormalZeroStratum]

/-- The canonical zero section is analytic for the transported atlas. -/
theorem differentialNormalZeroSection_contMDiff :
    ContMDiff throatCoverModelWithCorners NormalTotalModel ω
      (Bundle.zeroSection Real
        (DifferentialNormalFiber period hPeriod)) :=
  Bundle.contMDiff_zeroSection Real
    (DifferentialNormalFiber period hPeriod)

/-- Projection is a continuous left inverse, hence the zero section is a
topological embedding. -/
theorem differentialNormalZeroSection_isEmbedding :
    IsEmbedding
      (Bundle.zeroSection Real
        (DifferentialNormalFiber period hPeriod)) := by
  have hLeftInverse :
      Function.LeftInverse
        (Bundle.TotalSpace.proj :
          DifferentialNormalTotalSpace period hPeriod →
            ThroatBase period hPeriod)
        (Bundle.zeroSection Real
          (DifferentialNormalFiber period hPeriod)) :=
    fun point => Bundle.zeroSection_proj
      (F := Real) (E := DifferentialNormalFiber period hPeriod) point
  exact hLeftInverse.isEmbedding
    (FiberBundle.continuous_proj Real
      (DifferentialNormalFiber period hPeriod))
    (Bundle.Trivialization.continuous_zeroSection Real)

/-- The nonzero locus is open.  The proof is local in an arbitrary bundle
trivialization and uses only invertibility and linearity of its fiber map. -/
theorem differentialNormalNonzeroStratum_isOpen :
    IsOpen (differentialNormalNonzeroStratum period hPeriod) := by
  rw [isOpen_iff_mem_nhds]
  intro normal hNormal
  let trivialization :=
    trivializationAt Real (DifferentialNormalFiber period hPeriod) normal.1
  let coordinateNonzero : Set (ThroatBase period hPeriod × Real) :=
    univ ×ˢ ({0} : Set Real)ᶜ
  have hSource : normal ∈ trivialization.source :=
    FiberBundle.mem_trivializationAt_proj_source
  have hFiberNonzero : normal.2 ≠ 0 := hNormal
  have hCoordinateNonzero : (trivialization normal).2 ≠ 0 := by
    intro hZero
    apply hFiberNonzero
    apply (trivialization.continuousLinearEquivAt Real normal.1
      (trivialization.mem_source.1 hSource)).injective
    rw [map_zero]
    exact
      (trivialization.continuousLinearEquivAt_apply' normal hSource).trans hZero
  have hOpenCoordinates : IsOpen coordinateNonzero :=
    isOpen_univ.prod isClosed_singleton.isOpen_compl
  have hOpenNeighborhood :
      IsOpen
        (trivialization.source ∩
          trivialization ⁻¹' coordinateNonzero) :=
    trivialization.toOpenPartialHomeomorph.isOpen_inter_preimage
      hOpenCoordinates
  have hMemNeighborhood :
      normal ∈ trivialization.source ∩
        trivialization ⁻¹' coordinateNonzero := by
    exact ⟨hSource, ⟨mem_univ _, by simpa using hCoordinateNonzero⟩⟩
  refine Filter.mem_of_superset
    (hOpenNeighborhood.mem_nhds hMemNeighborhood) ?_
  intro other hOther
  change other.2 ≠ 0
  intro hOtherZero
  have hCoordinateZero : (trivialization other).2 = 0 := by
    rw [← trivialization.continuousLinearEquivAt_apply'
        (R := Real) other hOther.1,
      hOtherZero, map_zero]
  have hOtherCoordinateNonzero : (trivialization other).2 ≠ 0 := by
    simpa [coordinateNonzero] using hOther.2.2
  exact hOtherCoordinateNonzero hCoordinateZero

/-- Consequently, the zero stratum is closed. -/
theorem differentialNormalZeroStratum_isClosed :
    IsClosed (differentialNormalZeroStratum period hPeriod) := by
  rw [← isOpen_compl_iff]
  rw [← differentialNormalNonzeroStratum_eq_compl]
  exact differentialNormalNonzeroStratum_isOpen period hPeriod

/-- The analytic total comparison transports the zero stratum exactly. -/
@[simp] theorem differentialNormalTotalDiffeomorph_mem_zeroStratum_iff
    (normal : Bundle.TotalSpace Real
      (FixedThroatNormalFiber period hPeriod)) :
    differentialNormalTotalDiffeomorph period hPeriod normal ∈
        differentialNormalZeroStratum period hPeriod ↔
      normal ∈ fixedThroatNormalZeroStratum period hPeriod := by
  rcases normal with ⟨point, normal⟩
  change
    differentialNormalFiberEquiv period hPeriod point normal = 0 ↔
      normal = 0
  exact LinearEquiv.map_eq_zero_iff
    (differentialNormalFiberEquiv period hPeriod point)

/-- The analytic total comparison transports the nonzero stratum exactly. -/
@[simp] theorem differentialNormalTotalDiffeomorph_mem_nonzeroStratum_iff
    (normal : Bundle.TotalSpace Real
      (FixedThroatNormalFiber period hPeriod)) :
    differentialNormalTotalDiffeomorph period hPeriod normal ∈
        differentialNormalNonzeroStratum period hPeriod ↔
      normal ∈ fixedThroatNormalNonzeroStratum period hPeriod := by
  rcases normal with ⟨point, normal⟩
  change
    differentialNormalFiberEquiv period hPeriod point normal ≠ 0 ↔
      normal ≠ 0
  exact (LinearEquiv.map_eq_zero_iff
    (differentialNormalFiberEquiv period hPeriod point)).not

/-- Complete intrinsic two-stratum certificate available from the current
normal-bundle data. -/
theorem differentialNormalZeroNonzeroStratification :
    IsClosed (differentialNormalZeroStratum period hPeriod) ∧
      IsOpen (differentialNormalNonzeroStratum period hPeriod) ∧
      Disjoint (differentialNormalZeroStratum period hPeriod)
        (differentialNormalNonzeroStratum period hPeriod) ∧
      differentialNormalZeroStratum period hPeriod ∪
          differentialNormalNonzeroStratum period hPeriod = univ :=
  ⟨differentialNormalZeroStratum_isClosed period hPeriod,
    differentialNormalNonzeroStratum_isOpen period hPeriod,
    differentialNormalStrata_disjoint period hPeriod,
    differentialNormalStrata_cover period hPeriod⟩

end

end P0EFTJanusMappingTorusDifferentialNormalZeroNonzeroStratification
end JanusFormal
