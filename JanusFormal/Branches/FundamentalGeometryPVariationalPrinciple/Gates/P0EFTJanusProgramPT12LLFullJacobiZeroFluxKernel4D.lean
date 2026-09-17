import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalL2InfiniteDimensional4D

/-! At a zero-flux background the same-action three-slot Jacobi operator
annihilates every pure auxiliary-metric/measure direction. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
open P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLCanonicalL2InfiniteDimensional4D
open P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

theorem sameActionHessian_pureAuxMeasure_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (test : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLSameActionHessian period hPeriod data
      (pureAuxMeasureTest period hPeriod dAux dMeasure) test = 0 := by
  rw [← globalCandidateAFullLLContinuousHessian_smooth period hPeriod
    data analysis]
  rw [globalCandidateAFullLLContinuousHessian_zeroFlux period hPeriod
    data analysis hZero]
  simp [pureAuxMeasureTest, globalCandidateAFullLLFieldProjection_smooth]

/-- The complete L² Jacobi residual kills the two smooth algebraic slots
at every zero-flux background. -/
theorem llFullJacobiLinearMap_pureAuxMeasure_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    llFullJacobiLinearMap period hPeriod data analysis
      (pureAuxMeasureTest period hPeriod dAux dMeasure) = 0 := by
  let direction : GlobalFullLLSmooth period hPeriod analysis :=
    pureAuxMeasureTest period hPeriod dAux dMeasure
  let residual : FullLLHilbert period hPeriod :=
    fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis direction)
  have hPair (test : GlobalFullLLSmooth period hPeriod analysis) :
      inner Real residual
        (fullLLSmoothToHilbertLinearMap period hPeriod analysis test) = 0 := by
    have h := llFullJacobiLinearMap_pairing_eq_sameActionHessian
      period hPeriod data analysis direction test
    rw [sameActionHessian_pureAuxMeasure_zeroFlux period hPeriod
      data analysis hZero dAux dMeasure test] at h
    change
      (inner Real
          ((llFullJacobiLinearMap period hPeriod data analysis direction).1.1)
          (smoothThroatToL2 period hPeriod LLMetricFiber test.1.1) +
        inner Real
          ((llFullJacobiLinearMap period hPeriod data analysis direction).1.2)
          (smoothThroatToL2 period hPeriod Real test.1.2)) +
        inner Real
          ((llFullJacobiLinearMap period hPeriod data analysis direction).2)
          (llSmoothToL2 period hPeriod test.2.toTest) = 0
    simpa only [show smoothThroatToL2 period hPeriod LLMetricFiber test.1.1 =
        llAuxTestToL2 period hPeriod test.1.1 from rfl,
      show smoothThroatToL2 period hPeriod Real test.1.2 =
        llMeasureTestToL2 period hPeriod test.1.2 from rfl,
      show llSmoothToL2 period hPeriod test.2.toTest =
        llFieldTestToL2 period hPeriod test.2 from rfl,
      add_assoc] using h
  have hDense : Dense
      (fullLLJacobiSmoothDomain period hPeriod analysis :
        Set (FullLLHilbert period hPeriod)) :=
    fullLLJacobiSmoothPMap_denseDomain period hPeriod data analysis
  have hSubset :
      (fullLLJacobiSmoothDomain period hPeriod analysis :
        Set (FullLLHilbert period hPeriod)) ⊆
        {value | inner Real residual value = 0} := by
    rintro value ⟨test, rfl⟩
    exact hPair test
  have hClosed : IsClosed
      {value : FullLLHilbert period hPeriod |
        inner Real residual value = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hAll : (Set.univ : Set (FullLLHilbert period hPeriod)) ⊆
      {value | inner Real residual value = 0} := by
    calc
      Set.univ = closure
          (fullLLJacobiSmoothDomain period hPeriod analysis :
            Set (FullLLHilbert period hPeriod)) := hDense.closure_eq.symm
      _ ⊆ _ := closure_minimal hSubset hClosed
  have hResidual : residual = 0 :=
    inner_self_eq_zero.mp (hAll (Set.mem_univ residual))
  apply (fullLLL2HilbertEquiv period hPeriod).injective
  simpa [residual] using hResidual

/-- LL stationarity supplies the zero-flux hypothesis. -/
theorem llFullJacobiLinearMap_pureAuxMeasure_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    llFullJacobiLinearMap period hPeriod data analysis
      (pureAuxMeasureTest period hPeriod dAux dMeasure) = 0 :=
  llFullJacobiLinearMap_pureAuxMeasure_zeroFlux period hPeriod data analysis
    (llField_eq_zero_of_stationary period hPeriod
      (data.boundary.llFields period hPeriod) hStationary) dAux dMeasure

private theorem fullLLJacobiSmoothPMap_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullLLJacobiSmoothPMap period hPeriod data analysis
        ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
          LinearMap.mem_range_self
            (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩ =
      fullLLL2HilbertEquiv period hPeriod
        (llFullJacobiLinearMap period hPeriod data analysis direction) := by
  let e : GlobalFullLLSmooth period hPeriod analysis ≃ₗ[Real]
      fullLLJacobiSmoothDomain period hPeriod analysis :=
    LinearEquiv.ofInjective
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis)
      ((fullLLL2HilbertEquiv period hPeriod).injective.comp
        (fullLLSmoothToL2LinearMap_injective period hPeriod analysis))
  have hInverse : e.symm
      ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
        LinearMap.mem_range_self
          (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩ =
      direction := by
    change e.symm (e direction) = direction
    exact e.symm_apply_apply direction
  change fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis
        (e.symm
          ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
            LinearMap.mem_range_self
              (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩)) =
    fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis direction)
  rw [hInverse]

/-- Every smooth pure auxiliary-metric/measure vector belongs to the kernel
of the canonical closed three-slot L² realization at zero flux. -/
theorem fullLLJacobiClosedPMap_pureAuxMeasure_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    let direction : GlobalFullLLSmooth period hPeriod analysis :=
      pureAuxMeasureTest period hPeriod dAux dMeasure
    let value := fullLLSmoothToHilbertLinearMap period hPeriod analysis direction
    ∃ hDomain : value ∈
        (fullLLJacobiClosedPMap period hPeriod data analysis).domain,
      fullLLJacobiClosedPMap period hPeriod data analysis
        ⟨value, hDomain⟩ = 0 := by
  dsimp only
  let direction : GlobalFullLLSmooth period hPeriod analysis :=
    pureAuxMeasureTest period hPeriod dAux dMeasure
  let value := fullLLSmoothToHilbertLinearMap period hPeriod analysis direction
  have hSmooth : value ∈
      (fullLLJacobiSmoothPMap period hPeriod data analysis).domain :=
    LinearMap.mem_range_self
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction
  have hLe := fullLLJacobiSmoothPMap_le_closed period hPeriod data analysis
  refine ⟨hLe.1 hSmooth, ?_⟩
  have hSmoothZero : fullLLJacobiSmoothPMap period hPeriod data analysis
      ⟨value, hSmooth⟩ = 0 := by
    rw [fullLLJacobiSmoothPMap_apply period hPeriod data analysis direction,
      llFullJacobiLinearMap_pureAuxMeasure_zeroFlux period hPeriod
        data analysis hZero dAux dMeasure]
    exact map_zero _
  exact (hLe.2 (x := ⟨value, hSmooth⟩)
    (y := ⟨value, hLe.1 hSmooth⟩) rfl).symm.trans hSmoothZero

/-- The zero-flux kernel conclusion applies in particular to every LL
stationary background. -/
theorem fullLLJacobiClosedPMap_pureAuxMeasure_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    let direction : GlobalFullLLSmooth period hPeriod analysis :=
      pureAuxMeasureTest period hPeriod dAux dMeasure
    let value := fullLLSmoothToHilbertLinearMap period hPeriod analysis direction
    ∃ hDomain : value ∈
        (fullLLJacobiClosedPMap period hPeriod data analysis).domain,
      fullLLJacobiClosedPMap period hPeriod data analysis
        ⟨value, hDomain⟩ = 0 :=
  fullLLJacobiClosedPMap_pureAuxMeasure_zeroFlux period hPeriod data analysis
    (llField_eq_zero_of_stationary period hPeriod
      (data.boundary.llFields period hPeriod) hStationary) dAux dMeasure

/-- Pure measure L² vectors inside the three-slot Hilbert product. -/
def pureMeasureHilbert
    (measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    FullLLHilbert period hPeriod :=
  fullLLL2HilbertEquiv period hPeriod
    (((0, measure), 0) : FullLLL2 period hPeriod)

private theorem pureMeasureHilbert_continuous :
    Continuous (fun measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =>
        (pureMeasureHilbert period hPeriod measure,
          (0 : FullLLHilbert period hPeriod))) := by
  change Continuous (fun measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =>
    (WithLp.toLp 2
      (WithLp.toLp 2
        ((0 : Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)), measure),
        (0 : Lp LLFieldFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))),
      (0 : FullLLHilbert period hPeriod)))
  fun_prop

/-- Graph closure contains the entire pure-measure L² subspace at zero flux,
not only its smooth vectors. -/
theorem fullLLJacobiClosedPMap_pureMeasureL2_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    ∃ hDomain : pureMeasureHilbert period hPeriod measure ∈
        (fullLLJacobiClosedPMap period hPeriod data analysis).domain,
      fullLLJacobiClosedPMap period hPeriod data analysis
        ⟨pureMeasureHilbert period hPeriod measure, hDomain⟩ = 0 := by
  let C := fullLLJacobiClosedPMap period hPeriod data analysis
  let S := {measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) |
        (pureMeasureHilbert period hPeriod measure,
          (0 : FullLLHilbert period hPeriod)) ∈ C.graph}
  have hClosed : IsClosed S := by
    exact (fullLLJacobiClosedPMap_isClosed period hPeriod data analysis).preimage
      (pureMeasureHilbert_continuous period hPeriod)
  have hRange : Set.range (smoothThroatToL2 period hPeriod Real) ⊆ S := by
    rintro measure ⟨smooth, rfl⟩
    obtain ⟨hDomain, hImage⟩ :=
      fullLLJacobiClosedPMap_pureAuxMeasure_zeroFlux period hPeriod
        data analysis hZero 0 smooth
    apply C.mem_graph_iff.mpr
    refine ⟨⟨pureMeasureHilbert period hPeriod
      (smoothThroatToL2 period hPeriod Real smooth), hDomain⟩, rfl, ?_⟩
    exact hImage
  have hDense := smoothThroatToL2_denseRange period hPeriod Real
  have hAll : (Set.univ : Set (Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))) ⊆ S := by
    calc
      Set.univ = closure (Set.range (smoothThroatToL2 period hPeriod Real)) :=
        hDense.closure_range.symm
      _ ⊆ S := closure_minimal hRange hClosed
  obtain ⟨value, hValue, hImage⟩ := C.mem_graph_iff.mp
    (hAll (Set.mem_univ measure))
  have hValue' : (value : FullLLHilbert period hPeriod) =
      pureMeasureHilbert period hPeriod measure := by
    simpa only [Prod.fst] using hValue
  have hDomain : pureMeasureHilbert period hPeriod measure ∈ C.domain := by
    rw [← hValue']
    exact value.property
  refine ⟨hDomain, ?_⟩
  have hSubtype : value = ⟨pureMeasureHilbert period hPeriod measure,
      hDomain⟩ := Subtype.ext hValue'
  rw [← hSubtype]
  exact hImage

/-- The pure-measure L² insertion is linear. -/
def pureMeasureHilbertLinearMap :
    Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →ₗ[Real]
      FullLLHilbert period hPeriod where
  toFun := pureMeasureHilbert period hPeriod
  map_add' first second := by
    change fullLLL2HilbertEquiv period hPeriod
        (((0, first + second), 0) : FullLLL2 period hPeriod) =
      fullLLL2HilbertEquiv period hPeriod
          (((0, first), 0) : FullLLL2 period hPeriod) +
        fullLLL2HilbertEquiv period hPeriod
          (((0, second), 0) : FullLLL2 period hPeriod)
    rw [← (fullLLL2HilbertEquiv period hPeriod).map_add]
    congr 1
    simp
  map_smul' scalar measure := by
    change fullLLL2HilbertEquiv period hPeriod
        (((0, scalar • measure), 0) : FullLLL2 period hPeriod) =
      scalar • fullLLL2HilbertEquiv period hPeriod
          (((0, measure), 0) : FullLLL2 period hPeriod)
    rw [← (fullLLL2HilbertEquiv period hPeriod).map_smul]
    congr 1
    simp

/-- A copy of the complete scalar L² sits in the closed Jacobi kernel at
zero flux. -/
def pureMeasureKernelLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →ₗ[Real]
      LinearMap.ker (fullLLJacobiClosedPMap period hPeriod data analysis).toFun where
  toFun measure :=
    ⟨⟨pureMeasureHilbert period hPeriod measure,
        (fullLLJacobiClosedPMap_pureMeasureL2_zeroFlux period hPeriod
          data analysis hZero measure).choose⟩,
      (fullLLJacobiClosedPMap_pureMeasureL2_zeroFlux period hPeriod
        data analysis hZero measure).choose_spec⟩
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    exact (pureMeasureHilbertLinearMap period hPeriod).map_add first second
  map_smul' scalar measure := by
    apply Subtype.ext
    apply Subtype.ext
    exact (pureMeasureHilbertLinearMap period hPeriod).map_smul scalar measure

theorem pureMeasureKernelLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    Function.Injective
      (pureMeasureKernelLinearMap period hPeriod data analysis hZero) := by
  intro first second hEqual
  have hHilbert : pureMeasureHilbert period hPeriod first =
      pureMeasureHilbert period hPeriod second :=
    congrArg (fun value :
      LinearMap.ker (fullLLJacobiClosedPMap period hPeriod data analysis).toFun =>
        ((value : (fullLLJacobiClosedPMap period hPeriod data analysis).domain) :
          FullLLHilbert period hPeriod)) hEqual
  have hRaw : (((0, first), 0) : FullLLL2 period hPeriod) =
      (((0, second), 0) : FullLLL2 period hPeriod) :=
    (fullLLL2HilbertEquiv period hPeriod).injective
      (by simpa only [pureMeasureHilbert] using hHilbert)
  exact congrArg (fun value : FullLLL2 period hPeriod => value.1.2) hRaw

/-- The full closed L² Jacobi operator has an infinite-dimensional kernel
at every zero-flux background. -/
theorem fullLLJacobiClosedPMap_kernel_not_finiteDimensional_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    ¬ FiniteDimensional Real
      (LinearMap.ker (fullLLJacobiClosedPMap period hPeriod
        data analysis).toFun) := by
  intro hFinite
  letI : FiniteDimensional Real
      (LinearMap.ker (fullLLJacobiClosedPMap period hPeriod
        data analysis).toFun) := hFinite
  have hMeasureFinite : FiniteDimensional Real
      (Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :=
    FiniteDimensional.of_injective
      (pureMeasureKernelLinearMap period hPeriod data analysis hZero)
      (pureMeasureKernelLinearMap_injective period hPeriod data analysis hZero)
  exact canonicalThroatL2_not_finiteDimensional period hPeriod hMeasureFinite

/-- In particular, the faithful three-slot closed L² Jacobi operator cannot
have a finite-dimensional kernel at an LL stationary background. -/
theorem fullLLJacobiClosedPMap_kernel_not_finiteDimensional_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :
    ¬ FiniteDimensional Real
      (LinearMap.ker (fullLLJacobiClosedPMap period hPeriod
        data analysis).toFun) :=
  fullLLJacobiClosedPMap_kernel_not_finiteDimensional_zeroFlux
    period hPeriod data analysis
      (llField_eq_zero_of_stationary period hPeriod
        (data.boundary.llFields period hPeriod) hStationary)

end
end P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
end JanusFormal
