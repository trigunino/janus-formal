import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetCarrierTraceProduct

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

universe uField uBulkBase uThroatBase
universe uBulkModel uBulkModelSpace uThroatModel uThroatModelSpace
universe uBulkFiber uThroatFiber uBulkChart uThroatChart
universe uFirstBulkFiber uFirstThroatFiber uSecondBulkFiber uSecondThroatFiber
universe uFirstBulkChart uFirstThroatChart uSecondBulkChart uSecondThroatChart
universe uNewBulkChart uNewThroatChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]

variable {BulkModel : Type uBulkModel} [NormedAddCommGroup BulkModel]
variable [NormedSpace 𝕜 BulkModel]
variable {BulkModelSpace : Type uBulkModelSpace} [TopologicalSpace BulkModelSpace]
variable (IBulk : ModelWithCorners 𝕜 BulkModel BulkModelSpace)
variable {BulkBase : Type uBulkBase} [TopologicalSpace BulkBase]
variable [ChartedSpace BulkModelSpace BulkBase]

variable {ThroatModel : Type uThroatModel} [NormedAddCommGroup ThroatModel]
variable [NormedSpace 𝕜 ThroatModel]
variable {ThroatModelSpace : Type uThroatModelSpace} [TopologicalSpace ThroatModelSpace]
variable (IThroat : ModelWithCorners 𝕜 ThroatModel ThroatModelSpace)
variable {ThroatBase : Type uThroatBase} [TopologicalSpace ThroatBase]
variable [ChartedSpace ThroatModelSpace ThroatBase]

variable {BulkFiber : Type uBulkFiber}
variable {ThroatFiber : Type uThroatFiber}
variable [NormedAddCommGroup BulkFiber] [NormedSpace 𝕜 BulkFiber]
variable [NormedAddCommGroup ThroatFiber] [NormedSpace 𝕜 ThroatFiber]
variable {BulkChart : Type uBulkChart}
variable {ThroatChart : Type uThroatChart}

/-- A bulk-to-throat carrier trace records both preferred-coordinate and local
extractor laws.  The local overlap identity is derived below rather than stored
as an independent premise. -/
structure SmoothCoreCarrierTrace
    (restrictBase : ThroatBase → BulkBase)
    (bulkCore : VectorBundleCore 𝕜 BulkBase BulkFiber BulkChart)
    (throatCore : VectorBundleCore 𝕜 ThroatBase ThroatFiber ThroatChart)
    (bulkCoordinates : SmoothCoreSectionCoordinates IBulk bulkCore)
    (throatCoordinates : SmoothCoreSectionCoordinates IThroat throatCore) where
  chartMap : ThroatChart → BulkChart
  trace : ThroatBase → BulkFiber →L[𝕜] ThroatFiber
  localTrace : ThroatChart → ThroatBase → BulkFiber →L[𝕜] ThroatFiber
  baseSet_compatible :
    ∀ chart base, base ∈ throatCore.baseSet chart →
      restrictBase base ∈ bulkCore.baseSet (chartMap chart)
  value_compatible :
    ∀ base,
      throatCoordinates.value base =
        trace base (bulkCoordinates.value (restrictBase base))
  extractor_compatible :
    ∀ chart base, base ∈ throatCore.baseSet chart →
      throatCoordinates.extractor chart base =
        localTrace chart base
          (bulkCoordinates.extractor (chartMap chart) (restrictBase base))

/-- Exact local overlap law derived from the preferred-value and extractor
compatibilities of a carrier trace. -/
theorem SmoothCoreCarrierTrace.coordinate_compatible
    {restrictBase : ThroatBase → BulkBase}
    {bulkCore : VectorBundleCore 𝕜 BulkBase BulkFiber BulkChart}
    {throatCore : VectorBundleCore 𝕜 ThroatBase ThroatFiber ThroatChart}
    {bulkCoordinates : SmoothCoreSectionCoordinates IBulk bulkCore}
    {throatCoordinates : SmoothCoreSectionCoordinates IThroat throatCore}
    (carrier : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkCore throatCore bulkCoordinates throatCoordinates)
    (chart : ThroatChart) (base : ThroatBase)
    (hBase : base ∈ throatCore.baseSet chart) :
    throatCore.coordChange (throatCore.indexAt base) chart base
        (carrier.trace base (bulkCoordinates.value (restrictBase base))) =
      carrier.localTrace chart base
        (bulkCore.coordChange (bulkCore.indexAt (restrictBase base))
          (carrier.chartMap chart) (restrictBase base)
          (bulkCoordinates.value (restrictBase base))) := by
  calc
    throatCore.coordChange (throatCore.indexAt base) chart base
        (carrier.trace base (bulkCoordinates.value (restrictBase base))) =
      throatCore.coordChange (throatCore.indexAt base) chart base
        (throatCoordinates.value base) := by
          rw [carrier.value_compatible base]
    _ = throatCoordinates.extractor chart base :=
      throatCoordinates.coordinate_eq chart base hBase
    _ = carrier.localTrace chart base
        (bulkCoordinates.extractor (carrier.chartMap chart)
          (restrictBase base)) :=
      carrier.extractor_compatible chart base hBase
    _ = carrier.localTrace chart base
        (bulkCore.coordChange (bulkCore.indexAt (restrictBase base))
          (carrier.chartMap chart) (restrictBase base)
          (bulkCoordinates.value (restrictBase base))) := by
      rw [bulkCoordinates.coordinate_eq (carrier.chartMap chart)
        (restrictBase base) (carrier.baseSet_compatible chart base hBase)]

variable {FirstBulkFiber : Type uFirstBulkFiber}
variable {FirstThroatFiber : Type uFirstThroatFiber}
variable {SecondBulkFiber : Type uSecondBulkFiber}
variable {SecondThroatFiber : Type uSecondThroatFiber}
variable [NormedAddCommGroup FirstBulkFiber] [NormedSpace 𝕜 FirstBulkFiber]
variable [NormedAddCommGroup FirstThroatFiber] [NormedSpace 𝕜 FirstThroatFiber]
variable [NormedAddCommGroup SecondBulkFiber] [NormedSpace 𝕜 SecondBulkFiber]
variable [NormedAddCommGroup SecondThroatFiber] [NormedSpace 𝕜 SecondThroatFiber]
variable {FirstBulkChart : Type uFirstBulkChart}
variable {FirstThroatChart : Type uFirstThroatChart}
variable {SecondBulkChart : Type uSecondBulkChart}
variable {SecondThroatChart : Type uSecondThroatChart}

/-- Product of two exact smooth coordinate packages. -/
def smoothCoreSectionCoordinatesProd
    {Base : Type*} [TopologicalSpace Base]
    {Model : Type*} [NormedAddCommGroup Model] [NormedSpace 𝕜 Model]
    {ModelSpace : Type*} [TopologicalSpace ModelSpace]
    (IBase : ModelWithCorners 𝕜 Model ModelSpace)
    [ChartedSpace ModelSpace Base]
    {FirstFiber : Type*} {SecondFiber : Type*}
    [NormedAddCommGroup FirstFiber] [NormedSpace 𝕜 FirstFiber]
    [NormedAddCommGroup SecondFiber] [NormedSpace 𝕜 SecondFiber]
    {FirstChart : Type*} {SecondChart : Type*}
    (firstCore : VectorBundleCore 𝕜 Base FirstFiber FirstChart)
    (secondCore : VectorBundleCore 𝕜 Base SecondFiber SecondChart)
    (firstCoordinates : SmoothCoreSectionCoordinates IBase firstCore)
    (secondCoordinates : SmoothCoreSectionCoordinates IBase secondCore) :
    SmoothCoreSectionCoordinates IBase
      (vectorBundleCoreProd firstCore secondCore) where
  value base := (firstCoordinates.value base, secondCoordinates.value base)
  extractor chart base :=
    (firstCoordinates.extractor chart.1 base,
      secondCoordinates.extractor chart.2 base)
  coordinate_eq := by
    intro chart base hBase
    change
      (firstCore.coordChange (firstCore.indexAt base) chart.1 base
          (firstCoordinates.value base),
        secondCore.coordChange (secondCore.indexAt base) chart.2 base
          (secondCoordinates.value base)) =
      (firstCoordinates.extractor chart.1 base,
        secondCoordinates.extractor chart.2 base)
    rw [firstCoordinates.coordinate_eq chart.1 base hBase.1,
      secondCoordinates.coordinate_eq chart.2 base hBase.2]
  extractor_contMDiffOn := by
    intro chart
    have hFirst :=
      (firstCoordinates.extractor_contMDiffOn chart.1).mono (by
        intro base hBase
        exact hBase.1)
    have hSecond :=
      (secondCoordinates.extractor_contMDiffOn chart.2).mono (by
        intro base hBase
        exact hBase.2)
    exact hFirst.prodMk_space hSecond

/-- Product of two carrier traces over the same throat-to-bulk base map. -/
def smoothCoreCarrierTraceProd
    (restrictBase : ThroatBase → BulkBase)
    (firstBulkCore : VectorBundleCore 𝕜 BulkBase FirstBulkFiber FirstBulkChart)
    (firstThroatCore : VectorBundleCore 𝕜 ThroatBase FirstThroatFiber FirstThroatChart)
    (secondBulkCore : VectorBundleCore 𝕜 BulkBase SecondBulkFiber SecondBulkChart)
    (secondThroatCore : VectorBundleCore 𝕜 ThroatBase SecondThroatFiber SecondThroatChart)
    (firstBulkCoordinates : SmoothCoreSectionCoordinates IBulk firstBulkCore)
    (firstThroatCoordinates : SmoothCoreSectionCoordinates IThroat firstThroatCore)
    (secondBulkCoordinates : SmoothCoreSectionCoordinates IBulk secondBulkCore)
    (secondThroatCoordinates : SmoothCoreSectionCoordinates IThroat secondThroatCore)
    (firstTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      firstBulkCore firstThroatCore firstBulkCoordinates firstThroatCoordinates)
    (secondTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      secondBulkCore secondThroatCore secondBulkCoordinates secondThroatCoordinates) :
    SmoothCoreCarrierTrace IBulk IThroat restrictBase
      (vectorBundleCoreProd firstBulkCore secondBulkCore)
      (vectorBundleCoreProd firstThroatCore secondThroatCore)
      (smoothCoreSectionCoordinatesProd IBulk firstBulkCore secondBulkCore
        firstBulkCoordinates secondBulkCoordinates)
      (smoothCoreSectionCoordinatesProd IThroat firstThroatCore secondThroatCore
        firstThroatCoordinates secondThroatCoordinates) where
  chartMap chart :=
    (firstTrace.chartMap chart.1, secondTrace.chartMap chart.2)
  trace base := (firstTrace.trace base).prodMap (secondTrace.trace base)
  localTrace chart base :=
    (firstTrace.localTrace chart.1 base).prodMap
      (secondTrace.localTrace chart.2 base)
  baseSet_compatible := by
    intro chart base hBase
    exact ⟨firstTrace.baseSet_compatible chart.1 base hBase.1,
      secondTrace.baseSet_compatible chart.2 base hBase.2⟩
  value_compatible := by
    intro base
    change
      (firstThroatCoordinates.value base,
        secondThroatCoordinates.value base) =
      (firstTrace.trace base
          (firstBulkCoordinates.value (restrictBase base)),
        secondTrace.trace base
          (secondBulkCoordinates.value (restrictBase base)))
    rw [firstTrace.value_compatible base, secondTrace.value_compatible base]
  extractor_compatible := by
    intro chart base hBase
    change
      (firstThroatCoordinates.extractor chart.1 base,
        secondThroatCoordinates.extractor chart.2 base) =
      (firstTrace.localTrace chart.1 base
          (firstBulkCoordinates.extractor (firstTrace.chartMap chart.1)
            (restrictBase base)),
        secondTrace.localTrace chart.2 base
          (secondBulkCoordinates.extractor (secondTrace.chartMap chart.2)
            (restrictBase base)))
    rw [firstTrace.extractor_compatible chart.1 base hBase.1,
      secondTrace.extractor_compatible chart.2 base hBase.2]

variable {NewBulkChart : Type uNewBulkChart}
variable {NewThroatChart : Type uNewThroatChart}

/-- Reindex a smooth coordinate package along a chart equivalence. -/
def reindexSmoothCoreSectionCoordinates
    (core : VectorBundleCore 𝕜 BulkBase BulkFiber BulkChart)
    (indexEquiv : NewBulkChart ≃ BulkChart)
    (coordinates : SmoothCoreSectionCoordinates IBulk core) :
    SmoothCoreSectionCoordinates IBulk
      (reindexVectorBundleCore core indexEquiv) where
  value := coordinates.value
  extractor chart := coordinates.extractor (indexEquiv chart)
  coordinate_eq := by
    intro chart base hBase
    change
      core.coordChange (indexEquiv (indexEquiv.symm (core.indexAt base)))
          (indexEquiv chart) base (coordinates.value base) =
        coordinates.extractor (indexEquiv chart) base
    rw [indexEquiv.apply_symm_apply]
    exact coordinates.coordinate_eq (indexEquiv chart) base hBase
  extractor_contMDiffOn := by
    intro chart
    exact coordinates.extractor_contMDiffOn (indexEquiv chart)

/-- Reindex both carrier atlases without changing any trace map or section
value. -/
def reindexSmoothCoreCarrierTrace
    (restrictBase : ThroatBase → BulkBase)
    (bulkCore : VectorBundleCore 𝕜 BulkBase BulkFiber BulkChart)
    (throatCore : VectorBundleCore 𝕜 ThroatBase ThroatFiber ThroatChart)
    (bulkIndexEquiv : NewBulkChart ≃ BulkChart)
    (throatIndexEquiv : NewThroatChart ≃ ThroatChart)
    (bulkCoordinates : SmoothCoreSectionCoordinates IBulk bulkCore)
    (throatCoordinates : SmoothCoreSectionCoordinates IThroat throatCore)
    (carrier : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkCore throatCore bulkCoordinates throatCoordinates) :
    SmoothCoreCarrierTrace IBulk IThroat restrictBase
      (reindexVectorBundleCore bulkCore bulkIndexEquiv)
      (reindexVectorBundleCore throatCore throatIndexEquiv)
      (reindexSmoothCoreSectionCoordinates IBulk bulkCore bulkIndexEquiv bulkCoordinates)
      (reindexSmoothCoreSectionCoordinates IThroat throatCore throatIndexEquiv
        throatCoordinates) where
  chartMap chart :=
    bulkIndexEquiv.symm (carrier.chartMap (throatIndexEquiv chart))
  trace := carrier.trace
  localTrace chart := carrier.localTrace (throatIndexEquiv chart)
  baseSet_compatible := by
    intro chart base hBase
    exact carrier.baseSet_compatible (throatIndexEquiv chart) base hBase
  value_compatible := carrier.value_compatible
  extractor_compatible := by
    intro chart base hBase
    exact carrier.extractor_compatible (throatIndexEquiv chart) base hBase

end

end P0EFTJanusPhysicalSecondJetCarrierTraceProduct
end JanusFormal
