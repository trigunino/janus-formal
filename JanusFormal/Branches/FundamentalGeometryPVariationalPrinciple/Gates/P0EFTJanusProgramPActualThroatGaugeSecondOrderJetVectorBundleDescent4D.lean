import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDependentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D

/-!
# Pointwise descent into the throat gauge second-jet vector bundle

The exact presentation quotient is identified fiberwise with the model fiber
of the vector-bundle core, using its preferred frame/chart pair.  The actual
classes therefore define a set-theoretic section of the genuine topological
bundle.  Smoothness of that section is not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D

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

/-- The model fiber carried by the constructed vector-bundle core. -/
abbrev ThroatGaugeSecondOrderJetVectorBundleFiber
    (current : EffectiveThroat period hPeriod) :=
  (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).Fiber current

/-- The topological total space constructed by the vector-bundle core. -/
abbrev ThroatGaugeSecondOrderJetVectorBundleTotalSpace :=
  (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).TotalSpace

/-- The exact pointwise presentation quotient is the fiber of the constructed
bundle after normalization in the preferred pair `(current, current)`. -/
def throatGaugeSecondOrderJetPointwiseQuotientEquivVectorBundleFiberAt
    (current : EffectiveThroat period hPeriod) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current ≃
      ThroatGaugeSecondOrderJetVectorBundleFiber period hPeriod current := by
  have hCurrent :=
    mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current
  exact throatGaugeSecondOrderJetPointwiseQuotientEquivAt period hPeriod
    current current current hCurrent.1 hCurrent.2

/-- Include a pointwise quotient class in the genuine bundle total space. -/
def throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
    (current : EffectiveThroat period hPeriod)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    ThroatGaugeSecondOrderJetVectorBundleTotalSpace period hPeriod :=
  ⟨current,
    throatGaugeSecondOrderJetPointwiseQuotientEquivVectorBundleFiberAt
      period hPeriod current jetClass⟩

@[simp]
theorem throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace_fst
    (current : EffectiveThroat period hPeriod)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    (throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
      period hPeriod current jetClass).1 = current :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace_snd
    (current : EffectiveThroat period hPeriod)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    (throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
      period hPeriod current jetClass).2 =
      throatGaugeSecondOrderJetPointwiseQuotientEquivVectorBundleFiberAt
        period hPeriod current jetClass :=
  rfl

/-- The actual gauge second-jet classes as a section of the constructed
topological vector bundle. -/
def actualThroatGaugeSecondOrderJetVectorBundleSection
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    EffectiveThroat period hPeriod →
      ThroatGaugeSecondOrderJetVectorBundleTotalSpace period hPeriod :=
  fun current ↦
    throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
      period hPeriod current
        (actualThroatGaugeSecondOrderJetPointwiseClass
          period hPeriod potential component current)

@[simp]
theorem actualThroatGaugeSecondOrderJetVectorBundleSection_snd
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatGaugeSecondOrderJetVectorBundleSection
      period hPeriod potential component current).2 =
      throatGaugeSecondOrderJetPointwiseQuotientEquivVectorBundleFiberAt
        period hPeriod current
          (actualThroatGaugeSecondOrderJetPointwiseClass
            period hPeriod potential component current) :=
  rfl

@[simp]
theorem actualThroatGaugeSecondOrderJetVectorBundleSection_proj
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).proj
        (actualThroatGaugeSecondOrderJetVectorBundleSection
          period hPeriod potential component current) =
      current :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D
end JanusFormal
