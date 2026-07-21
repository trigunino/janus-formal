import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding

/-! # Canonical effective decorated mapping torus -/

namespace JanusFormal
namespace P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev EffectiveAmbient := MappingTorus (reflectedSphereData period hPeriod)
abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveAmbient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveAmbient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- A genuine smooth topological embedding of the effective throat into the
effective ambient quotient. -/
abbrev SmoothEffectiveThroatEmbedding :=
  { inclusion : EffectiveThroat period hPeriod → EffectiveAmbient period hPeriod //
      ContMDiff throatCoverModelWithCorners coverModelWithCorners ω inclusion ∧
        Topology.IsEmbedding inclusion }

def canonicalSmoothEffectiveThroatEmbedding :
    SmoothEffectiveThroatEmbedding period hPeriod :=
  ⟨fixedThroatQuotientInclusion period hPeriod,
    fixedThroatQuotientInclusion_contMDiff period hPeriod,
    fixedThroatQuotientInclusion_isEmbedding period hPeriod⟩

/-- Already-constructed global decorations carried simultaneously by the
same effective D8 quotient and its canonical throat. -/
structure CanonicalEffectiveDecoratedMappingTorus where
  lorentzMetric : SmoothGeneralLorentzMetric period hPeriod
  actionMeasure : FiniteNonzeroActionMeasure period hPeriod
  spacetimePT : EffectiveAmbient period hPeriod ≃ₘ^ω⟮
    coverModelWithCorners, coverModelWithCorners⟯ EffectiveAmbient period hPeriod
  throatPT : EffectiveThroat period hPeriod ≃ₘ^ω⟮
    throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      EffectiveThroat period hPeriod
  throatEmbedding : SmoothEffectiveThroatEmbedding period hPeriod
  ambientPinMinusBundle :
    CanonicalAmbientPinMinusActualPrincipalBundle period hPeriod

/-- The canonical metric, volume, PT maps, throat embedding and actual
`Pin⁻(4)` principal bundle assembled on one base. -/
def canonicalEffectiveDecoratedMappingTorus :
    CanonicalEffectiveDecoratedMappingTorus period hPeriod where
  lorentzMetric := intrinsicSmoothGeneralLorentzMetric period hPeriod
  actionMeasure := intrinsicCanonicalLorentzActionMeasure period hPeriod
  spacetimePT := reflectedSpherePTDiffeomorph period hPeriod
  throatPT := fixedThroatPTDiffeomorph period hPeriod
  throatEmbedding := canonicalSmoothEffectiveThroatEmbedding period hPeriod
  ambientPinMinusBundle :=
    canonicalAmbientPinMinusActualPrincipalBundle period hPeriod

@[simp] theorem canonicalEffectiveDecoratedMappingTorus_lorentzMetric :
    (canonicalEffectiveDecoratedMappingTorus period hPeriod).lorentzMetric =
      intrinsicSmoothGeneralLorentzMetric period hPeriod := rfl

@[simp] theorem canonicalEffectiveDecoratedMappingTorus_actionMeasure :
    (canonicalEffectiveDecoratedMappingTorus period hPeriod).actionMeasure =
      intrinsicCanonicalLorentzActionMeasure period hPeriod := rfl

@[simp] theorem canonicalEffectiveDecoratedMappingTorus_throatEmbedding :
    (canonicalEffectiveDecoratedMappingTorus period hPeriod).throatEmbedding.1 =
      fixedThroatQuotientInclusion period hPeriod := rfl

theorem canonicalEffectiveDecoratedMappingTorus_pinMinusCore :
    (canonicalEffectiveDecoratedMappingTorus period hPeriod).ambientPinMinusBundle.core =
      canonicalAmbientPinMinusPrincipalBundleCore period hPeriod :=
  (canonicalEffectiveDecoratedMappingTorus period hPeriod).ambientPinMinusBundle.core_eq

end
end P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D
end JanusFormal
