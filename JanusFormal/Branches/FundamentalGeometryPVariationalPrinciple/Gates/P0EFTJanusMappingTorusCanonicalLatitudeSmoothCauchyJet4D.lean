import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetAllWindingDeck4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

/-!
# Jointly smooth deck-compatible latitude Cauchy jets

For smooth boundary value and oriented-normal representatives, the exact collar
formula

`η(ν) g(x) + ν η(ν) h(x)`

is jointly smooth in the latitude base and normal coordinate.  It has the
prescribed first Cauchy jet, is invariant under every integer deck winding, and
has support strictly inside the genuine tubular band.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeSmoothCauchyJet4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology Filter
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetAllWindingDeck4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeBaseIsManifold :
    IsManifold canonicalLatitudeBaseModelWithCorners ω CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeParameterChartedSpace :
    ChartedSpace CanonicalLatitudeParameterModel CanonicalLatitudeParameter :=
  inferInstance

local instance canonicalLatitudeParameterIsManifold :
    IsManifold canonicalLatitudeParameterModelWithCorners ω
      CanonicalLatitudeParameter :=
  inferInstance

variable {period : Real}

/-- Smooth value and oriented-normal boundary representatives with the correct
mapping-torus deck parity. -/
structure SmoothCanonicalLatitudeDeckCauchyData (period : Real) where
  value : CanonicalLatitudeBase → Real
  normal : CanonicalLatitudeBase → Real
  value_contMDiff : ContMDiff canonicalLatitudeBaseModelWithCorners
    𝓘(Real, Real) ∞ value
  normal_contMDiff : ContMDiff canonicalLatitudeBaseModelWithCorners
    𝓘(Real, Real) ∞ normal
  value_periodic : CanonicalLatitudeValueDeckPeriodic period value
  normal_antiperiodic : CanonicalLatitudeNormalDeckAntiperiodic period normal

namespace SmoothCanonicalLatitudeDeckCauchyData

/-- Underlying deck-compatible Cauchy data. -/
def toDeckCauchyData
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D.CanonicalLatitudeDeckCauchyData
      period where
  value := data.value
  normal := data.normal
  value_periodic := data.value_periodic
  normal_antiperiodic := data.normal_antiperiodic

/-- Exact local collar extension. -/
def localExtension
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    CanonicalLatitudeParameter → Real :=
  canonicalLatitudeLocalCauchyExtension (data.value, data.normal)

/-- Joint smoothness of the exact local collar extension. -/
theorem localExtension_contMDiff
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    ContMDiff canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real) ∞ data.localExtension := by
  unfold localExtension canonicalLatitudeLocalCauchyExtension
  have hValueProfile : ContMDiff canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real) ∞
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeCauchyValueProfile parameter.2) :=
    canonicalLatitudeCauchyValueProfile_contDiff.contMDiff.comp contMDiff_snd
  have hNormalProfile : ContMDiff canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real) ∞
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeCauchyNormalProfile parameter.2) :=
    canonicalLatitudeCauchyNormalProfile_contDiff.contMDiff.comp contMDiff_snd
  have hValue : ContMDiff canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real) ∞
      (fun parameter : CanonicalLatitudeParameter => data.value parameter.1) :=
    data.value_contMDiff.comp contMDiff_fst
  have hNormal : ContMDiff canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real) ∞
      (fun parameter : CanonicalLatitudeParameter => data.normal parameter.1) :=
    data.normal_contMDiff.comp contMDiff_fst
  exact (hValueProfile.mul hValue).add (hNormalProfile.mul hNormal)

/-- Exact value trace on the zero-normal slice. -/
@[simp] theorem localExtension_zero
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (base : CanonicalLatitudeBase) :
    data.localExtension (base, 0) = data.value base :=
  canonicalLatitudeLocalCauchyExtensionSlice_zero
    (data.value, data.normal) base

/-- Exact normal derivative on the zero-normal slice. -/
@[simp] theorem deriv_localExtension_slice_zero
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (base : CanonicalLatitudeBase) :
    deriv (fun normal => data.localExtension (base, normal)) 0 =
      data.normal base :=
  deriv_canonicalLatitudeLocalCauchyExtensionSlice_zero
    (data.value, data.normal) base

/-- Support of every normal slice lies in the open unit band. -/
theorem support_localExtension_slice_subset
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (base : CanonicalLatitudeBase) :
    Function.support (fun normal => data.localExtension (base, normal)) ⊆
      Set.Ioo (-1 : Real) 1 :=
  support_canonicalLatitudeLocalCauchyExtensionSlice_subset
    (data.value, data.normal) base

/-- The local extension vanishes whenever the normal coordinate has magnitude at
least one. -/
theorem localExtension_eq_zero_of_one_le_abs
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : 1 ≤ |normal|) :
    data.localExtension (base, normal) = 0 :=
  canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
    (data.value, data.normal) base normal hNormal

/-- All-winding deck invariance of the jointly smooth local extension. -/
theorem localExtension_deck_zpow
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (winding : Int) (parameter : CanonicalLatitudeParameter) :
    data.localExtension
        ((canonicalLatitudeCollarDeckEquiv period ^ winding) parameter) =
      data.localExtension parameter :=
  canonicalLatitudeLocalCauchyExtension_deck_zpow
    period data.value data.normal data.value_periodic
      data.normal_antiperiodic winding parameter

/-- Joint smoothness, exact jets, deck gluing and strict support in one package. -/
theorem certificate
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    ContMDiff canonicalLatitudeParameterModelWithCorners
        𝓘(Real, Real) ∞ data.localExtension ∧
      (∀ base, data.localExtension (base, 0) = data.value base) ∧
      (∀ base,
        deriv (fun normal => data.localExtension (base, normal)) 0 =
          data.normal base) ∧
      (∀ (winding : Int) (parameter : CanonicalLatitudeParameter),
        data.localExtension
            ((canonicalLatitudeCollarDeckEquiv period ^ winding) parameter) =
          data.localExtension parameter) ∧
      (∀ base,
        Function.support (fun normal => data.localExtension (base, normal)) ⊆
          Set.Ioo (-1 : Real) 1) :=
  ⟨data.localExtension_contMDiff,
    data.localExtension_zero,
    data.deriv_localExtension_slice_zero,
    data.localExtension_deck_zpow,
    data.support_localExtension_slice_subset⟩

end SmoothCanonicalLatitudeDeckCauchyData

end
end P0EFTJanusMappingTorusCanonicalLatitudeSmoothCauchyJet4D
end JanusFormal
