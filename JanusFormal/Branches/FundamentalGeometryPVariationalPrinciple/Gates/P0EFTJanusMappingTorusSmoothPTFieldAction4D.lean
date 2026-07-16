import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldDescent4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution

/-!
# PT/exchange on smooth fields of the effective D8 quotient

The analytic PT diffeomorphism acts by pullback on genuine smooth quotient
fields.  Exchanging two sectors after this pullback is an exact involution.
This is a coefficient-field construction; tensor representations, gauge
fields and boundary trace conditions remain separate tasks.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothPTFieldAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- Pullback of a smooth coefficient field by the actual analytic PT
diffeomorphism of the quotient. -/
def ptPullback
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothQuotientField period hPeriod Fiber where
  toFun := field ∘ reflectedSpherePT period hPeriod
  contMDiff_toFun := field.contMDiff_toFun.comp
    (reflectedSpherePT_contMDiff period hPeriod)

@[simp]
theorem ptPullback_apply
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    ptPullback period hPeriod Fiber field point =
      field (reflectedSpherePT period hPeriod point) :=
  rfl

@[simp]
theorem ptPullback_involutive
    (field : SmoothQuotientField period hPeriod Fiber) :
    ptPullback period hPeriod Fiber
        (ptPullback period hPeriod Fiber field) = field := by
  apply SmoothQuotientField.ext period hPeriod Fiber
  intro point
  simp [ptPullback_apply, reflectedSpherePT_involutive]

/-- PT pullback is an exact equivalence of the smooth quotient-field space. -/
def ptPullbackEquiv :
    SmoothQuotientField period hPeriod Fiber ≃
      SmoothQuotientField period hPeriod Fiber where
  toFun := ptPullback period hPeriod Fiber
  invFun := ptPullback period hPeriod Fiber
  left_inv := ptPullback_involutive period hPeriod Fiber
  right_inv := ptPullback_involutive period hPeriod Fiber

/-- Candidate-A sector exchange: pull back both fields by PT and interchange
their labels. -/
def sectorExchange
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) :
    SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber :=
  (ptPullback period hPeriod Fiber fields.2,
    ptPullback period hPeriod Fiber fields.1)

@[simp]
theorem sectorExchange_fst
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) :
    (sectorExchange period hPeriod Fiber fields).1 =
      ptPullback period hPeriod Fiber fields.2 :=
  rfl

@[simp]
theorem sectorExchange_snd
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) :
    (sectorExchange period hPeriod Fiber fields).2 =
      ptPullback period hPeriod Fiber fields.1 :=
  rfl

@[simp]
theorem sectorExchange_involutive
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) :
    sectorExchange period hPeriod Fiber
        (sectorExchange period hPeriod Fiber fields) = fields := by
  ext <;> simp [sectorExchange]

/-- The smooth two-sector field space equipped with PT/exchange as an exact
involutive equivalence. -/
def sectorExchangeEquiv :
    (SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) ≃
    (SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) where
  toFun := sectorExchange period hPeriod Fiber
  invFun := sectorExchange period hPeriod Fiber
  left_inv := sectorExchange_involutive period hPeriod Fiber
  right_inv := sectorExchange_involutive period hPeriod Fiber

/-- Exact PT matching of the two smooth sectors. -/
def PTMatched
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) : Prop :=
  fields.2 = ptPullback period hPeriod Fiber fields.1

theorem ptMatched_iff_fixed_exchange
    (fields : SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber) :
    PTMatched period hPeriod Fiber fields ↔
      sectorExchange period hPeriod Fiber fields = fields := by
  constructor
  · intro hMatched
    change fields.2 = ptPullback period hPeriod Fiber fields.1 at hMatched
    apply Prod.ext
    · rw [sectorExchange_fst, hMatched, ptPullback_involutive]
    · exact hMatched.symm
  · intro hFixed
    have hSecond := congrArg Prod.snd hFixed
    simpa [PTMatched, sectorExchange] using hSecond.symm

/-- Every smooth field supplies a nonempty exactly PT-matched two-sector
configuration on the global quotient. -/
def matchedPair
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothQuotientField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber :=
  (field, ptPullback period hPeriod Fiber field)

theorem matchedPair_ptMatched
    (field : SmoothQuotientField period hPeriod Fiber) :
    PTMatched period hPeriod Fiber
      (matchedPair period hPeriod Fiber field) :=
  rfl

end

end P0EFTJanusMappingTorusSmoothPTFieldAction4D
end JanusFormal
