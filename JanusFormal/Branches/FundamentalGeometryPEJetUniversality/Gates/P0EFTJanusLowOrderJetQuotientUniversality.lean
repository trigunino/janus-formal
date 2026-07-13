import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAbelianConnectionJetNormalForm

namespace JanusFormal
namespace P0EFTJanusLowOrderJetQuotientUniversality

set_option autoImplicit false

universe u v w x

open P0EFTJanusSecondJetNormalForm
open P0EFTJanusAbelianConnectionJetNormalForm

section ImmersionSecondJet

/-- An observable on the normalized immersion second-jet model is invariant when
quadratic source-coordinate changes do not alter its value. -/
def IsSourceChangeInvariant
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [Add Tangential]
    (observable : SecondJetData Tangential Normal → Target) : Prop :=
  ∀ change jet,
    observable (sourceQuadraticChange change jet) = observable jet

/-- Inclusion of the canonical zero-tangential slice. -/
def normalSlice
    {Tangential : Type u}
    {Normal : Type v}
    [Zero Tangential]
    (normal : Normal) : SecondJetData Tangential Normal where
  tangentialQuadratic := 0
  normalQuadratic := normal

/-- Restriction of an observable to the canonical normal slice. -/
def reducedNormalObservable
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [Zero Tangential]
    (observable : SecondJetData Tangential Normal → Target) :
    Normal → Target :=
  fun normal => observable (normalSlice normal)

/-- Source-change invariance forces factorization through the normal quadratic
component. -/
theorem source_invariant_factors_through_normal
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [AddGroup Tangential]
    (observable : SecondJetData Tangential Normal → Target)
    (hInvariant : IsSourceChangeInvariant observable) :
    ∀ jet,
      observable jet =
        reducedNormalObservable observable jet.normalQuadratic := by
  intro jet
  calc
    observable jet =
        observable
          (sourceQuadraticChange (-jet.tangentialQuadratic) jet) :=
      (hInvariant (-jet.tangentialQuadratic) jet).symm
    _ = observable (normalForm jet) := by
      rw [chosen_change_reaches_normal_form]
    _ = reducedNormalObservable observable jet.normalQuadratic := by
      rfl

/-- Every function of the normal quadratic component defines a source-change
invariant observable. -/
theorem normal_factorization_is_source_invariant
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [Add Tangential]
    (reduced : Normal → Target) :
    IsSourceChangeInvariant
      (fun jet : SecondJetData Tangential Normal =>
        reduced jet.normalQuadratic) := by
  intro change jet
  rfl

/-- Exact quotient classification: invariance under quadratic source changes is
equivalent to factorization through the normal component. -/
theorem source_invariant_iff_factors_through_normal
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [AddGroup Tangential]
    (observable : SecondJetData Tangential Normal → Target) :
    IsSourceChangeInvariant observable ↔
      ∃ reduced : Normal → Target,
        ∀ jet, observable jet = reduced jet.normalQuadratic := by
  constructor
  · intro hInvariant
    exact ⟨reducedNormalObservable observable,
      source_invariant_factors_through_normal observable hInvariant⟩
  · rintro ⟨reduced, hFactor⟩
    intro change jet
    rw [hFactor (sourceQuadraticChange change jet), hFactor jet]
    rfl

/-- The reduced observable is unique. Thus the normal component has the
universal property of the orbit quotient in this algebraic model. -/
theorem source_invariant_has_unique_normal_reduction
    {Tangential : Type u}
    {Normal : Type v}
    {Target : Type w}
    [AddGroup Tangential]
    (observable : SecondJetData Tangential Normal → Target)
    (hInvariant : IsSourceChangeInvariant observable) :
    ∃! reduced : Normal → Target,
      ∀ jet, observable jet = reduced jet.normalQuadratic := by
  refine ⟨reducedNormalObservable observable,
    source_invariant_factors_through_normal observable hInvariant, ?_⟩
  intro other hOther
  funext normal
  have hAtSlice := hOther (normalSlice normal)
  simpa [reducedNormalObservable, normalSlice] using hAtSlice.symm

end ImmersionSecondJet

section AbelianConnectionJet

/-- Gauge invariance of an observable on the decomposed abelian connection
one-jet model. -/
def IsGaugeJetInvariant
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [Add Value]
    [Add SymmetricDerivative]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target) : Prop :=
  ∀ gauge jet,
    observable (gaugeChange gauge jet) = observable jet

/-- Inclusion of the canonical curvature-only slice. -/
def curvatureSlice
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Zero Value]
    [Zero SymmetricDerivative]
    (curvature : Curvature) :
    ConnectionOneJet Value SymmetricDerivative Curvature where
  value := 0
  symmetricDerivative := 0
  curvature := curvature

/-- Restriction of a connection-jet observable to the curvature-only slice. -/
def reducedCurvatureObservable
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [Zero Value]
    [Zero SymmetricDerivative]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target) :
    Curvature → Target :=
  fun curvature => observable (curvatureSlice curvature)

/-- Gauge invariance forces factorization through curvature. -/
theorem gauge_invariant_factors_through_curvature
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target)
    (hInvariant : IsGaugeJetInvariant observable) :
    ∀ jet,
      observable jet =
        reducedCurvatureObservable observable jet.curvature := by
  intro jet
  calc
    observable jet =
        observable (gaugeChange (normalizingGauge jet) jet) :=
      (hInvariant (normalizingGauge jet) jet).symm
    _ = observable (curvatureNormalForm jet) := by
      rw [chosen_gauge_reaches_curvature_normal_form]
    _ = reducedCurvatureObservable observable jet.curvature := by
      rfl

/-- Every function of curvature defines a gauge-invariant one-jet observable. -/
theorem curvature_factorization_is_gauge_invariant
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [Add Value]
    [Add SymmetricDerivative]
    (reduced : Curvature → Target) :
    IsGaugeJetInvariant
      (fun jet : ConnectionOneJet Value SymmetricDerivative Curvature =>
        reduced jet.curvature) := by
  intro gauge jet
  rfl

/-- Exact quotient classification for the abelian connection one-jet model. -/
theorem gauge_invariant_iff_factors_through_curvature
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target) :
    IsGaugeJetInvariant observable ↔
      ∃ reduced : Curvature → Target,
        ∀ jet, observable jet = reduced jet.curvature := by
  constructor
  · intro hInvariant
    exact ⟨reducedCurvatureObservable observable,
      gauge_invariant_factors_through_curvature observable hInvariant⟩
  · rintro ⟨reduced, hFactor⟩
    intro gauge jet
    rw [hFactor (gaugeChange gauge jet), hFactor jet]
    rfl

/-- Curvature has the universal property of the gauge-orbit quotient in this
algebraic one-jet model. -/
theorem gauge_invariant_has_unique_curvature_reduction
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    {Target : Type x}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target)
    (hInvariant : IsGaugeJetInvariant observable) :
    ∃! reduced : Curvature → Target,
      ∀ jet, observable jet = reduced jet.curvature := by
  refine ⟨reducedCurvatureObservable observable,
    gauge_invariant_factors_through_curvature observable hInvariant, ?_⟩
  intro other hOther
  funext curvature
  have hAtSlice := hOther (curvatureSlice curvature)
  simpa [reducedCurvatureObservable, curvatureSlice] using hAtSlice.symm

end AbelianConnectionJet

/-- The universal quotient theorems are low-order algebraic results. Promotion to
the Janus geometry requires the concrete jet actions and the smooth quotient
presentation. -/
structure LowOrderQuotientUniversalityStatus where
  immersionSourceActionGeometricallyDerived : Prop
  connectionGaugeActionGeometricallyDerived : Prop
  abstractUniversalFactorizationsProved : Prop
  reducedTensorSpacesIdentified : Prop
  residualFrameActionsConstructed : Prop
  smoothQuotientPropertiesProved : Prop
  compatibleStructuredJetGroupoidConstructed : Prop

/-- Closure of the genuine low-order structured-jet quotient theorem. -/
def lowOrderQuotientUniversalityClosed
    (s : LowOrderQuotientUniversalityStatus) : Prop :=
  s.immersionSourceActionGeometricallyDerived /\
  s.connectionGaugeActionGeometricallyDerived /\
  s.abstractUniversalFactorizationsProved /\
  s.reducedTensorSpacesIdentified /\
  s.residualFrameActionsConstructed /\
  s.smoothQuotientPropertiesProved /\
  s.compatibleStructuredJetGroupoidConstructed

/-- Algebraic factorization alone does not identify the residual frame action on
second fundamental form and curvature tensors. -/
theorem missing_residual_action_blocks_geometric_quotient
    (s : LowOrderQuotientUniversalityStatus)
    (hMissing : Not s.residualFrameActionsConstructed) :
    Not (lowOrderQuotientUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end P0EFTJanusLowOrderJetQuotientUniversality
end JanusFormal
