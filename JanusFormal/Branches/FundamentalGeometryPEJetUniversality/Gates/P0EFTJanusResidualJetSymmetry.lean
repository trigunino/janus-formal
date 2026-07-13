import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderJetQuotientUniversality

namespace JanusFormal
namespace P0EFTJanusResidualJetSymmetry

set_option autoImplicit false

universe u v w x y

open P0EFTJanusSecondJetNormalForm
open P0EFTJanusAbelianConnectionJetNormalForm
open P0EFTJanusLowOrderJetQuotientUniversality

section ImmersionSecondJet

/-- Coordinatewise action of a residual frame symmetry on the reduced
second-immersion-jet model. -/
def actOnSecondJet
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    [SMul Symmetry Tangential]
    [SMul Symmetry Normal]
    (symmetry : Symmetry)
    (jet : SecondJetData Tangential Normal) :
    SecondJetData Tangential Normal where
  tangentialQuadratic := symmetry • jet.tangentialQuadratic
  normalQuadratic := symmetry • jet.normalQuadratic

/-- The coordinatewise formula is a genuine group action whenever the two
components are group actions. -/
@[simp]
theorem actOnSecondJet_one
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    [Group Symmetry]
    [MulAction Symmetry Tangential]
    [MulAction Symmetry Normal]
    (jet : SecondJetData Tangential Normal) :
    actOnSecondJet (1 : Symmetry) jet = jet := by
  ext <;> simp [actOnSecondJet]

@[simp]
theorem actOnSecondJet_mul
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    [Group Symmetry]
    [MulAction Symmetry Tangential]
    [MulAction Symmetry Normal]
    (first second : Symmetry)
    (jet : SecondJetData Tangential Normal) :
    actOnSecondJet (first * second) jet =
      actOnSecondJet first (actOnSecondJet second jet) := by
  ext <;> simp [actOnSecondJet, mul_smul]

/-- Additivity of the residual tangent action is exactly the compatibility
needed to commute residual symmetries with quadratic source changes. -/
theorem residual_action_commutes_with_source_change
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    [Add Tangential]
    [SMul Symmetry Tangential]
    [SMul Symmetry Normal]
    (hAdd : ∀ (symmetry : Symmetry) (first second : Tangential),
      symmetry • (first + second) =
        symmetry • first + symmetry • second)
    (symmetry : Symmetry)
    (change : Tangential)
    (jet : SecondJetData Tangential Normal) :
    actOnSecondJet symmetry (sourceQuadraticChange change jet) =
      sourceQuadraticChange (symmetry • change)
        (actOnSecondJet symmetry jet) := by
  ext
  · exact hAdd symmetry jet.tangentialQuadratic change
  · rfl

/-- Equivariance of an observable under the residual frame action. -/
def IsSecondJetResidualEquivariant
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    {Target : Type x}
    [SMul Symmetry Tangential]
    [SMul Symmetry Normal]
    [SMul Symmetry Target]
    (observable : SecondJetData Tangential Normal → Target) : Prop :=
  ∀ (symmetry : Symmetry)
    (jet : SecondJetData Tangential Normal),
    observable (actOnSecondJet symmetry jet) =
      symmetry • observable jet

/-- Equivariance of a reduced observable on the normal quadratic tensor. -/
def IsNormalResidualEquivariant
    {Symmetry : Type u}
    {Normal : Type v}
    {Target : Type w}
    [SMul Symmetry Normal]
    [SMul Symmetry Target]
    (reduced : Normal → Target) : Prop :=
  ∀ (symmetry : Symmetry) (normal : Normal),
    reduced (symmetry • normal) = symmetry • reduced normal

/-- Restricting a residual-equivariant observable to the normal slice preserves
equivariance, provided the residual tangent action fixes zero. -/
theorem reduced_normal_observable_is_residual_equivariant
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    {Target : Type x}
    [Zero Tangential]
    [SMul Symmetry Tangential]
    [SMul Symmetry Normal]
    [SMul Symmetry Target]
    (hZero : ∀ symmetry : Symmetry,
      symmetry • (0 : Tangential) = 0)
    (observable : SecondJetData Tangential Normal → Target)
    (hEquivariant : IsSecondJetResidualEquivariant observable) :
    IsNormalResidualEquivariant
      (reducedNormalObservable observable) := by
  intro symmetry normal
  calc
    reducedNormalObservable observable (symmetry • normal) =
        observable (normalSlice (symmetry • normal)) := by
      rfl
    _ = observable
        (actOnSecondJet symmetry (normalSlice normal)) := by
      congr 1
      ext <;> simp [normalSlice, actOnSecondJet, hZero]
    _ = symmetry • observable (normalSlice normal) :=
      hEquivariant symmetry (normalSlice normal)
    _ = symmetry • reducedNormalObservable observable normal := by
      rfl

/-- Staged quotient theorem: an observable invariant under source changes and
equivariant under residual frames has one unique residual-equivariant reduction
on the normal tensor. -/
theorem source_invariant_residual_equivariant_has_unique_reduction
    {Symmetry : Type u}
    {Tangential : Type v}
    {Normal : Type w}
    {Target : Type x}
    [AddGroup Tangential]
    [SMul Symmetry Tangential]
    [SMul Symmetry Normal]
    [SMul Symmetry Target]
    (hZero : ∀ symmetry : Symmetry,
      symmetry • (0 : Tangential) = 0)
    (observable : SecondJetData Tangential Normal → Target)
    (hSource : IsSourceChangeInvariant observable)
    (hResidual : IsSecondJetResidualEquivariant observable) :
    ∃! reduced : Normal → Target,
      (∀ jet, observable jet = reduced jet.normalQuadratic) /\
        IsNormalResidualEquivariant
          (Symmetry := Symmetry) reduced := by
  refine ⟨reducedNormalObservable observable,
    ⟨source_invariant_factors_through_normal observable hSource,
      reduced_normal_observable_is_residual_equivariant
        hZero observable hResidual⟩, ?_⟩
  intro other hOther
  funext normal
  have hAtSlice := hOther.1 (normalSlice normal)
  simpa [reducedNormalObservable, normalSlice] using hAtSlice.symm

end ImmersionSecondJet

section AbelianConnectionJet

/-- Coordinatewise residual action on the decomposed abelian connection
one-jet. -/
def actOnConnectionJet
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    [SMul Symmetry Value]
    [SMul Symmetry SymmetricDerivative]
    [SMul Symmetry Curvature]
    (symmetry : Symmetry)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    ConnectionOneJet Value SymmetricDerivative Curvature where
  value := symmetry • jet.value
  symmetricDerivative := symmetry • jet.symmetricDerivative
  curvature := symmetry • jet.curvature

@[simp]
theorem actOnConnectionJet_one
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    [Group Symmetry]
    [MulAction Symmetry Value]
    [MulAction Symmetry SymmetricDerivative]
    [MulAction Symmetry Curvature]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    actOnConnectionJet (1 : Symmetry) jet = jet := by
  ext <;> simp [actOnConnectionJet]

@[simp]
theorem actOnConnectionJet_mul
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    [Group Symmetry]
    [MulAction Symmetry Value]
    [MulAction Symmetry SymmetricDerivative]
    [MulAction Symmetry Curvature]
    (first second : Symmetry)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    actOnConnectionJet (first * second) jet =
      actOnConnectionJet first (actOnConnectionJet second jet) := by
  ext <;> simp [actOnConnectionJet, mul_smul]

/-- Residual linearity on the gauge-removable components makes the residual
action commute with abelian gauge two-jets. -/
theorem residual_action_commutes_with_gauge_change
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    [Add Value]
    [Add SymmetricDerivative]
    [SMul Symmetry Value]
    [SMul Symmetry SymmetricDerivative]
    [SMul Symmetry Curvature]
    (hValueAdd : ∀ (symmetry : Symmetry) (first second : Value),
      symmetry • (first + second) =
        symmetry • first + symmetry • second)
    (hDerivativeAdd :
      ∀ (symmetry : Symmetry) (first second : SymmetricDerivative),
        symmetry • (first + second) =
          symmetry • first + symmetry • second)
    (symmetry : Symmetry)
    (gauge : GaugeTwoJet Value SymmetricDerivative)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    actOnConnectionJet symmetry (gaugeChange gauge jet) =
      gaugeChange
        { gradient := symmetry • gauge.gradient
          hessian := symmetry • gauge.hessian }
        (actOnConnectionJet symmetry jet) := by
  ext
  · exact hValueAdd symmetry jet.value gauge.gradient
  · exact hDerivativeAdd symmetry jet.symmetricDerivative gauge.hessian
  · rfl

/-- Residual equivariance of an observable on connection one-jets. -/
def IsConnectionJetResidualEquivariant
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    {Target : Type y}
    [SMul Symmetry Value]
    [SMul Symmetry SymmetricDerivative]
    [SMul Symmetry Curvature]
    [SMul Symmetry Target]
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target) : Prop :=
  ∀ (symmetry : Symmetry)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature),
    observable (actOnConnectionJet symmetry jet) =
      symmetry • observable jet

/-- Residual equivariance of an observable defined only on curvature. -/
def IsCurvatureResidualEquivariant
    {Symmetry : Type u}
    {Curvature : Type v}
    {Target : Type w}
    [SMul Symmetry Curvature]
    [SMul Symmetry Target]
    (reduced : Curvature → Target) : Prop :=
  ∀ (symmetry : Symmetry) (curvature : Curvature),
    reduced (symmetry • curvature) = symmetry • reduced curvature

/-- Restriction to the curvature slice preserves residual equivariance when the
residual action fixes the zero connection and zero symmetric derivative. -/
theorem reduced_curvature_observable_is_residual_equivariant
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    {Target : Type y}
    [Zero Value]
    [Zero SymmetricDerivative]
    [SMul Symmetry Value]
    [SMul Symmetry SymmetricDerivative]
    [SMul Symmetry Curvature]
    [SMul Symmetry Target]
    (hValueZero : ∀ symmetry : Symmetry,
      symmetry • (0 : Value) = 0)
    (hDerivativeZero : ∀ symmetry : Symmetry,
      symmetry • (0 : SymmetricDerivative) = 0)
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target)
    (hEquivariant : IsConnectionJetResidualEquivariant observable) :
    IsCurvatureResidualEquivariant
      (reducedCurvatureObservable observable) := by
  intro symmetry curvature
  calc
    reducedCurvatureObservable observable (symmetry • curvature) =
        observable (curvatureSlice (symmetry • curvature)) := by
      rfl
    _ = observable
        (actOnConnectionJet symmetry (curvatureSlice curvature)) := by
      congr 1
      ext <;> simp [curvatureSlice, actOnConnectionJet,
        hValueZero, hDerivativeZero]
    _ = symmetry • observable (curvatureSlice curvature) :=
      hEquivariant symmetry (curvatureSlice curvature)
    _ = symmetry • reducedCurvatureObservable observable curvature := by
      rfl

/-- Staged gauge quotient theorem with residual equivariance. -/
theorem gauge_invariant_residual_equivariant_has_unique_reduction
    {Symmetry : Type u}
    {Value : Type v}
    {SymmetricDerivative : Type w}
    {Curvature : Type x}
    {Target : Type y}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    [SMul Symmetry Value]
    [SMul Symmetry SymmetricDerivative]
    [SMul Symmetry Curvature]
    [SMul Symmetry Target]
    (hValueZero : ∀ symmetry : Symmetry,
      symmetry • (0 : Value) = 0)
    (hDerivativeZero : ∀ symmetry : Symmetry,
      symmetry • (0 : SymmetricDerivative) = 0)
    (observable :
      ConnectionOneJet Value SymmetricDerivative Curvature → Target)
    (hGauge : IsGaugeJetInvariant observable)
    (hResidual : IsConnectionJetResidualEquivariant observable) :
    ∃! reduced : Curvature → Target,
      (∀ jet, observable jet = reduced jet.curvature) /\
        IsCurvatureResidualEquivariant
          (Symmetry := Symmetry) reduced := by
  refine ⟨reducedCurvatureObservable observable,
    ⟨gauge_invariant_factors_through_curvature observable hGauge,
      reduced_curvature_observable_is_residual_equivariant
        hValueZero hDerivativeZero observable hResidual⟩, ?_⟩
  intro other hOther
  funext curvature
  have hAtSlice := hOther.1 (curvatureSlice curvature)
  simpa [reducedCurvatureObservable, curvatureSlice] using hAtSlice.symm

end AbelianConnectionJet

/-- The residual-symmetry theorem isolates the next concrete Janus input: the
actual tangent/normal/SpinC frame representations on the reduced tensors. -/
structure ResidualJetSymmetryStatus where
  abstractResidualActionsDefined : Prop
  compatibilityWithOrbitDirectionsProved : Prop
  uniqueEquivariantReductionsProved : Prop
  tangentNormalFrameGroupIdentified : Prop
  spinCAndTwistResidualGroupIdentified : Prop
  reducedTensorRepresentationsConstructed : Prop
  compactnessOrReductivityEstablished : Prop
  invariantTheoryApplied : Prop

/-- Closure of the residual structured-jet representation theorem. -/
def residualJetSymmetryClosed
    (s : ResidualJetSymmetryStatus) : Prop :=
  s.abstractResidualActionsDefined /\
  s.compatibilityWithOrbitDirectionsProved /\
  s.uniqueEquivariantReductionsProved /\
  s.tangentNormalFrameGroupIdentified /\
  s.spinCAndTwistResidualGroupIdentified /\
  s.reducedTensorRepresentationsConstructed /\
  s.compactnessOrReductivityEstablished /\
  s.invariantTheoryApplied

/-- The abstract staged quotient does not supply compactness or reductivity of
the actual residual Janus symmetry. -/
theorem missing_residual_reductivity_blocks_invariant_theory
    (s : ResidualJetSymmetryStatus)
    (hMissing : Not s.compactnessOrReductivityEstablished) :
    Not (residualJetSymmetryClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end P0EFTJanusResidualJetSymmetry
end JanusFormal
