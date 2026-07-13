import Mathlib

namespace JanusFormal
namespace P0EFTJanusAbelianConnectionJetNormalForm

set_option autoImplicit false

universe u v w

/-- Algebraic decomposition of a first jet of an abelian connection into its
value, the symmetric part of its first derivative, and its curvature part. -/
@[ext]
structure ConnectionOneJet
    (Value : Type u)
    (SymmetricDerivative : Type v)
    (Curvature : Type w) where
  value : Value
  symmetricDerivative : SymmetricDerivative
  curvature : Curvature

/-- The relevant two-jet of an abelian gauge parameter: its gradient changes
the connection value and its Hessian changes only the symmetric derivative. -/
@[ext]
structure GaugeTwoJet
    (Value : Type u)
    (SymmetricDerivative : Type v) where
  gradient : Value
  hessian : SymmetricDerivative

/-- Gauge action on the decomposed connection one-jet. -/
def gaugeChange
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Add Value]
    [Add SymmetricDerivative]
    (gauge : GaugeTwoJet Value SymmetricDerivative)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    ConnectionOneJet Value SymmetricDerivative Curvature where
  value := jet.value + gauge.gradient
  symmetricDerivative := jet.symmetricDerivative + gauge.hessian
  curvature := jet.curvature

/-- Canonical algebraic gauge slice: connection value and symmetric derivative
are zero, while curvature is retained. -/
def curvatureNormalForm
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Zero Value]
    [Zero SymmetricDerivative]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    ConnectionOneJet Value SymmetricDerivative Curvature where
  value := 0
  symmetricDerivative := 0
  curvature := jet.curvature

/-- Gauge-equivalence relation in the decomposed one-jet model. -/
def GaugeEquivalent
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Add Value]
    [Add SymmetricDerivative]
    (first second : ConnectionOneJet Value SymmetricDerivative Curvature) : Prop :=
  ∃ gauge : GaugeTwoJet Value SymmetricDerivative,
    gaugeChange gauge first = second

/-- The explicit gradient/Hessian choice kills the gauge-removable components. -/
def normalizingGauge
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Neg Value]
    [Neg SymmetricDerivative]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    GaugeTwoJet Value SymmetricDerivative where
  gradient := -jet.value
  hessian := -jet.symmetricDerivative

/-- The chosen two-jet of gauge parameter reaches curvature normal form. -/
theorem chosen_gauge_reaches_curvature_normal_form
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    gaugeChange (normalizingGauge jet) jet =
      curvatureNormalForm jet := by
  ext <;> simp [gaugeChange, normalizingGauge, curvatureNormalForm]

/-- Curvature is unchanged by every abelian gauge two-jet. -/
theorem curvature_is_gauge_invariant
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [Add Value]
    [Add SymmetricDerivative]
    (gauge : GaugeTwoJet Value SymmetricDerivative)
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    (gaugeChange gauge jet).curvature = jet.curvature :=
  rfl

/-- Complete orbit classification of the decomposed abelian connection one-jet:
two jets are gauge-equivalent exactly when their curvature components agree. -/
theorem gauge_equivalent_iff_curvature_eq
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (first second : ConnectionOneJet Value SymmetricDerivative Curvature) :
    GaugeEquivalent first second ↔ first.curvature = second.curvature := by
  constructor
  · rintro ⟨gauge, hGauge⟩
    have hCurvature := congrArg ConnectionOneJet.curvature hGauge
    simpa [gaugeChange] using hCurvature
  · intro hCurvature
    let gauge : GaugeTwoJet Value SymmetricDerivative :=
      { gradient := -first.value + second.value
        hessian := -first.symmetricDerivative + second.symmetricDerivative }
    refine ⟨gauge, ?_⟩
    ext
    · simp [gauge, gaugeChange, add_assoc]
    · simp [gauge, gaugeChange, add_assoc]
    · simpa [gaugeChange] using hCurvature

@[refl]
theorem gauge_equivalent_refl
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    GaugeEquivalent jet jet :=
  (gauge_equivalent_iff_curvature_eq jet jet).2 rfl

@[symm]
theorem gauge_equivalent_symm
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    {first second : ConnectionOneJet Value SymmetricDerivative Curvature}
    (hEquivalent : GaugeEquivalent first second) :
    GaugeEquivalent second first :=
  (gauge_equivalent_iff_curvature_eq second first).2
    ((gauge_equivalent_iff_curvature_eq first second).1 hEquivalent).symm

@[trans]
theorem gauge_equivalent_trans
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    {first second third :
      ConnectionOneJet Value SymmetricDerivative Curvature}
    (hFirst : GaugeEquivalent first second)
    (hSecond : GaugeEquivalent second third) :
    GaugeEquivalent first third :=
  (gauge_equivalent_iff_curvature_eq first third).2
    ((gauge_equivalent_iff_curvature_eq first second).1 hFirst).trans
      ((gauge_equivalent_iff_curvature_eq second third).1 hSecond)

/-- Every gauge orbit meets the curvature-only slice. -/
theorem every_orbit_meets_curvature_slice
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    (jet : ConnectionOneJet Value SymmetricDerivative Curvature) :
    GaugeEquivalent jet (curvatureNormalForm jet) := by
  exact ⟨normalizingGauge jet,
    chosen_gauge_reaches_curvature_normal_form jet⟩

/-- The curvature-only representative of each orbit is unique. -/
theorem curvature_slice_representative_unique
    {Value : Type u}
    {SymmetricDerivative : Type v}
    {Curvature : Type w}
    [AddGroup Value]
    [AddGroup SymmetricDerivative]
    {first second : ConnectionOneJet Value SymmetricDerivative Curvature}
    (hFirstValue : first.value = 0)
    (hSecondValue : second.value = 0)
    (hFirstSymmetric : first.symmetricDerivative = 0)
    (hSecondSymmetric : second.symmetricDerivative = 0)
    (hEquivalent : GaugeEquivalent first second) :
    first = second := by
  apply ConnectionOneJet.ext
  · exact hFirstValue.trans hSecondValue.symm
  · exact hFirstSymmetric.trans hSecondSymmetric.symm
  · exact (gauge_equivalent_iff_curvature_eq first second).1 hEquivalent

/-- Geometric obligations suppressed by the decomposed algebraic model. -/
structure GeometricConnectionJetReductionStatus where
  localConnectionFormConstructed : Prop
  gaugeTwoJetActionComputed : Prop
  derivativeSplitIntoSymmetricAndAlternatingParts : Prop
  algebraicOrbitReductionProved : Prop
  alternatingPartIdentifiedWithCurvature : Prop
  compatibilityWithStructuredJetGroupoidProved : Prop
  globalGaugeBundleDataSeparated : Prop

/-- Closure of the genuine abelian connection one-jet normal-form theorem. -/
def geometricConnectionJetReductionClosed
    (s : GeometricConnectionJetReductionStatus) : Prop :=
  s.localConnectionFormConstructed /\
  s.gaugeTwoJetActionComputed /\
  s.derivativeSplitIntoSymmetricAndAlternatingParts /\
  s.algebraicOrbitReductionProved /\
  s.alternatingPartIdentifiedWithCurvature /\
  s.compatibilityWithStructuredJetGroupoidProved /\
  s.globalGaugeBundleDataSeparated

/-- Identifying the alternating derivative with curvature is an indispensable
geometric step not supplied by the abstract additive orbit theorem. -/
theorem missing_curvature_identification_blocks_geometric_reduction
    (s : GeometricConnectionJetReductionStatus)
    (hMissing : Not s.alternatingPartIdentifiedWithCurvature) :
    Not (geometricConnectionJetReductionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end P0EFTJanusAbelianConnectionJetNormalForm
end JanusFormal
