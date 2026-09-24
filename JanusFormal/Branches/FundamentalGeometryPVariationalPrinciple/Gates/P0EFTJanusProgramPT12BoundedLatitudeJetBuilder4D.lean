import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJet2SubstitutionC2

/-! A reusable bounded raw second-jet construction from compact latitude data.
Derivative compatibility is transported from a dense image by the proved closed graph theorem. -/
namespace JanusFormal.P0EFTJanusProgramPT12BoundedLatitudeJetBuilder4D
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusBoundedFiberJet2SubstitutionC2
variable (X : Type*) [MetricSpace X] [CompactSpace X]
local instance : NormedAddCommGroup (Jet2 X) := (jet2Submodule X).normedAddCommGroup
local instance : NormedSpace Real (Jet2 X) := Submodule.normedSpace (jet2Submodule X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
abbrev LatitudeTriple := Fin 3 → C(X × ArctanCompactFiber, Real)
variable (latitude : E →L[Real] LatitudeTriple X)

def latitudeRawComponent (index : Fin 3) : E →L[Real] P0EFTJanusBoundedFiberJet2SubstitutionC2.Field X :=
  (boundedArctanCompactPullbackCLM X).comp ((ContinuousLinearMap.proj index).comp latitude)

def boundedLatitudeRawAmbient : E →L[Real] Ambient X :=
  ContinuousLinearMap.pi ![
    latitudeRawComponent X latitude 0,
    (ContinuousLinearMap.mul Real (P0EFTJanusBoundedFiberJet2SubstitutionC2.Field X) ((boundedFiberArctanJet3 X).1 1)).comp
      (latitudeRawComponent X latitude 1),
    (ContinuousLinearMap.mul Real (P0EFTJanusBoundedFiberJet2SubstitutionC2.Field X) (((boundedFiberArctanJet3 X).1 1) ^ 2)).comp
      (latitudeRawComponent X latitude 2) +
    (ContinuousLinearMap.mul Real (P0EFTJanusBoundedFiberJet2SubstitutionC2.Field X) ((boundedFiberArctanJet3 X).1 2)).comp
      (latitudeRawComponent X latitude 1)]

/-- Only the already computed derivatives of a smooth scalar representative enter this bridge. -/
theorem boundedLatitudeRawAmbient_of_derivatives
    (x : E) (value first second : X → Real → Real)
    (hValue : ∀ point (angle : ArctanCompactFiber), latitude x 0 (point, angle) = value point angle)
    (hFirst : ∀ point (angle : ArctanCompactFiber), latitude x 1 (point, angle) = first point angle)
    (hSecond : ∀ point (angle : ArctanCompactFiber), latitude x 2 (point, angle) = second point angle)
    (hD0 : ∀ point angle, HasDerivAt (value point) (first point angle) angle)
    (hD1 : ∀ point angle, HasDerivAt (first point) (second point angle) angle) :
    boundedLatitudeRawAmbient X latitude x ∈ jet2DerivativeSubmodule X := by
  have hRaw (index : Fin 3) (point : X) (fiber : Real) :
      latitudeRawComponent X latitude index x (point, fiber) =
        latitude x index (point, arctanCompactFiberMap fiber) := rfl
  refine ⟨?_, ?_⟩
  · intro point fiber
    change HasDerivAt (fun varied => latitudeRawComponent X latitude 0 x (point, varied))
      ((boundedFiberArctanJet3 X).1 1 (point, fiber) *
        latitudeRawComponent X latitude 1 x (point, fiber)) fiber
    have h := (hD0 point (Real.arctan fiber)).comp fiber
      ((boundedFiberArctanJet3 X).2.1 point fiber)
    apply (h.congr_of_eventuallyEq ?_).congr_deriv
    · rw [hRaw, hFirst]
      simp only [arctanCompactFiberMap, ContinuousMap.coe_mk, Subtype.coe_mk]
      ring
    · filter_upwards [] with varied
      rw [hRaw, hValue]
      rfl
  · intro point fiber
    change HasDerivAt (fun varied => (boundedFiberArctanJet3 X).1 1 (point, varied) *
      latitudeRawComponent X latitude 1 x (point, varied))
      (((boundedFiberArctanJet3 X).1 1 (point, fiber)) ^ 2 *
        latitudeRawComponent X latitude 2 x (point, fiber) +
      (boundedFiberArctanJet3 X).1 2 (point, fiber) *
        latitudeRawComponent X latitude 1 x (point, fiber)) fiber
    have h := ((boundedFiberArctanJet3 X).2.2.1 point fiber).mul
      ((hD1 point (Real.arctan fiber)).comp fiber ((boundedFiberArctanJet3 X).2.1 point fiber))
    apply (h.congr_of_eventuallyEq ?_).congr_deriv
    · rw [hRaw, hRaw, hFirst, hSecond]
      simp only [Function.comp_apply, arctanCompactFiberMap, ContinuousMap.coe_mk, Subtype.coe_mk]
      ring
    · filter_upwards [] with varied
      rw [hRaw, hFirst]
      rfl

theorem boundedLatitudeRawAmbient_mem_of_dense {D : Type*}
    (inclusion : D → E) (hDense : DenseRange inclusion)
    (hSmooth : ∀ d, boundedLatitudeRawAmbient X latitude (inclusion d) ∈ jet2DerivativeSubmodule X)
    (x : E) : boundedLatitudeRawAmbient X latitude x ∈ jet2DerivativeSubmodule X := by
  have hClosed : IsClosed ((boundedLatitudeRawAmbient X latitude) ⁻¹'
      (jet2DerivativeSubmodule X : Set (Ambient X))) :=
    (jet2DerivativeSubmodule_isClosed X).preimage (boundedLatitudeRawAmbient X latitude).continuous
  have hRange : Set.range inclusion ⊆ (boundedLatitudeRawAmbient X latitude) ⁻¹'
      (jet2DerivativeSubmodule X : Set (Ambient X)) := by
    rintro _ ⟨d, rfl⟩
    exact hSmooth d
  exact closure_minimal hRange hClosed (hDense x)

theorem boundedLatitudeRawAmbient_top_uniformContinuous (x : E) :
    UniformContinuous (boundedLatitudeRawAmbient X latitude x 2) := by
  have hA1 : UniformContinuous ((boundedFiberArctanJet3 X).1 1) := by
    simpa using boundedFiberArctanJet3_component_uniformContinuous X (1 : Fin 3)
  have hA2 : UniformContinuous ((boundedFiberArctanJet3 X).1 2) := by
    simpa using boundedFiberArctanJet3_component_uniformContinuous X (2 : Fin 3)
  have hL1 : UniformContinuous (latitudeRawComponent X latitude 1 x) :=
    boundedArctanCompactPullback_uniformContinuous X (latitude x 1)
  have hL2 : UniformContinuous (latitudeRawComponent X latitude 2 x) :=
    boundedArctanCompactPullback_uniformContinuous X (latitude x 2)
  have hSquare := field_mul_uniformContinuous X
    ((boundedFiberArctanJet3 X).1 1) ((boundedFiberArctanJet3 X).1 1) hA1 hA1
  have hTerm1 := field_mul_uniformContinuous X
    (((boundedFiberArctanJet3 X).1 1) * ((boundedFiberArctanJet3 X).1 1))
    (latitudeRawComponent X latitude 2 x) hSquare hL2
  have hTerm2 := field_mul_uniformContinuous X
    ((boundedFiberArctanJet3 X).1 2) (latitudeRawComponent X latitude 1 x) hA2 hL1
  change UniformContinuous (fun point =>
    ((boundedFiberArctanJet3 X).1 1 point) ^ 2 * latitudeRawComponent X latitude 2 x point +
    (boundedFiberArctanJet3 X).1 2 point * latitudeRawComponent X latitude 1 x point)
  simpa [pow_two] using hTerm1.add hTerm2

variable (hDerivative : ∀ x, boundedLatitudeRawAmbient X latitude x ∈ jet2DerivativeSubmodule X)

def boundedLatitudeRawJet2 : E →L[Real] Jet2 X :=
  (boundedLatitudeRawAmbient X latitude).codRestrict (jet2Submodule X) (fun x =>
    ⟨(hDerivative x).1, (hDerivative x).2, boundedLatitudeRawAmbient_top_uniformContinuous X latitude x⟩)

def boundedLatitudeEvaluation (current : E × BoundedContinuousFunction X Real) :
    BoundedContinuousFunction X Real :=
  evaluation X (boundedLatitudeRawJet2 X latitude hDerivative current.1, current.2)

theorem boundedLatitudeEvaluation_contDiff_two :
    ContDiff Real 2 (boundedLatitudeEvaluation X latitude hDerivative) :=
  (evaluation_contDiff_two X).comp
    (((boundedLatitudeRawJet2 X latitude hDerivative).contDiff.comp contDiff_fst).prodMk contDiff_snd)

@[simp] theorem boundedLatitudeEvaluation_apply
    (x : E) (graph : BoundedContinuousFunction X Real) (point : X) :
    boundedLatitudeEvaluation X latitude hDerivative (x, graph) point =
      latitude x 0 (point, arctanCompactFiberMap (graph point)) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12BoundedLatitudeJetBuilder4D
