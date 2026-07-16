import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusQuotient

/-!
# Time reversal on an involutive mapping torus

For self-inverse monodromy, reversal of the cover coordinate sends the deck
iterate `n` to `-n`.  It therefore descends to a continuous involution on the
actual orbit quotient.  The construction is specialized below to both the
reflected three-sphere mapping torus and its fixed throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTInvolution

set_option autoImplicit false

open P0EFTJanusMappingTorusQuotient

variable {X : Type*} [TopologicalSpace X]

/-- Reversal of the real cover coordinate. -/
def timeReverseCover (data : MappingTorusData X) :
    MappingTorusCover data → MappingTorusCover data :=
  fun point ↦ ⟨point.fiber, -point.time⟩

@[simp] theorem timeReverseCover_fiber (data : MappingTorusData X)
    (point : MappingTorusCover data) :
    (timeReverseCover data point).fiber = point.fiber := rfl

@[simp] theorem timeReverseCover_time (data : MappingTorusData X)
    (point : MappingTorusCover data) :
    (timeReverseCover data point).time = -point.time := rfl

@[simp] theorem timeReverseCover_involutive (data : MappingTorusData X)
    (point : MappingTorusCover data) :
    timeReverseCover data (timeReverseCover data point) = point := by
  apply MappingTorusCover.ext
  · rfl
  · simp [timeReverseCover]

theorem continuous_timeReverseCover (data : MappingTorusData X) :
    Continuous (timeReverseCover data) := by
  have hFiber := continuous_fiber data
  have hTime := (continuous_time data).neg
  exact ((coverHomeomorphProd data).symm.continuous.comp
    (hFiber.prodMk hTime)).congr fun _ ↦ rfl

private theorem zpow_neg_eq_of_symm_eq
    (monodromy : X ≃ₜ X) (hSymm : monodromy.symm = monodromy)
    (winding : ℤ) :
    monodromy ^ (-winding) = monodromy ^ winding := by
  calc
    monodromy ^ (-winding) = (monodromy ^ winding)⁻¹ := by
      exact zpow_neg monodromy winding
    _ = (monodromy⁻¹) ^ winding := by
      rw [inv_zpow]
    _ = monodromy ^ winding := by
      rw [show monodromy⁻¹ = monodromy from hSymm]

/-- Time reversal descends precisely when the monodromy is self-inverse. -/
def mappingTorusTimeReversal
    (data : MappingTorusData X) (hSymm : data.monodromy.symm = data.monodromy) :
    MappingTorus data → MappingTorus data :=
  Quotient.map (timeReverseCover data) fun first second hOrbit ↦ by
    change AddAction.orbitRel ℤ (MappingTorusCover data) first second at hOrbit
    change AddAction.orbitRel ℤ (MappingTorusCover data)
      (timeReverseCover data first) (timeReverseCover data second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨-winding, ?_⟩
    apply MappingTorusCover.ext
    · change (data.monodromy ^ (-winding)) second.fiber = first.fiber
      rw [zpow_neg_eq_of_symm_eq data.monodromy hSymm winding]
      exact congrArg MappingTorusCover.fiber hWinding
    · have hTime := congrArg MappingTorusCover.time hWinding
      change second.time + (winding : ℝ) * data.period = first.time at hTime
      change -second.time + ((-winding : ℤ) : ℝ) * data.period = -first.time
      push_cast
      linarith

@[simp] theorem mappingTorusTimeReversal_mk
    (data : MappingTorusData X) (hSymm : data.monodromy.symm = data.monodromy)
    (point : MappingTorusCover data) :
    mappingTorusTimeReversal data hSymm (mappingTorusMk data point) =
      mappingTorusMk data (timeReverseCover data point) := rfl

theorem continuous_mappingTorusTimeReversal
    (data : MappingTorusData X) (hSymm : data.monodromy.symm = data.monodromy) :
    Continuous (mappingTorusTimeReversal data hSymm) := by
  apply (continuous_quotient_mk'.comp (continuous_timeReverseCover data)).quotient_lift

@[simp] theorem mappingTorusTimeReversal_involutive
    (data : MappingTorusData X) (hSymm : data.monodromy.symm = data.monodromy)
    (point : MappingTorus data) :
    mappingTorusTimeReversal data hSymm
        (mappingTorusTimeReversal data hSymm point) = point := by
  refine Quotient.inductionOn point ?_
  intro representative
  change mappingTorusMk data
      (timeReverseCover data (timeReverseCover data representative)) =
    mappingTorusMk data representative
  rw [timeReverseCover_involutive]

section ReflectedSphere

theorem sphereReflection_symm : sphereReflection.symm = sphereReflection := by
  apply Homeomorph.ext
  intro point
  rfl

/-- Continuous PT/time-reversal involution on the effective reflected-sphere
mapping torus. -/
def reflectedSpherePT (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorus (reflectedSphereData period hPeriod) →
      MappingTorus (reflectedSphereData period hPeriod) :=
  mappingTorusTimeReversal (reflectedSphereData period hPeriod)
    sphereReflection_symm

theorem continuous_reflectedSpherePT (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (reflectedSpherePT period hPeriod) :=
  continuous_mappingTorusTimeReversal _ sphereReflection_symm

@[simp] theorem reflectedSpherePT_involutive
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    reflectedSpherePT period hPeriod (reflectedSpherePT period hPeriod point) = point :=
  mappingTorusTimeReversal_involutive _ sphereReflection_symm point

theorem fixedEquatorMonodromy_symm (period : ℝ) (hPeriod : period ≠ 0) :
    (fixedEquatorData period hPeriod).monodromy.symm =
      (fixedEquatorData period hPeriod).monodromy := by
  rfl

/-- Continuous PT/time-reversal involution on the same effective throat used
by the quotient inclusion and associated normal line. -/
def fixedThroatPT (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorus (fixedEquatorData period hPeriod) →
      MappingTorus (fixedEquatorData period hPeriod) :=
  mappingTorusTimeReversal (fixedEquatorData period hPeriod)
    (fixedEquatorMonodromy_symm period hPeriod)

theorem continuous_fixedThroatPT (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (fixedThroatPT period hPeriod) :=
  continuous_mappingTorusTimeReversal _
    (fixedEquatorMonodromy_symm period hPeriod)

@[simp] theorem fixedThroatPT_involutive
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    fixedThroatPT period hPeriod (fixedThroatPT period hPeriod point) = point :=
  mappingTorusTimeReversal_involutive _
    (fixedEquatorMonodromy_symm period hPeriod) point

/-- The throat inclusion intertwines the two quotient PT involutions. -/
theorem fixedThroatQuotientInclusion_pt_equivariant
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    fixedThroatQuotientInclusion period hPeriod
        (fixedThroatPT period hPeriod point) =
      reflectedSpherePT period hPeriod
        (fixedThroatQuotientInclusion period hPeriod point) := by
  refine Quotient.inductionOn point ?_
  intro representative
  rfl

end ReflectedSphere

end P0EFTJanusMappingTorusPTInvolution
end JanusFormal
