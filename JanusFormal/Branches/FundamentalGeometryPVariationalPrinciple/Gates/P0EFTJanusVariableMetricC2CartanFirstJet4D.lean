import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricDeDonderFirstJet4D

/-! # The completed Cartan first jet in the fixed regular frame

Metric and diffeomorphism-ghost coefficients require only two ordered spatial
derivatives. The nonholonomic bracketCoefficient terms and their derivatives are retained.
No inverse metric or admissibility restriction is needed for this polynomial map.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2CartanFirstJet4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusVariableMetricDeDonderFirstJet4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev MetricC2Core (reference : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod reference

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Four completed scalar coefficients of a diffeomorphism ghost in the fixed frame. -/
abbrev DiffeomorphismGhostC2Coefficients := Fin 4 → C2Scalar period hPeriod

/-- The Cartan tensor value, including the frame-bracket correction in each slot. -/
def variableMetricC2CartanComponentExpression
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : DiffeomorphismGhostC2Coefficients period hPeriod) (first second : Fin 4) :
    C0Scalar period hPeriod :=
  let g := regularGeneralMetricC0MetricCoefficient period hPeriod reference variation
  let dg := regularGeneralMetricC0MetricFirstDerivative period hPeriod reference variation
  let c := fun index => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (ghost index)
  let dc := fun direction index =>
    regularFrameC2FirstDerivative period hPeriod reference direction (ghost index)
  let bracketCoefficient := regularFrameStructureCoefficientContinuous period hPeriod reference
  ∑ index : Fin 4,
    (c index * dg index first second + dc first index * g index second +
      dc second index * g first index -
      (∑ upper : Fin 4,
        (c index * bracketCoefficient index first upper * g upper second +
          c index * bracketCoefficient index second upper * g first upper)))

/-- The explicit ordered first derivative of every factor in the Cartan value. -/
def variableMetricC2CartanComponentFirstDerivative
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : DiffeomorphismGhostC2Coefficients period hPeriod)
    (outer first second : Fin 4) : C0Scalar period hPeriod :=
  let g := regularGeneralMetricC0MetricCoefficient period hPeriod reference variation
  let dg := regularGeneralMetricC0MetricFirstDerivative period hPeriod reference variation
  let ddg := regularGeneralMetricC0MetricSecondDerivative period hPeriod reference variation
  let c := fun index => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (ghost index)
  let dc := fun direction index =>
    regularFrameC2FirstDerivative period hPeriod reference direction (ghost index)
  let ddc := fun outer inner index =>
    regularFrameC2SecondDerivative period hPeriod reference outer inner (ghost index)
  let bracketCoefficient := regularFrameStructureCoefficientContinuous period hPeriod reference
  let dStructure := regularFrameStructureCoefficientDerivativeContinuous period hPeriod reference
  ∑ index : Fin 4,
    ((dc outer index * dg index first second + c index * ddg outer index first second) +
      (ddc outer first index * g index second + dc first index * dg outer index second) +
      (ddc outer second index * g first index + dc second index * dg outer first index) -
      (∑ upper : Fin 4,
        ((dc outer index * bracketCoefficient index first upper * g upper second +
          c index * dStructure outer index first upper * g upper second +
          c index * bracketCoefficient index first upper * dg outer upper second) +
        (dc outer index * bracketCoefficient index second upper * g first upper +
          c index * dStructure outer index second upper * g first upper +
          c index * bracketCoefficient index second upper * dg outer first upper))))

/-- Values and first derivatives, in the slot order accepted by De Donder. -/
def variableMetricC2CartanFirstJet
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : DiffeomorphismGhostC2Coefficients period hPeriod) :
    TensorC0FirstJet period hPeriod :=
  (variableMetricC2CartanComponentExpression period hPeriod reference variation ghost,
    variableMetricC2CartanComponentFirstDerivative period hPeriod reference variation ghost)

/-- Joint global smoothness on the fixed metric and ghost C² spaces. -/
theorem variableMetricC2CartanFirstJet_contDiff
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞
      (fun input : MetricC2Core period hPeriod reference ×
          DiffeomorphismGhostC2Coefficients period hPeriod =>
        variableMetricC2CartanFirstJet period hPeriod reference input.1 input.2) := by
  let Input := MetricC2Core period hPeriod reference ×
    DiffeomorphismGhostC2Coefficients period hPeriod
  have hG (first second : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      regularGeneralMetricC0MetricCoefficient period hPeriod reference input.1 first second) :=
    (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod reference
      first second).comp contDiff_fst
  have hDG (direction first second : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod reference input.1
        direction first second) :=
    (regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod reference
      direction first second).comp contDiff_fst
  have hDDG (outer inner first second : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      regularGeneralMetricC0MetricSecondDerivative period hPeriod reference input.1
        outer inner first second) :=
    (regularGeneralMetricC0MetricSecondDerivative_contDiff period hPeriod reference
      outer inner first second).comp contDiff_fst
  have hGhost (index : Fin 4) : ContDiff Real ∞ (fun input : Input => input.2 index) :=
    (contDiff_apply Real (C2Scalar period hPeriod) index).comp contDiff_snd
  have hC (index : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (input.2 index)) :=
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp (hGhost index)
  have hDC (direction index : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      regularFrameC2FirstDerivative period hPeriod reference direction (input.2 index)) :=
    (regularFrameC2FirstDerivative_contDiff period hPeriod reference direction).comp (hGhost index)
  have hDDC (outer inner index : Fin 4) : ContDiff Real ∞ (fun input : Input =>
      regularFrameC2SecondDerivative period hPeriod reference outer inner (input.2 index)) :=
    (regularFrameC2SecondDerivative_contDiff period hPeriod reference outer inner).comp
      (hGhost index)
  unfold variableMetricC2CartanFirstJet
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro first
    apply contDiff_pi.mpr
    intro second
    dsimp only [variableMetricC2CartanComponentExpression]
    apply ContDiff.sum
    intro index _
    apply ContDiff.sub
    · exact (((hC index).mul (hDG index first second)).add
        ((hDC first index).mul (hG index second))).add
          ((hDC second index).mul (hG first index))
    · apply ContDiff.sum
      intro upper _
      exact (((hC index).mul contDiff_const).mul (hG upper second)).add
        (((hC index).mul contDiff_const).mul (hG first upper))
  · apply contDiff_pi.mpr
    intro outer
    apply contDiff_pi.mpr
    intro first
    apply contDiff_pi.mpr
    intro second
    dsimp only [variableMetricC2CartanComponentFirstDerivative]
    apply ContDiff.sum
    intro index _
    apply ContDiff.sub
    · exact ((((hDC outer index).mul (hDG index first second)).add
        ((hC index).mul (hDDG outer index first second))).add
          (((hDDC outer first index).mul (hG index second)).add
            ((hDC first index).mul (hDG outer index second)))).add
              (((hDDC outer second index).mul (hG first index)).add
                ((hDC second index).mul (hDG outer first index)))
    · apply ContDiff.sum
      intro upper _
      exact (((((hDC outer index).mul contDiff_const).mul (hG upper second)).add
        (((hC index).mul contDiff_const).mul (hG upper second))).add
          (((hC index).mul contDiff_const).mul (hDG outer upper second))).add
            (((((hDC outer index).mul contDiff_const).mul (hG first upper)).add
              (((hC index).mul contDiff_const).mul (hG first upper))).add
                (((hC index).mul contDiff_const).mul (hDG outer first upper)))

end
end P0EFTJanusVariableMetricC2CartanFirstJet4D
end JanusFormal
