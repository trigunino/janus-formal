import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D

/-!
# Mass-independent first-order SpinC graph-core density

The finite-core closure introduced previously was stated for the full smooth
Hessian `2D + m²`, and therefore carried the Candidate-A matter mass through
every terminal interface.  The unbounded part is actually the single
first-order geometric Dirac operator.  Once a finite signed-mode exhaustion
converges for both `ψ` and `Dψ`, convergence for `2Dψ + m²ψ` follows from a
fixed bounded linear combination.

This gate isolates that mass-independent statement and constructs the previous
mass-dependent graph-core datum for every real mass.  No spectral coefficient,
action, boundary condition or D10 direction is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter Set Topology
open scoped BigOperators ENNReal lp LinearPMap InnerProductSpace
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OneSectorSmooth :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev FiniteCoefficients :=
  PrimitiveSpinCGeometricSignedFiniteCoefficients
private abbrev OneSectorL2 :=
  D9PrimitiveSpinCGeometricL2Completion period hPeriod .positiveQuarter

/-- The genuinely mass-independent analytic statement: the exact finite
signed Fourier packets are a core for the first-order geometric Dirac graph. -/
structure ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D :
    Prop where
  approximate : ∀ field : OneSectorSmooth period hPeriod,
    ∃ sequence : ℕ → FiniteCoefficients,
      Tendsto
          (fun index =>
            d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                period hPeriod (sequence index)))
          atTop
          (𝓝 (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter field)) ∧
        Tendsto
          (fun index =>
            d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
                (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                  period hPeriod (sequence index))))
          atTop
          (𝓝 (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
              field)))

/-- Bounded linear combination sending `(Dψ, ψ)` to `2Dψ + m²ψ` in geometric
`L²`. -/
private def actionHessianFromDiracPairCLM
    (massSquared : Real) :
    (OneSectorL2 period hPeriod × OneSectorL2 period hPeriod) →L[Complex]
      OneSectorL2 period hPeriod :=
  (2 : Complex) •
      ContinuousLinearMap.fst Complex
        (OneSectorL2 period hPeriod) (OneSectorL2 period hPeriod) +
    (massSquared : Complex) •
      ContinuousLinearMap.snd Complex
        (OneSectorL2 period hPeriod) (OneSectorL2 period hPeriod)

private theorem actionHessianFromDiracPairCLM_embedding
    (massSquared : Real) (field : OneSectorSmooth period hPeriod) :
    actionHessianFromDiracPairCLM period hPeriod massSquared
        (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod field),
          d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter field) =
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field) := by
  change
    (2 : Complex) •
          d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod field) +
        (massSquared : Complex) •
          d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter field =
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field)
  unfold primitiveSpinCGeometricSignedActionHessianSmoothCore
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_smul, map_smul]

/-- First-order graph-core density constructs the former mass-dependent
`2D + m²` graph-core datum for every real mass. -/
def programPPrimitiveSpinCSmoothDiracGraphCoreDensityData_of_firstOrder
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D
      period hPeriod) :
    ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period hPeriod
      massSquared where
  approximate := by
    intro field
    obtain ⟨sequence, hField, hDirac⟩ := density.approximate field
    refine ⟨sequence, hField, ?_⟩
    have hPair :
        Tendsto
          (fun index =>
            (d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
                  (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                    period hPeriod (sequence index))),
              d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                  period hPeriod (sequence index))))
          atTop
          (𝓝
            (d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
                  field),
              d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter field)) :=
      hDirac.prodMk_nhds hField
    have hMapped :=
      (actionHessianFromDiracPairCLM period hPeriod massSquared).continuous
        |>.tendsto.comp hPair
    have hSequence :
        (fun index =>
          actionHessianFromDiracPairCLM period hPeriod massSquared
            (d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
                  (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                    period hPeriod (sequence index))),
              d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                  period hPeriod (sequence index)))) =
          (fun index =>
            d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricSignedActionHessianSmoothCore
                period hPeriod massSquared
                (primitiveSpinCGeometricSignedDiracFiniteSynthesis
                  period hPeriod (sequence index)))) := by
      funext index
      exact actionHessianFromDiracPairCLM_embedding period hPeriod massSquared
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod (sequence index))
    have hLimit :=
      actionHessianFromDiracPairCLM_embedding period hPeriod massSquared field
    rw [hSequence, hLimit] at hMapped
    exact hMapped

/-- The existing finite Green and closure gates may therefore be consumed from
one mass-independent first-order density theorem. -/
def programPPrimitiveSpinCSmoothDiracGreenData_of_firstOrderGraphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D
      period hPeriod) :=
  programPPrimitiveSpinCSmoothDiracGreenData_of_graphCoreDensity period hPeriod
    massSquared
      (programPPrimitiveSpinCSmoothDiracGraphCoreDensityData_of_firstOrder
        period hPeriod massSquared density)

/-- Maximal-domain membership and exact smooth-operator restriction for every
mass are derived from the first-order core theorem. -/
def programPPrimitiveSpinCSmoothMaximalDomainData_of_firstOrderGraphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D
      period hPeriod) :=
  programPPrimitiveSpinCSmoothMaximalDomainData_of_graphCoreDensity period
    hPeriod massSquared
      (programPPrimitiveSpinCSmoothDiracGraphCoreDensityData_of_firstOrder
        period hPeriod massSquared density)

/-- Exact same-action smooth matter graph realization for every mass. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_firstOrderGraphCoreDensity
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D
      period hPeriod) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_graphCoreDensity period
    hPeriod massSquared
      (programPPrimitiveSpinCSmoothDiracGraphCoreDensityData_of_firstOrder
        period hPeriod massSquared density)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D
end JanusFormal
