import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Spectral enumeration, heat trace and zeta regularization

Compact resolvent gives finite-dimensional eigenspaces and spectral
completeness, but an explicit eigenvalue enumeration and its Weyl asymptotics
are additional analytic results.  This file records the exact data needed for
heat-kernel and one-loop constructions.

A positive spectral enumeration supplies:

* the heat trace `sum m_n exp(-t lambda_n)`;
* the real spectral zeta series `sum m_n lambda_n^{-s}`;
* a regularized value and derivative at zero;
* the zeta-regularized determinant `exp(-zeta'(0))`.

No asymptotic or analytic-continuation theorem is postulated globally; each is a
field of the corresponding interface.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianSpectralZeta4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter Module
open scoped Topology BigOperators ENNReal
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Enumeration of the positive discrete spectrum of one analytic closure
package.  Repeated eigenvalues are represented by explicit multiplicities. -/
structure CanonicalScalarPositiveSpectrumEnumeration
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition) where
  eigenvalue : Nat → Real
  multiplicity : Nat → Nat
  positive : ∀ index, 0 < eigenvalue index
  multiplicity_pos : ∀ index, 0 < multiplicity index
  monotone : Monotone eigenvalue
  tendsto_atTop : Tendsto eigenvalue atTop atTop
  realized : ∀ index,
    CanonicalScalarClosedLagrangianHasEigenvalue
      data hClosable traceBound condition (eigenvalue index)
  exhaustive : ∀ spectralParameter : Real,
    CanonicalScalarClosedLagrangianHasEigenvalue
        data hClosable traceBound condition spectralParameter →
      ∃ index, eigenvalue index = spectralParameter
  multiplicity_matches : ∀ index,
    Module.finrank Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition (eigenvalue index)) =
      multiplicity index

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {hClosable : CanonicalScalarGraphClosable data}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}
  {closureData : CanonicalScalarLagrangianAnalyticClosureData
    data hClosable traceBound condition}

namespace CanonicalScalarPositiveSpectrumEnumeration

/-- One heat-trace term. -/
def heatTraceTerm
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (time : Real) (index : Nat) : Real :=
  enumeration.multiplicity index *
    Real.exp (-time * enumeration.eigenvalue index)

/-- Heat trace as a possibly divergent `tsum`; convergence is a separate
property below. -/
def heatTrace
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (time : Real) : Real :=
  ∑' index, enumeration.heatTraceTerm time index

/-- Heat-trace summability at a time. -/
def HeatTraceSummable
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (time : Real) : Prop :=
  Summable (enumeration.heatTraceTerm time)

/-- One real spectral-zeta term. -/
def spectralZetaTerm
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (exponent : Real) (index : Nat) : Real :=
  enumeration.multiplicity index *
    (enumeration.eigenvalue index) ^ (-exponent)

/-- Real spectral-zeta series. -/
def spectralZeta
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (exponent : Real) : Real :=
  ∑' index, enumeration.spectralZetaTerm exponent index

/-- Spectral-zeta summability at one real exponent. -/
def SpectralZetaSummable
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (exponent : Real) : Prop :=
  Summable (enumeration.spectralZetaTerm exponent)

/-- Every heat-trace term is nonnegative at nonnegative time. -/
theorem heatTraceTerm_nonnegative
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (time : Real) (hTime : 0 ≤ time) (index : Nat) :
    0 ≤ enumeration.heatTraceTerm time index := by
  unfold heatTraceTerm
  positivity

/-- Every zeta term is positive. -/
theorem spectralZetaTerm_positive
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (exponent : Real) (index : Nat) :
    0 < enumeration.spectralZetaTerm exponent index := by
  unfold spectralZetaTerm
  have hMultiplicity : 0 < (enumeration.multiplicity index : Real) := by
    exact_mod_cast enumeration.multiplicity_pos index
  exact mul_pos hMultiplicity
    (Real.rpow_pos_of_pos (enumeration.positive index) _)

/-- Heat trace is nonnegative whenever the series is summable. -/
theorem heatTrace_nonnegative
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (time : Real) (hTime : 0 ≤ time) :
    0 ≤ enumeration.heatTrace time := by
  unfold heatTrace
  exact tsum_nonneg fun index => enumeration.heatTraceTerm_nonnegative
    time hTime index

/-- Spectral zeta is nonnegative. -/
theorem spectralZeta_nonnegative
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData)
    (exponent : Real) :
    0 ≤ enumeration.spectralZeta exponent := by
  unfold spectralZeta
  exact tsum_nonneg fun index =>
    (enumeration.spectralZetaTerm_positive exponent index).le

end CanonicalScalarPositiveSpectrumEnumeration

/-- Weyl-type quantitative input ensuring heat/zeta convergence in a right
half-line. -/
structure CanonicalScalarSpectralGrowthData
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData) where
  dimensionExponent : Real
  dimensionExponent_pos : 0 < dimensionExponent
  heat_summable : ∀ time : Real, 0 < time →
    enumeration.HeatTraceSummable time
  zeta_summable : ∀ exponent : Real,
    dimensionExponent < exponent →
      enumeration.SpectralZetaSummable exponent
  countingConstant : Real
  countingConstant_nonnegative : 0 ≤ countingConstant
  counting_bound : ∀ cutoff : Real, 0 ≤ cutoff →
    (Finset.filter
      (fun index : Finset.range (Nat.ceil (cutoff + 1)) =>
        enumeration.eigenvalue index.1 ≤ cutoff)
      (Finset.univ)).card ≤
      Nat.ceil (countingConstant * (1 + cutoff) ^ dimensionExponent)

/-- Regular continuation of the zeta series to the origin. -/
structure CanonicalScalarSpectralZetaRegularizationData
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData) where
  regularizedZeta : Real → Real
  agreesOn : Set Real
  agreesOn_nonempty : agreesOn.Nonempty
  agrees : ∀ exponent ∈ agreesOn,
    regularizedZeta exponent = enumeration.spectralZeta exponent
  differentiableAtZero : DifferentiableAt Real regularizedZeta 0

variable {enumeration : CanonicalScalarPositiveSpectrumEnumeration
  data hClosable traceBound condition closureData}

namespace CanonicalScalarSpectralZetaRegularizationData

/-- Zeta value at zero. -/
def zetaZero
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) : Real :=
  regularization.regularizedZeta 0

/-- Zeta derivative at zero. -/
noncomputable def zetaPrimeZero
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) : Real :=
  deriv regularization.regularizedZeta 0

/-- Zeta-regularized determinant. -/
noncomputable def zetaDeterminant
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) : Real :=
  Real.exp (-regularization.zetaPrimeZero)

/-- Zeta-regularized one-loop action. -/
noncomputable def zetaOneLoop
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) : Real :=
  (1 / 2 : Real) * Real.log regularization.zetaDeterminant

/-- The zeta determinant is strictly positive. -/
theorem zetaDeterminant_pos
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) :
    0 < regularization.zetaDeterminant :=
  Real.exp_pos _

/-- The logarithm of the zeta determinant is minus the zeta derivative. -/
theorem log_zetaDeterminant
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) :
    Real.log regularization.zetaDeterminant =
      -regularization.zetaPrimeZero := by
  unfold zetaDeterminant
  rw [Real.log_exp]

/-- One-loop action equals minus half the zeta derivative. -/
theorem zetaOneLoop_eq
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) :
    regularization.zetaOneLoop =
      -(1 / 2 : Real) * regularization.zetaPrimeZero := by
  unfold zetaOneLoop
  rw [regularization.log_zetaDeterminant]
  ring

/-- Zeta-regularization certificate. -/
theorem certificate
    (regularization : CanonicalScalarSpectralZetaRegularizationData
      enumeration) :
    0 < regularization.zetaDeterminant ∧
      Real.log regularization.zetaDeterminant =
        -regularization.zetaPrimeZero ∧
      regularization.zetaOneLoop =
        -(1 / 2 : Real) * regularization.zetaPrimeZero :=
  ⟨regularization.zetaDeterminant_pos,
    regularization.log_zetaDeterminant,
    regularization.zetaOneLoop_eq⟩

end CanonicalScalarSpectralZetaRegularizationData

/-- Full spectral-zeta interface. -/
structure CanonicalScalarSpectralZetaPackage
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition) where
  enumeration : CanonicalScalarPositiveSpectrumEnumeration
    data hClosable traceBound condition closureData
  growth : CanonicalScalarSpectralGrowthData enumeration
  regularization : CanonicalScalarSpectralZetaRegularizationData enumeration

/-- Full zeta-package certificate. -/
theorem canonicalScalarLagrangianSpectralZeta_certificate
    (package : CanonicalScalarSpectralZetaPackage
      data hClosable traceBound condition closureData) :
    (∀ time : Real, 0 < time →
      package.enumeration.HeatTraceSummable time) ∧
      (∀ exponent : Real,
        package.growth.dimensionExponent < exponent →
          package.enumeration.SpectralZetaSummable exponent) ∧
      0 < package.regularization.zetaDeterminant ∧
      package.regularization.zetaOneLoop =
        -(1 / 2 : Real) * package.regularization.zetaPrimeZero :=
  ⟨package.growth.heat_summable,
    package.growth.zeta_summable,
    package.regularization.zetaDeterminant_pos,
    package.regularization.zetaOneLoop_eq⟩

end
end P0EFTJanusMappingTorusScalarLagrangianSpectralZeta4D
end JanusFormal
