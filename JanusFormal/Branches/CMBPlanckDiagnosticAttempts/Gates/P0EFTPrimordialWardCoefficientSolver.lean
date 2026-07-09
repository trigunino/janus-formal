namespace JanusFormal
namespace P0EFTPrimordialWardCoefficientSolver

set_option autoImplicit false

structure PrimordialWardCoefficients where
  cSound : Int
  cOpacity : Int
  cGeff : Int
  cImmirzi : Int
  theta : Int

def wardClosed (c : PrimordialWardCoefficients) : Prop :=
  c.cSound = c.theta /\
  c.cOpacity = -c.theta /\
  c.cGeff = -2 * c.theta /\
  c.cImmirzi = -2 * c.theta

def amplitudeFixed (c : PrimordialWardCoefficients) : Prop :=
  c.theta ≠ 0

def noFitWardReady (c : PrimordialWardCoefficients) : Prop :=
  wardClosed c /\
  amplitudeFixed c

theorem ward_solution_family
    (c : PrimordialWardCoefficients)
    (hSound : c.cSound = c.theta)
    (hOpacity : c.cOpacity = -c.theta)
    (hGeff : c.cGeff = -2 * c.theta)
    (hImmirzi : c.cImmirzi = -2 * c.theta) :
    wardClosed c := by
  exact And.intro hSound (And.intro hOpacity (And.intro hGeff hImmirzi))

theorem unfixed_amplitude_blocks_no_fit
    (c : PrimordialWardCoefficients)
    (_hWard : wardClosed c)
    (hMissing : Not (amplitudeFixed c)) :
    Not (noFitWardReady c) := by
  intro h
  exact hMissing h.right

end P0EFTPrimordialWardCoefficientSolver
end JanusFormal
