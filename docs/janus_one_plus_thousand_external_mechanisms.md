# External mechanisms for `1 + 1000`

Status: archived exploratory audit; not promoted into program P and not used
as an input or target dimension.

## Permutation mechanism

For 1001 equivalent components, the permutation representation splits
canonically into the uniform line and the zero-sum subspace:

`R^1001 = <(1,...,1)> + {x | sum x_i = 0}`.

The dimensions are `1 + 1000`.  This needs no M31 quadratic form.  It does,
however, require a physically derived set of exactly 1001 exchangeable states.
The Lean audit constructs both projectors and proves exact reconstruction and
zero total relative amplitude.

A common scalar evolution, of the kind presently available from a shared
clock/lapse in program P, preserves both sectors.  It does not resolve or order
the 1000 relative modes: an additional non-scalar transfer operator is needed.

## Trace mechanism

If the eleven-dimensional module carries an invariant nondegenerate quadratic
form, rank-four symmetric tensors admit the harmonic/trace split with dimensions
`935 + 65 + 1 = 1001`.  This is mathematically standard, but the full affine M31
coadjoint action has not supplied the required invariant pairing.

## Comparison

The permutation route is structurally closer to program P because its unique
uniform mode can carry a common clock.  Its missing input is the physical origin
and exchange symmetry of the 1001 states.  The trace route derives 1001 from
eleven dimensions, but its missing input is M31-invariant orthogonality.

Neither route currently derives a physical `1 + 1000` prediction.

## Dimension-free restart from P

The current dust-FLRW branch has a one-dimensional constrained tangent and an
exact nonlinear constraint curve.  The reduced equal-lapse Hamiltonian is zero
all along that curve, as are its first and second constrained variations.  The
nonzero ambient Hessian measures departure from the constraint surface and is
not a physical spectral operator.

Therefore current P selects neither 1001 nor any other finite level count.  A
nontrivial spectrum requires additional reduced degrees of freedom (for example
inhomogeneous perturbations or matter modes) and their derived quadratic
Hamiltonian.  This is now the dimension-free next gate; `1001` must not be fed
back into it.

The newer reduced quadratic P gate already supplies the algebraic seed: for
each independently supplied field-mode label, equal sheet kinetics split into
one diagonal/common channel and one relative channel.  The interaction leaves
the common channel massless and shifts the relative channel by `2 m_rel`.
This is a genuine modewise `1 + 1`, not a global `1 + 1000`.  The number and
dispersion of field modes still require a spatial differential operator,
boundary conditions and constraint reduction; none is selected by the current
finite two-amplitude Hessian.

An isolated spectral lift now diagonalizes an arbitrary supplied spatial
operator.  If its eigenvalue is `lambda_k`, P's quadratic interaction gives

`omega_common(k)^2 = lambda_k`,

`omega_relative(k)^2 = lambda_k + 2 m_rel`.

Thus P fixes the constant squared-frequency gap `2 m_rel` between the two
channels and preserves positivity when `lambda_k,m_rel >= 0`.  It still does
not derive `lambda_k`, its boundary conditions, or the cardinality of the
index set.  Those require the second variation of the covariant derivative
terms plus full constraint reduction.
