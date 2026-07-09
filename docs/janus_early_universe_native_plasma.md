# Janus Early-Universe Native Plasma

This branch is the first explicit extension beyond the paper-native late-time
SN/background layer.

It uses `X2026-variable-constants` Eq. 40 as the early-universe gauge input and
connects it to the active Z2/Sigma BAO/plasma machinery.

## What Eq40 closes

With:

```text
c ~ a^-1/2
h ~ a^3/2
e ~ a^1/2
m ~ a
G ~ a^-1
mu0 ~ a
length ~ a
time ~ a^3/2
```

the branch derives:

- fine-structure constant invariant;
- rest energy `m c^2` invariant;
- hydrogen ionization scale invariant;
- Compton length scales as `a`;
- Thomson cross-section scales as `a^2`.

## What remains open

This still does not derive:

- active baryon number or `rho_b0^J`;
- active photon temperature/occupation law;
- active ionization history;
- pre-drag two-sector `H_J(a)`;
- redshift map valid from today to `z_d^J`.

## New physical fork

The Eq40-native comoving photon law gives:

```text
rho_gamma ~ a^-3
rho_b,energy ~ a^-3
blackbody n_gamma ~ a^-3
Gamma_drag/H ~ constant before ionization physics
```

So Eq40 alone does not naturally select a drag epoch.

A thermodynamic cooling law gives:

```text
rho_gamma ~ a^-4
rho_b,energy ~ a^-3
blackbody n_gamma ~ a^-6
Gamma_drag/H evolves
```

That can support an evolving drag ratio, but it conflicts with conserved photon
number unless Janus also derives a photon entropy/phase-space production law.

The minimal compensating law is:

```text
phase-space occupation / entropy factor ~ a^3
```

With that extra derived law, one can have both:

- `T_energy ~ a^-1`;
- conserved blackbody photon number `n_gamma ~ a^-3`.

This is the current best concrete target for the next derivation.

## Occupation search

The phase-space occupation search tests several mechanisms against the required
`a^3` factor.

Rejected or insufficient:

- constant `Z2` sheet multiplicity;
- fixed `RP3/Sigma` topology;
- pure Sigma area modes;
- naive `h^3` quantum-cell deformation;
- Compton-cutoff mode count.

Still viable/open:

- 3D Sigma/collar volume modes;
- causal horizon volume modes;
- adiabatic radiation first law;
- negative-sector entropy projection.

Best current target:

```text
adiabatic radiation first law in the Janus/Z2 variable-constants frame
```

Report:

```text
outputs/reports/p0_eft_janus_phase_space_occupation_search_gate.md
```

## Conditional first-law closure

If the visible photon stress tensor is separately conserved in the plus-sector
FLRW frame and remains trace-free, then:

```text
d(rho_gamma V) + p_gamma dV = 0
p_gamma = rho_gamma/3
V ~ a^3
=> rho_gamma ~ a^-4
```

With Eq40 blackbody counting:

```text
h c ~ a
T_energy ~ a^-1
bare n_gamma ~ (T/(h c))^3 ~ a^-6
```

To keep comoving photon number/entropy conserved:

```text
occupation factor ~ a^3
```

This closes the required exponent conditionally. It is not unconditional until
the plus-sector radiation first law is derived from the Janus bimetric
projection.

## Photon stress conservation

The repo already has two useful anchors:

- M15/M30: positive-energy photons follow the plus-sector metric/geodesic family;
- a same-sector Noether stress-conservation scaffold in the Z2/Sigma branch.

Therefore the clean route is:

```text
S_gamma_plus[g_plus, A_plus]
+ minimal coupling to g_plus
+ photon equations of motion
+ no cross-sector photon exchange
=> nabla_plus T_gamma_plus = 0
```

The branch now adds that object as a minimal standard extension:

```text
S_gamma_plus = -1/4 int sqrt|g_plus| F_plus_mn F_plus^mn
```

This is compatible with the paper photon-geodesic anchors, but it is not an
explicit paper-native formula. Within this extension contract, Noether closes
`nabla_plus T_gamma_plus = 0` on shell and the radiation first-law input is no
longer blocked. The remaining hard objects are the variable-constants thermal
frame, active baryon density, ionization/drag history, and pre-drag `H_J(a)`.

## Thermal frame map

The thermal exponent is now solved rather than assumed. In Eq40:

```text
(h c)^3 ~ a^3
n_gamma ~ occupation * T_energy^3 / (h c)^3
rho_gamma ~ occupation * T_energy^4 / (h c)^3
```

Imposing both:

```text
n_gamma ~ a^-3
rho_gamma ~ a^-4
```

uniquely gives:

```text
T_energy ~ a^-1
occupation ~ a^3
```

The remaining hard step is to derive `occupation~a^3` as a real
entropy/phase-space degeneracy, not a bookkeeping factor.

## Drag exponent frontier

With conserved baryon/electron number and Eq40:

```text
n_e ~ a^-3
sigma_T ~ a^2
c ~ a^-1/2
Gamma_drag = n_e sigma_T c ~ a^-3/2
```

If:

```text
H_J ~ a^p
```

then:

```text
Gamma_drag / H_J ~ a^(-3/2 - p)
```

To have stronger coupling in the far past without relying on ionization
suppression, the native pre-drag branch needs:

```text
p > -3/2
```

Thus radiation-like `H_J ~ a^-2` or steeper is not enough in the Eq40 frame.
The next physical input must be either a Janus-native pre-drag `H_J(a)` branch
with shallower scaling, or an active ionization/visibility law. Fitting `alpha`
cannot repair this exponent-level issue.

Pushing the Eq40 Friedmann exponents gives:

```text
radiation fluid        -> H_J ~ a^-2      -> fails native early coupling
matter / baryons       -> H_J ~ a^-3/2    -> Gamma/H constant
curvature-like term    -> H_J ~ a^-3/2    -> Gamma/H constant
bridge/vacuum state    -> H_J shallower   -> can restore early coupling
```

So a native BAO branch cannot be obtained from ordinary radiation alone in this
frame. It needs either:

- a derived bridge/vacuum state component in the pre-drag background; or
- an active ionization/visibility law that supplies the crossing.

## Eq40 Saha visibility

The ionization route is not empty. With Eq40 and the solved thermal frame:

```text
m_e ~ a
T_energy ~ a^-1
h ~ a^3/2
n_b ~ a^-3
E_ion ~ a^0
```

The Saha scaling becomes:

```text
x_e^2/(1-x_e)
  ~ (m_e T / h^2)^(3/2) n_b^-1 exp(-E_ion/T)
  ~ a^-3/2 exp(-const * a)
```

So recombination/visibility is at least structurally native in the Eq40 frame:
small `a` is ionized, larger `a` recombines. The remaining blocker is absolute,
not structural: the model still needs the dimensionless anchor `E_ion/T0` or an
equivalent baryon/photon normalization before a numerical `z_d^J` can be
computed.

## Drag equation contract

The native symbolic crossing equation is now:

```text
A_drag * a^(-3/2 - p_H) * x_e(a; C_ion, eta_b) = 1
```

with:

```text
x_e^2/(1-x_e) = B_eta * a^-3/2 * exp(-C_ion * a)
```

This is structurally ready but not numerically predictive. Remaining anchors:

- `C_ion = E_ion/T0_Janus`;
- baryon/photon or baryon-density normalization;
- drag normalization `A_drag`;
- native full `H_J(a)`.

## Native sound horizon

The sound speed contract becomes:

```text
R_b(a) = R_b0 * a
c_s^J(a) = c0 a^-1/2 / sqrt(3(1 + R_b0 a))
r_d^J = int_{a_min}^{a_d} c_s^J(a)/(a^2 H_J(a)) da
```

If `H_J ~ a^p`, the small-`a` integrand scales as:

```text
a^(-5/2 - p)
```

A finite integral from `a=0` requires `p < -3/2`, but early drag coupling
without ionization wanted `p > -3/2`. This is a real tension. The Janus-native
way out is not a fit parameter: the branch must derive either a nonzero throat
lower bound `a_min>0`, or a transition in `H_J(a)` before the drag era.

The published exact shape does provide such a lower bound:

```text
a(u) = alpha cosh(u)^2
a_min = alpha
```

With present normalization and published `q0=-0.087`:

```text
a_min/a0 ~= 0.1482
z_max ~= 5.747
```

So the late-time SN branch regularizes the lower limit, but it does not reach a
pre-drag epoch. Native BAO therefore requires an attached early-time branch or a
modified early redshift map, not just reuse of the published SN background.

For a simple early map:

```text
1 + z = (a0/a)^s
```

the published throat requires:

```text
s ~= 3.62
```

to reach `z~1000`. Current candidates:

```text
s=1    M18 geometric redshift        -> fails
s=1.5  Eq40 clock/frequency unit     -> fails
s=3    Eq40 occupation/volume factor -> still fails
s=4    four-volume/action phase      -> reaches, but speculative
```

So the only viable redshift-map escape currently needs a real early photon/clock
transport derivation. It cannot be promoted as a guessed exponent.

Inverting the same calculation:

```text
s=1    requires q0 ~= -0.0005
s=1.5  requires q0 ~= -0.005
s=3    requires q0 ~= -0.055
s=4    requires q0 ~= -0.108
```

So low-power redshift maps push `q0` toward the same near-zero edge already
seen in BAO diagnostics. A four-power map is the only tested case close to the
published SN band, but it remains speculative until derived from photon/clock
transport.

The tempting decomposition:

```text
s = 1 geometric redshift + 3 occupation volume
```

is not valid as a redshift derivation. Occupation changes density/intensity, not
the frequency of an individual spectral line. A promotable high-power map must
come from photon four-momentum transport and atomic clock transport in the same
Eq40 frame. This is not yet derived.

A minimal photon/clock transport audit is actually negative for `s=4`:

```text
photon frequency transport        ~ a^-1
atomic transition frequency Eq40  ~ E_ion/h ~ a^-3/2
observed emitted-line frequency   ~ a^-1/2
inferred 1+z exponent             ~ +1/2
```

This depends on conventions, so it is diagnostic. But it shows that standard
null transport plus Eq40 atomic clocks do not generate the high-power redshift
needed for pre-drag BAO.

If high-power redshift is rejected, the only clean path is an attached early
branch. With geometric redshift to `z~1000`:

```text
required a_min/a0 <= 0.001
published late SN a_min/a0 ~= 0.148
```

The late branch is therefore too short by a factor of about 148. A native BAO
model would need an early Eq40/pre-drag branch plus a matching surface preserving
`a`, `H_J`, photon-clock transport, `c_s`, and `x_e`.

## Frontier verdict

The branch now has a sharp frontier:

- closed: Eq40 microphysics, Maxwell/radiation extension, first-law thermal
  frame, Saha visibility, symbolic drag equation, sound-speed/ruler contract;
- blocked: numeric `z_d^J`, `r_d^J`, baryon normalization, drag normalization,
  full pre-drag `H_J(a)`;
- surviving routes:
  - derive high-power photon/clock redshift transport;
  - derive an attached early-time branch with matching surface.

Do not import a Lambda-CDM ruler, multiply redshift by occupation, or use alpha
fitting to hide this boundary.

## Attached Early Branch Diagnostic

A minimal diagnostic early branch:

```text
a_E(y) = a_min,E cosh(y)^2
```

can be C0/C1 matched to the late SN branch at a chosen transition redshift by
choosing a new time-scale ratio. This shows that an attached early branch is not
geometrically impossible. It is not yet physics: the new time scale is a new
state/integration constant until derived from an action or boundary law.

The time-scale ratio itself can be reduced further. If:

```text
x = a_transition / a_min,E
```

then the early cosh branch has:

```text
h_shape,E = 2 sqrt(x - 1) / x^(3/2)
time_scale_ratio = (H_late/H0) / h_shape,E
                 ~ (H_late/H0) x / 2  for large x
```

So the ratio is fixed once `a_min,E` and the transition are chosen. The remaining
freedom is not the ratio; it is the physical selection of `a_min,E` and the
transition surface.

Candidate selectors for `a_min,E` were audited:

- setting it by `z~1000` is circular;
- Eq40 length scaling gives no absolute cutoff;
- Saha selects the drag surface, not the throat;
- Planck/quantum cutoff would be new quantum-gravity input;
- topological integer sector could work only if Janus derives `N`;
- the published late SN throat is too large.

So `a_min,E` is the remaining hard selector.

If one tries:

```text
a_min,E = 1/N
```

then geometric reach to `z~1000` needs:

```text
N >= 1001
```

The projective Janus cover gives `N=2`, so it cannot supply this. A large `N`
would have to come from a boundary Hilbert-sector dimension, flux quantization,
area quantization, or another derived state-count law, and it must enter photon
ruler dynamics rather than remain a label.

The cleanest quantum route is:

```text
CP1 spin-j orbit: N = 2j + 1
```

For `N=1001`, this requires:

```text
j = 500
KKS/CS level k = 1000
```

The repo already contains CP1/KKS scaffolding, but not the Janus/PT sector law
that selects `j=500` or `k=1000`. This is now the precise quantum-frontier
target.

The sector-selection frontier was then audited explicitly:

- projective cover selects `N=2`, not `N=1001`;
- CP1 can represent the needed sector through `j=500`, but does not select it;
- KKS/CS can represent the needed sector through `k=1000`, but does not select it;
- flux and spin-network/area routes still need a boundary gauge, area, or puncture law.

Current verdict:

```text
boundary Hilbert sector selector = blocked without boundary state law
```

So the branch has reached a hard quantum frontier: derive a Janus/PT boundary
state law, or keep `N` as an observational/global-state sector rather than a
no-fit prediction.

The boundary-state candidate matrix keeps all current non-rustine exits visible:

- `Sym^4(C^11)` symmetric boundary sector: `1001`;
- `CP1` spin superselection: `j=500`;
- KKS/Chern-Simons level selection: `k=1000`;
- flux/area puncture count: `N=1001`;
- exterior-power boundary fermion sector: `1001 = C(14,4)`;
- anomaly/modular consistency level;
- microcanonical boundary entropy peak.

None is accepted as derived. The new useful observation is only:

```text
1001 = 7 * 11 * 13 = C(14,4)
```

This makes a finite boundary Hilbert-sector law plausible enough to keep, but it
does not close the model unless Janus/PT derives the boundary modes, action, or
sector selection.

The strongest current numerical clue is now more structured than a bare
coincidence:

```text
M31: dim(Jan) = 11
M31: independent CPT generators = 3
11 + 3 = 14
M31: spacetime translation/stress-energy sector has dimension 4
C(14,4) = 1001
```

Interpretation candidate: a four-excitation exterior-power boundary sector over
the Janus torsor modes plus CPT generators. This is not accepted as a derivation,
because it still mixes continuous torsor modes and discrete CPT generators, and
the boundary exterior-algebra Hilbert law/statistics is not derived.

The exterior-degree spectrum is also restrictive: for 14 primitive modes, only
degrees `4` and `10` give `1001`. Degree `4` has the cleaner Janus anchor because
M31 already has an `R4` translation/stress-energy sector; degree `10` is only the
dual complement.

Consistency audit: in strict M31, `C,P,T` are discrete connected-component
labels. If they remain discrete labels, they multiply sectors rather than add
three one-particle modes. Then the natural dimensions are:

```text
Lambda^4(C^11) = 330
2^3 * Lambda^4(C^11) = 2640
```

not `1001`. Therefore the `C(14,4)` route now has one precise missing theorem:

```text
derive boundary CPT fermionization / Clifford lift
```

Without that, `C(14,4)` is the best numerical clue, not a legal no-fit selector.

Existing Z2/Sigma work helps but does not close this:

- resolved tunnel Pin lift: ready;
- Z2/Sigma spinor projection: ready;
- unit normal Clifford action: ready;
- projected charge reduction: ready, but `N_occ` remains open.

So the remaining theorem is not ordinary Pin geometry. It is stronger:

```text
C,P,T must become three occupiable boundary fermion/CAR modes,
with a derived exterior/Fock statistics and selected Lambda^4 sector.
```

Currently no such boundary fermionization law is derived.

Stronger alternative found after the consistency audit:

```text
dim Sym^4(C^11) = C(11 + 4 - 1, 4) = C(14,4) = 1001
```

This is cleaner than `Lambda^4(C^(11+3))` because it uses only the M31
continuous Janus Lie/torsor dimension `11`. The degree `4` is anchored by the
M31 `R4` translation/stress-energy block. It avoids treating `C,P,T` as
fermionic modes.

Current best candidate:

```text
boundary sector = homogeneous degree-4 symmetric states over the 11 Janus torsor modes
```

Still missing:

```text
derive boundary bosonic/Fock statistics;
derive why the physical sector is Sym^4;
derive Sym^4 -> a_min -> photon/ruler dynamics.
```

If those missing steps were derived, the chain would become:

```text
N = dim Sym^4(C^11) = 1001
a_min = 1/N
z_max = N - 1 = 1000
```

So this would exactly repair the pre-drag reach. The open issue is not arithmetic;
it is the state law connecting the M31 torsor Hilbert sector to the early throat.

Second audit: `N=1001` repairs BAO reach only under a linear-resolution map:

```text
a_min = 1/N
```

Other natural maps fail:

```text
area map:   a_min = 1/sqrt(N)     -> z_max ~ 30.6
volume map: a_min = 1/N^(1/3)     -> z_max ~ 9.0
entropy map: same scaling class as volume here
```

So the remaining theorem is even sharper:

```text
Sym^4(C^11) must count linear throat/redshift resolution states.
```

Cleanest current interpretation:

```text
Sym^4(C^11) counts states of the one-dimensional normal/redshift channel.
```

This is physically plausible because the early-branch BAO obstruction has been
reduced to the single lower bound `a_min`. It is still not derived: we need a
normal-channel spectral operator, or an equivalent boundary law, whose state
count is `dim Sym^4(C^11)`.

Spectral-operator audit:

```text
candidate operator = self-adjoint 1D normal/redshift Sturm-Liouville problem
linear mode indexing = available
spectrum without cutoff = infinite
finite N selected by operator alone = false
finite N selected by Sym4 sector = true, conditionally
```

This sharpens the missing theorem. A one-dimensional operator can justify linear
mode counting, but it does not itself pick the finite bandlimit `N=1001`. The
remaining no-fit requirement is:

```text
derive a Janus/PT boundary state law where Sym^4(C^11) is the finite bandlimit
of the normal/redshift channel, then prove a_min = 1/N.
```

Stronger version:

```text
normal/redshift evolution = finite transfer operator on Sym^4(C^11)
```

This avoids imposing a cutoff on an infinite continuum spectrum. The finite
dimension is then intrinsic:

```text
dim Sym^4(C^11) = 1001
```

But it still needs a real Janus/PT transfer generator:

```text
finite transfer matrix on Sym^4(C^11);
unitary or self-adjoint evolution rule;
Z2/PT covariance;
ordered normal-resolution spectrum;
proof that endpoint count gives a_min = 1/1001;
proof that photon-baryon drag uses the same clock.
```

Transfer-generator matrix:

```text
M31 quadratic Casimir: anchored, finite on Sym4, but does not order 1001 normal states
R4 number/stress-energy operator: anchored, finite, but constant on degree 4
PT modular flow: anchored as symmetry, but no modular Hamiltonian/density matrix derived
basis path graph: orders states, but arbitrary unless derived from Janus/PT
boundary Hamiltonian from action: required object, not yet derived
```

So the current best route is precise:

```text
derive a Janus/PT boundary Hamiltonian or transfer generator on Sym^4(C^11)
whose Z2/PT-covariant ordered spectrum supplies 1001 normal/redshift endpoint states.
```

Diagonal Hamiltonian audit:

```text
M31 physical blocks = ell(3), g(3), p(3), E(1), q(1)
Sym4 basis states = 1001
isotropic block occupation profiles = C(4+5-1,4) = C(8,4) = 70
```

Therefore a diagonal Hamiltonian that only distinguishes the published M31
physical blocks cannot order all 1001 states. To get 1001 distinct normal
levels one needs either:

```text
componentwise weights inside ell/g/p triplets, which requires an extra selector
or breaks isotropy;
or a non-diagonal boundary transfer generator derived from the Janus/PT action.
```

M31-to-Sym4 representation gap:

```text
available: M31 coadjoint/torsor action
available: structural boundary mode space V = C^11
missing: rho: janus_lie -> End(V)
missing: lifted action on Sym^4(V)
missing: selected normal/redshift Hamiltonian
missing: ordered spectrum -> a_min map
```

This is the minimal non-diagonal route. It would not fit observations directly;
it would define how the published Janus symmetry transports boundary states.

Refinement:

```text
rho candidate = M31 coadjoint action on torsor components (l,g,p,E,q)
lift to Sym^4(C^11) = standard once rho is accepted
```

This partially closes the representation gap. The remaining problem is not
`rho` itself; it is the physical normal/redshift Hamiltonian. Natural M31 blocks
do not provide it:

```text
Lorentz rotations: classify/isotropize, not cosmological normal time
Lorentz boosts: observer-frame changes, not throat endpoint evolution
translations: coadjoint shears, not a self-adjoint 1001-level clock
charge reflection/translation: sector labels, not ordered redshift levels
```

Normal-Hamiltonian route ranking:

```text
best next route: PT/Sigma boundary action Hamiltonian
second route: boundary modular Hamiltonian from a state law
insufficient alone: geometric throat length operator, because scale returns
blocked alone: KKS moment map, because no M31 generator is H_normal
rejected: empirical or lexicographic basis ordering
```

The next real calculation is therefore:

```text
construct theta_Sigma and Omega_boundary;
identify the normal/throat evolution vector field X_normal;
derive delta H = i_X Omega_boundary;
lift H to Sym^4(C^11);
test whether its ordered spectrum supplies 1001 endpoint states.
```

Existing reusable brick:

```text
Z2/Sigma Noether boundary charge:
delta H_xi = integral_Sigma (delta Q_xi - i_xi theta)
Brown-York symbolic reduction: E_BY = kappa^-1 integral N sqrt(q)(k_ref-k_phys)
symbolic H ready = true
numeric H ready = false
```

This is the right symbolic source for `theta_Sigma/Omega_boundary`, but it does
not yet close the early-ruler branch. Missing bridge:

```text
boundary H used as X_normal generator;
boundary H -> End(Sym^4(C^11));
Z2/PT covariance;
ordered 1001-state spectrum;
same clock for photon drag.
```

Scalar-vs-operator audit:

```text
Brown-York/Noether H_boundary = scalar energy charge
action on Sym^4(C^11) = H_boundary * Identity
number of ordered levels from scalar H = 1
required ordered levels = 1001
```

Therefore the existing boundary energy is not enough as a transfer operator. The
branch needs one of:

```text
M31-valued boundary charge H_A rho(T_A);
non-diagonal H_normal from theta_Sigma/Omega_boundary;
modular Hamiltonian from a derived boundary state.
```

Plus/minus leg audit:

```text
leg difference operator: at most 2 levels
leg PT mixing operator: at most 2 levels
leg operator tensor identity on Sym4: does not split Sym4 states
leg operator tensor H_M31_normal: works only if H_M31_normal is independently derived
```

So the two boundary legs are physically meaningful as a PT doublet, but they do
not replace the missing internal `Sym^4(C^11)` transfer generator.

Frontier verdict:

```text
exhausted:
- scalar Brown-York/Noether boundary energy;
- M31 isotropic block diagonal Hamiltonian;
- natural M31 coadjoint generators;
- plus/minus PT leg operator;
- manual basis ordering.

remaining:
- non-diagonal H_normal from PT/Sigma boundary action;
- or modular Hamiltonian from a boundary state law.
```

So this subbranch should not continue by adding more combinatorial selectors.
Further progress requires deriving `H_normal` from the action or from a modular
state.

Schur obstruction:

```text
Sym^4(C^11) is irreducible under the natural linear action.
Any fully invariant Hamiltonian on this sector is scalar.
A scalar Hamiltonian cannot order 1001 states.
```

So a useful `H_normal` must be derived symmetry breaking, not fully symmetric:

```text
PT/Sigma action selects a normal generator;
or a boundary modular state selects a Hamiltonian;
or a derived operator-valued boundary charge reduces the symmetry.
```

Symmetry-breaking candidates:

```text
recommended: PT/Sigma normal generator -> internal Sym4 matrix
credible second route: boundary modular Hamiltonian
not enough: cosmological time flow, currently scalar
rejected: arbitrary componentwise triplet direction
```

So the next concrete theorem is:

```text
PT normal orientation must induce a non-scalar internal matrix on the M31/Sym4
boundary sector.
```

PT-normal attempt:

```text
global PT sign on all modes: scalar on Sym4
plus/minus leg exchange: external doublet only
CPT/M31 block signs: finite block splitting, not 1001 ordering
normal connection endomorphism A_normal on C^11: needed, not derived
```

So the refined missing object is:

```text
A_normal: C^11 -> C^11
```

derived from the pullback of the PT/Sigma normal connection on the boundary mode
bundle, then lifted to `Sym^4(C^11)`.

Existing normal-connection machinery:

```text
calculator: src/janus_lab/z2_sigma_normal_connection.py
input: outputs/active_z2_sigma/normal_connection_frame_primitives.json
output: outputs/active_z2_sigma/normal_connection_omega_perp_inputs.json
status: calculator ready, active input manifest missing
```

Even an active `omega_perp` would still not be enough by itself. It is a
normal-frame connection matrix. The missing bridge is:

```text
rho_perp: normal-frame algebra -> End(C^11)
A_normal = rho_perp(omega_perp)
lift A_normal to Sym^4(C^11)
```

Spectral condition for `A_normal`:

```text
If A_normal has C11 weights w_i,
then Sym4(A_normal) has weights w_i+w_j+w_k+w_l.
```

To obtain 1001 ordered levels, those degree-4 multiset sums must all be
distinct. Equivalently:

```text
the 11 C11 weights must be 4-dissociated.
```

Checks:

```text
scalar weights: 1 level
M31 block weights: 70 profiles
arithmetic component weights 0..10: too resonant
base-5 weights: 1001 levels, but not Janus-derived
```

So the exact remaining theorem is:

```text
derive 4-dissociated A_normal eigenweights from PT/Sigma normal holonomy,
normal connection, or a boundary modular state.
```

Weight-origin matrix:

```text
rejected no-fit closures:
  scalar boundary charge
  published M31 block weights
  topological cycle number alone
  generic base-5 weights

credible remaining routes:
  active PT/Sigma normal connection -> rho_perp -> A_normal
  boundary modular state -> modular Hamiltonian on C11
```

Current status:

```text
frontier narrowed
no-fit not closed
```

M31 compact-charge audit:

```text
source: EPJC 2024 Janus/Souriau-Kaluza compact charge sector, eqs. 43-72
closes: compact charge dimensions, PT/C sign action, charge quantization motivation
does not close: A_normal, rho_perp -> End(C11), four-dissociated weights
```

Interpretation:
compact charge dimensions are relevant to a boundary-state route, but ordinary
charge labels/signs do not yet give the native 1001-level early-ruler operator.

Active normal-connection availability:

```text
current assets: local Sigma unit frame, torsionless baseline, zero torsion pullback
missing: active collar embedding X(lambda,u)
missing: normal frame N_A(lambda,u)
missing: partial_u N_A(lambda,u)
missing: ambient connection Gamma_u(lambda,u)
```

Therefore a zero/local manifest must not be used as proof of `A_normal`.

Existing collar probes:

```text
round product collar: omega_perp = 0, no radius/weight selection
pure deck sign twist: lambda-independent defect, no unique root
nonlocal twist probe: can select a root, but diagnostic-only and not action-derived
```

So the required object is not a simple projective sign. It is a nontrivial
active normal connection or boundary state law derived from Janus/PT data.

### Quantum Fock no-carry candidate

Constructive operator:

```text
A_no_carry = sum_i 5^i N_i on Sym^4(C^11)
```

Reason:

```text
Sym degree = 4
occupations n_i range from 0 to 4
minimal no-carry base = degree + 1 = 5
```

Result:

```text
distinct levels = 1001
orders all Sym^4(C^11) states = true
```

This is the sharpest constructive candidate so far. It would make the
1001-level early-ruler sector exact. It is not yet promoted because Janus/PT
still has to derive:

```text
ordered 11-mode basis on C^11
no-carry modular Hamiltonian or q=5 boundary state law
rho_perp mapping normal/boundary transport to A_no_carry
```

Souriau torsor bridge:

```text
C11 can be anchored as mu={l,g,p,E,q}
dimensions: 3 + 3 + 3 + 1 + 1 = 11
```

This removes part of the arbitrariness: the 11-dimensional carrier can be read
as the published Janus/Souriau torsor component space. It does not yet derive
the component order or the base-5 modular hierarchy.

Coadjoint-action filtration:

```text
q' = lambda*mu*q
P' = L P
M' = L M L^T - L P C^T + C P^T L^T
```

This gives a natural `q / P / M` hierarchy with dimensions `1 + 4 + 6 = 11`.
It is source-derived, but too coarse: on `Sym^4` it gives 15 block profiles,
not 1001 ordered states.

Isotropy obstruction:

```text
SO(3)-preserving torsor blocks: l(3), g(3), p(3), E(1), q(1)
degree-4 block profiles: C(5+4-1,4) = 70
full Sym^4(C^11) states: C(11+4-1,4) = 1001
```

Therefore a component-level no-carry Hamiltonian would break visible spatial
isotropy unless it is reinterpreted as boundary microstate structure with a
derived isotropic observable average.

Boundary microstate interpretation:

```text
hidden boundary microstates: 1001
visible isotropic macro profiles: 70
```

This avoids a visible preferred spatial direction only if a Janus/PT boundary
state law proves:

```text
SO(3)-invariant boundary density matrix
visible tensors depend only on triplet averages
early ruler uses hidden microstate count rather than macro profile count
```

This is the current best place where the quantum/complex-reality branch can
help.

Microcanonical boundary state attempt:

```text
rho_boundary = Identity_on_Sym^4(C^11) / 1001
SO(3)-invariant = true
visible preferred direction = false
S_boundary = log(1001)
a_min candidate = exp(-S_boundary) = 1/1001
```

This closes the isotropy part of the hidden-microstate idea. It still does not
derive why the photon-baryon ruler must use `exp(S_boundary)` rather than the
70 isotropic macro profiles.

Entropy-to-resolution map:

```text
S_boundary = log(1001)
a_min = exp(-S_boundary) = 1/1001
z_max = 1000
```

This closes the dimensionless resolution arithmetic. It does not yet close the
physical coupling of this boundary resolution to the native photon-baryon drag
epoch or sound-horizon integral.

Entropy cutoff to sound horizon:

```text
r_d^J = int_{a_min}^{a_d} c_s^J(a)/(a^2 H_J(a)) da
a_min = 1/1001
```

This conditionally removes the lower-limit obstruction and reaches `z=1000`.
Still missing for an executable BAO/ruler:

```text
a_d^J
H_J(a)
R_b0 or baryon/photon normalization
proof that Janus action couples boundary entropy to the plasma ruler
```

Drag readiness after entropy cutoff:

```text
closed/available:
  a_min = 1/1001
  CODATA constants
  FIRAS photon temperature
  photon density normalization
  C_ion = E_ion/(k_B T0)

still missing:
  baryon number or eta_b normalization
  native H_J(a)
  A_drag normalization
```

Exact-shape compatibility:

```text
same cosh branch relation: z_max = -1/(2 q0)
entropy cutoff z_max=1000 -> q0=-0.0005
published late SN q0=-0.087 -> z_max~5.75
```

Therefore the entropy cutoff cannot be inserted into the same late SN exact
branch without destroying the published late-time fit. A native early branch
and an early-to-late matching surface are required.

Two-cosh gluing obstruction:

```text
if early and late branches are both a=a_min cosh(u)^2
and they are glued at the late branch throat:
  C0 scale match possible
  C1 shape match impossible without extra transition/lapse/surface
```

Reason:
the late branch has zero shape velocity at its throat, while the entropy early
branch reaches that same scale with nonzero shape velocity.

Report:

```text
outputs/reports/p0_eft_janus_plus_sector_photon_stress_conservation_gate.md
```

So the extension is real, but not yet an executable native BAO prediction.

Report:

```text
outputs/reports/p0_eft_janus_early_universe_native_plasma_extension_gate.md
```

## Final early/late matching pass

The current throat/entropy branch has been pushed to its non-rustine frontier.

```text
same late cosh branch: blocked
two-cosh gluing at late throat: blocked by C1 mismatch
entropy-cutoff sound horizon: partially progressed
native drag epoch: partially progressed
transition surface or lapse law: absent
```

What is genuinely gained:

```text
hidden 1001 microstate count can be isotropic via a microcanonical state
a_min = 1/1001 gives z_max = 1000
C_ion is available from CODATA/FIRAS
```

Remaining blockers:

```text
derive early H_J(a)
derive baryon/eta_b normalization
derive a transition surface or lapse matching law
preserve the published late SN q0 branch
```

Next branch:

```text
JanusProjectivePointPTLimit
```
