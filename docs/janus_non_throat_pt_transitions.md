# Janus Non-Throat PT Transitions

Purpose: compare non-gorge/non-point alternatives that keep a transition
structure without a finite Sigma radius.

Candidate ranking:

```text
1. ConformalPTBoundary
   best compromise: no Sigma radius, but finite conformal matching data

2. CrosscapPTTransition
   topologically natural PT/crosscap route, harder to dynamize cleanly

3. NullPTBoundary
   causal bridge route, but requires null charge/tension or null boundary law
```

First test contract for `ConformalPTBoundary`:

```text
define conformal boundary metric class [h]
derive PT action on [h] and matter/energy signs
derive conformal redshift map
check whether the late SN branch attaches without C1 throat mismatch
```

Status: candidate matrix opened, no observational branch yet.

## Conformal PT Boundary Attempt

Current result:

```text
finite Sigma radius removed = true
C1 throat mismatch removed = true
conformal boundary class declared = true
PT action on conformal class declared = true
conformal lapse/clock law derived = false
native early H_J(a) derived = false
active baryon normalization derived = false
```

Interpretation: this is the strongest current path. It removes the finite-throat
artifact, but it does not yet derive the early clock/ruler.

## Crosscap PT Transition

Current result:

```text
sigma radius removed = true
non-orientable PT transition declared = true
topological Z2 action available = true
local field equations on crosscap derived = false
stress-free transition proved = false
redshift/clock law derived = false
ruler contract derived = false
```

Interpretation: crosscap is topologically clean but dynamically weaker than the
conformal boundary route.

## Exotic Matrix

Current ranking:

```text
1. WeylCuspPTBoundary
2. MobiusNormalBand
3. CrosscapPTTransition
4. LensSpacePTQuotient
5. BranchedCoverPTTransition
```

The useful exotic direction is not arbitrary topology. It is a conformal/Weyl
transition where physical volume can vanish while conformal boundary data and a
clock law remain available.

## Weyl Cusp PT Boundary

Ansatz:

```text
g = Omega^2 g_hat
Omega -> 0 at the PT boundary
[g_hat] remains finite
```

Result:

```text
finite Sigma radius removed = true
physical volume can vanish = true
finite conformal boundary data = true
pre-drag redshift domain available = true
late cosh z_max obstruction removed = true

Weyl gauge fixed by action/matter clock = false
physical clock law derived = false
conformal Friedmann equation derived = false
late SN matching law derived = false
```

Interpretation: this is the first non-throat route that genuinely removes the
early-redshift domain obstruction. It is still not predictive because a Weyl
cusp is gauge until the Janus action or matter sector selects the physical clock
frame.

Next hard calculation:

```text
derive Weyl-frame matter coupling
derive physical clock/lapse
derive conformal Friedmann equation for Omega
derive matching law to the published late SN branch
```

## Physical Clock Candidates

Ranking for making the Weyl cusp observable:

```text
1. VisibleMatterJordanFrame
   best route if visible matter is shown to couple to g = Omega^2 g_hat

2. BimetricScaleRatioClock
   Janus-native route if Omega is derived from a_plus/a_minus or determinant ratio

3. ThermalPhotonClock
   useful only after entropy and baryon/photon normalization are derived

4. DilatonCompensatorClock
   mathematically clean but an extension: adds a new field/action

5. PureConformalGeometryClock
   rejected: a conformal class alone has no physical clock
```

Current verdict:

```text
Weyl cusp solves the redshift-domain problem.
It does not become predictive until matter coupling or bimetric scale-ratio
dynamics selects the physical conformal frame.
```

## Visible Matter Jordan Frame

Local source audit:

```text
published positive-sector geodesic rule = true
visible photons follow g(+) = true
visible matter clock fixed by g(+) = true
Weyl gauge fixed for visible observers = true
```

This is real progress: the visible physical clock is not arbitrary. It is the
`g(+)` Jordan frame used by positive-energy matter and photons.

Still missing:

```text
g(+) pullback to Weyl cusp
Omega evolution from bimetric equations
redshift map through PT boundary
matching to late SN branch
```

## Bimetric Scale-Ratio Clock

Current result:

```text
two scale factors available = true
published ratio signals available = true
determinant-ratio field equations available = true
Omega defined uniquely as bimetric ratio = false
ratio evolution through pre-drag = false
ratio selects physical visible clock = false
```

Interpretation: this remains the best Janus-native dynamical route after the
visible Jordan frame, but it needs an explicit ratio evolution law. The existing
ratio statements do not yet define the Weyl-cusp clock.

## GPlus Weyl-Cusp Kinematic Pullback

The visible-clock pullback is now explicit:

```text
g_plus = Omega^2 g_hat_plus
d tau_plus = Omega d tau_hat
a_plus = Omega a_hat
1 + z = (Omega_obs a_hat_obs) / (Omega_emit a_hat_emit)
H_plus = Omega^-1 (H_hat + d ln(Omega)/d tau_hat)
```

This closes the kinematic part. It does not close the dynamics:

```text
Omega dynamics derived = false
source terms in conformal frame derived = false
```

## Omega Equation Contract

Minimal conformal Friedmann contract:

```text
a_plus = Omega a_hat
H_plus = Omega^-1 (H_hat + d ln(Omega)/d tau_hat)
H_plus^2 + k/a_plus^2 = kappa_eff rho_eff_plus / 3
```

Equivalent Omega equation:

```text
(H_hat + d ln(Omega)/d tau_hat)^2 + k/a_hat^2
  = Omega^2 kappa_eff rho_eff_plus / 3
```

This equation can be written without a throat radius. To solve it, the branch
needs:

```text
hat background
rho_eff_plus
initial/boundary condition for Omega
```

## Omega Dynamics Candidates

Current ranking:

```text
1. ConformalEinsteinTrace
   derive Omega from trace/00 projection of G[g_plus] after g_plus=Omega^2 g_hat

2. BimetricDeterminantRatio
   derive Omega from sqrt(-g_minus/-g_plus) or scale-factor ratio

3. VisibleMatterConservation
   useful but insufficient unless a_hat is fixed

4. VariableConstantsClock
   must be tied to the Weyl cusp, not inserted independently

5. DilatonCompensator
   extension only
```

Next concrete calculation:

```text
ConformalEinsteinTrace reduction.
```

## Conformal Einstein Trace Reduction

With:

```text
g_plus = exp(2 phi) g_hat_plus
Omega = exp(phi)
```

the 4D trace reduction gives:

```text
R[g_plus] = exp(-2 phi) (R_hat - 6 box_hat(phi) - 6 |grad_hat phi|^2)
-R[g_plus] = kappa_eff T_eff_plus
```

so:

```text
R_hat - 6 box_hat(phi) - 6 |grad_hat phi|^2
  = - kappa_eff exp(2 phi) T_eff_plus
```

This is the first true Omega equation without a throat radius and without adding
a dilaton. It is still blocked by active data:

```text
R_hat source
T_eff_plus source
PT/late boundary condition
```

## Determinant Ratio Check

Janus-native determinant coupling:

```text
Q_det = sqrt(-g_minus / -g_plus)
```

For FLRW:

```text
Q_det = (N_minus a_minus^3)/(N_plus a_plus^3)
```

If the two metrics were conformal:

```text
g_minus = Xi^2 g_plus -> Q_det = Xi^4
```

But the determinant ratio alone fixes a volume scale, not a unique full
conformal metric factor. This route needs a near-PT conformality theorem or a
gauge condition.

## Late SN Matching Boundary Problem

The matching problem is now:

```text
PT cusp: Omega -> 0 with finite g_hat data
late SN recovery: Omega -> 1 and d ln(Omega)/d tau_hat -> 0
smooth clock: H_plus finite wherever the late branch is regular
```

This turns the branch into a precise boundary-value problem for Omega. It is not
solved until the conformal trace equation is fed with Janus-native sources and
boundary data.

## Trace Source Audit

The trace equation is not enough for pre-drag physics:

```text
photons/radiation: trace = 0
baryons/nonrelativistic matter: trace nonzero
negative-sector dust: signed trace possible
vacuum/reference term: trace nonzero
```

So the correct early-plasma projection is:

```text
ConformalEinstein00
```

not trace alone.

## Conformal Einstein 00 Route

Use:

```text
(H_hat + d ln(Omega)/d tau_hat)^2 + k/a_hat^2
  = Omega^2 kappa_eff rho_eff_plus / 3
```

This keeps radiation in the source. It still needs:

```text
hat_H
rho_eff_plus
Omega boundary condition
```

## Hat Background Candidates

Ranking:

```text
1. ProjectiveS4RP4ConformalBackground
2. FlatMilneReferenceBackground
3. MinusSectorBackground
4. ArbitraryRegularHatMetric
```

Best no-rustine route:

```text
derive g_hat from S4_L -> RP4_L projective conformal geometry.
```

Flat/Milne is only a reference check unless PT geometry derives it.

## Projective S4/RP4 Conformal Background

The projective topology supplies a natural conformal chart:

```text
cover: S4_L
quotient: RP4_L = S4_L/(x ~ -x)
chart: S4_L minus one PT point is conformal to R4
hat metric: flat chart metric on the punctured conformal patch
Omega_S4(r) = 2 L^2/(L^2 + r^2)
PT limit: r -> infinity gives Omega_S4 -> 0
```

This closes the geometry of `g_hat` for the Weyl-cusp route.

It does not close cosmology:

```text
absolute L fixed by geometry = false
Lorentzian FLRW time derived = false
rho_eff_plus derived = false
```

Interpretation: the projective geometry removes the need for a finite throat
radius and supplies a conformal compactification. It still needs a Lorentzian
cosmological time/source law to become predictive.

## Bimetric `rho_eff_plus` Source Contract

Published Janus source anchor:

```text
G(+) = chi [T(+) + sqrt(-g(-)/-g(+)) T(-)]
```

Therefore the plus-sector effective source contract is:

```text
Q_det = sqrt(-g_minus / -g_plus)
T_eff_plus = T_plus + Q_det T_minus
rho_eff_plus_00 = rho_plus + Q_det rho_minus_projected
rho_plus = rho_r_plus + rho_b_plus + ...
```

This contract is source-derived. It is not yet a pre-drag source model:

```text
rho_plus radiation component derived = false
rho_plus baryon component derived = false
rho_minus projection component derived = false
pre-drag scaling derived = false
```

## Projective `H_hat` Limit

`S4/RP4` closes:

```text
hat conformal class
PT cusp coordinate
Omega_S4(r)
```

It does not close:

```text
absolute L
Lorentzian time slicing
observable H_hat
```

So topology supplies the conformal class, not the physical Hubble clock.

## Omega 00 Bottom Frontier

Closed:

```text
g(+) Weyl kinematics
projective hat conformal geometry
plus-sector source contract
00/Friedmann projection choice
```

Still open:

```text
absolute L
Lorentzian time slicing
observable H_hat
pre-drag rho_plus components
Omega boundary condition
```

This is the bottom of the current non-throat Weyl-cusp branch. The old blocker
is not gone; it has been reduced to a cleaner form without finite Sigma throat
or arbitrary counterterm.

## Global Conservation To Omega

Using the published signed-energy conservation:

```text
rho_plus c_plus^2 a_plus^3 + rho_minus c_minus^2 a_minus^3 = E_global
```

and:

```text
a_plus = Omega a_hat
```

gives:

```text
Omega^3 =
  (E_global - rho_minus c_minus^2 a_minus^3)
  / (rho_plus c_plus^2 a_hat^3)
```

This is an algebraic Omega relation, not a prediction. It needs:

```text
E_global
minus-sector history
plus pre-drag density
c-law tied to the Weyl cusp
```

## Internal Route Exhaustion

Routes pushed:

```text
ProjectiveS4RP4Topology
VisibleMatterJordanFrame
ConformalEinstein00
BimetricSourceContract
DeterminantRatio
GlobalSignedEnergyConservation
BoundaryMicrostateEntropy1001
Crosscap/Mobius/Lens/Branched variants
```

All stop at the same class of missing data:

```text
physical scale
Lorentzian clock
active pre-drag source
boundary/state law
```

## Final Frontier

Closed without rustine:

```text
Weyl-cusp redshift domain
g(+) visible kinematics
S4/RP4 hat conformal background
bimetric plus-sector source contract
global conservation Omega relation
00 projection choice
```

Not closed without a new derived law:

```text
absolute L or E_global
Lorentzian time slicing
pre-drag source scalings
Omega boundary condition
```

Final verdict: the branch is cleaner than the finite-throat route, but it is not
a no-fit observable model until a real Janus state/source/clock law is added or
derived.
