# Program B — PT boundary variation gate

- Program: **B**
- Stable ID: `B-PT-BOUNDARY-VARIATION`
- Evidence: **T** (Lean) plus conditional **X** Cartan–GHY audits
- Dependencies: PT boundary pairing and supplied reduced surface density
- Lean target: `P0EFTJanusPTQuasilocalChargePairing.lean`

## Result

For a PT-odd boundary first-variation functional, variations paired by PT have
opposite values and cancel in the total first variation. The existing Cartan–GHY
audits also verify, for the supplied reduced surface density, the boundary
constraint and its agreement with the scalar gate.

A separate no-go theorem records that paired cancellation does not imply
independent vanishing of the two boundary variations. Therefore it cannot by
itself replace the full junction equations.

## Remaining scope

Still required are the full Cartan–GHY derivation, null/corner terms, independent
plus/minus boundary variations, the boundary symplectic potential and an
integrable Hamiltonian charge with proven PT orientation signs.

## Failure criterion

Reject any claimed junction closure based only on cancellation after imposing
the PT pairing before variation.
