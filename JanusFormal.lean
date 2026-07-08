/- Root Janus facade.

Default build:
  `lake build JanusFormal`

This imports only the active Z2/Sigma proof surface through
`JanusFormal.ActiveZ2Sigma`.

Archived CMB/Z4 and exploratory modules are intentionally outside the default
facade. Build them explicitly only when auditing history:
  `lake build JanusFormal.AllImportsArchive`
-/

import JanusFormal.ActiveZ2Sigma
import JanusFormal.ComplexRealityStateLaw
