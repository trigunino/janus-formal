# Program B — local-GR / PPN source gate

- Program: **B**
- Stable ID: `B-LOCAL-GR-PPN-SOURCE`
- Evidence: **T** (Lean theorem)
- Dependencies: massless diagonal and massive relative tensor modes
- Lean target: `P0EFTJanusLocalGRSourceDecoupling.lean`

## Result

The linear source coupling decomposes exactly into diagonal and relative modes:

```text
J_+ h_+ + J_- h_-
= (J_+ + J_-)/2 (h_+ + h_-)
+ (J_+ - J_-)/2 (h_+ - h_-).
```

Consequences:

- the relative massive mode is unsourced exactly when `J_+ = J_-`;
- a source placed on one sheet excites the relative mode;
- equal sources excite a pure diagonal GR-like mode;
- opposite PT sources excite a pure relative mode.

Therefore the existence of a massless diagonal eigenmode is insufficient to
prove the local-GR or post-Newtonian limit. The physical matter source map must
either suppress/screen the relative source or make its effects compatible with
local bounds.

## Remaining scope

Still open: propagators with physical normalization, effective Newton constant,
Yukawa/Vainshtein behavior, PPN gamma and preferred-frame bounds.
