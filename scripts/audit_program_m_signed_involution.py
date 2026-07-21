"""MF-SIGN-001: audit the minimal sign-reversing involution extension."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def run_audit() -> dict[str, object]:
    swap = (1, 0)
    magnitudes = (1, 2, 3)
    odd_charges = tuple((magnitude, -magnitude) for magnitude in magnitudes)
    invariant_charges = tuple((magnitude, magnitude) for magnitude in magnitudes)
    odd_gates = [
        charge[swap[x]] == -charge[x]
        for charge in odd_charges
        for x in range(2)
    ]
    simultaneous = tuple(
        charge
        for charge in ((a, b) for a in range(-3, 4) for b in range(-3, 4))
        if all(charge[swap[x]] == charge[x] == -charge[x] for x in range(2))
    )
    return {
        "program": "MF-SIGN-001",
        "involution": list(swap),
        "odd_charge_candidates": [list(charge) for charge in odd_charges],
        "invariant_charge_candidates": [list(charge) for charge in invariant_charges],
        "simultaneously_invariant_and_odd": [list(charge) for charge in simultaneous],
        "gates": {
            "all_declared_odd_pairs_reverse_sign": all(odd_gates),
            "odd_pair_total_charge_is_zero": all(sum(charge) == 0 for charge in odd_charges),
            "magnitude_remains_free": len(odd_charges) == 3,
            "ordinary_invariance_and_oddness_force_zero": simultaneous == ((0, 0),),
        },
        "conclusion": (
            "nonzero opposite charges require a sign-twisted transformation law; "
            "the involution fixes pairing but not magnitude"
        ),
        "scope": (
            "abstract signed charge only; no interpretation as inertial or "
            "gravitational mass"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
