"""MF-PBRIDGE-002: audit the conditional signed M-to-P adapter boundary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "JanusFormal/Foundations/ProgramMSignedProgramPAdapter.lean"

SUPPLIED = (
    "relational configuration carrier",
    "relation-preserving involutive exchange",
    "binary positive/negative sector label for nonzero charge",
    "exact exchange of the two sector labels",
    "positive charge magnitude separated from its sign",
    "signed-source algebraic factorization",
)

REMAINS_EXTERNAL = (
    "existence and choice of the involution",
    "odd charge law and nonzero-charge restriction",
    "charge magnitude and physical normalization",
    "interpretation as inertial or gravitational mass",
    "smooth manifold, dimension, Lorentzian metric and fields",
    "throat, mapping torus, PT spacetime map and SpinC data",
    "parent action, Euler source, Helmholtz data and selected action",
    "Newtonian mediator law and covariant dynamics",
)


def run_audit() -> dict[str, object]:
    text = LEAN.read_text(encoding="utf-8")
    theorem_names = (
        "sectorOfRealCharge_value_mul_magnitude",
        "sectorOfRealCharge_neg",
        "SignedProgramPInput.sector_exchange",
        "SignedProgramPInput.charge_factorization",
        "SignedProgramPInput.source_factorization",
    )
    forbidden_structure_tokens = (
        "LorentzianMetric",
        "SmoothManifold",
        "throat :",
        "action :",
    )
    return {
        "program": "MF-PBRIDGE-002",
        "lean_adapter": str(LEAN.relative_to(ROOT)).replace("\\", "/"),
        "supplied_to_program_p": list(SUPPLIED),
        "remains_external": list(REMAINS_EXTERNAL),
        "theorems": {name: name in text for name in theorem_names},
        "gates": {
            "adapter_exists": LEAN.is_file(),
            "all_factorization_theorems_present": all(name in text for name in theorem_names),
            "geometry_is_not_hidden_in_adapter_structure": not any(
                token in text for token in forbidden_structure_tokens
            ),
            "physical_mass_interpretation_remains_external": any(
                "interpretation as inertial or gravitational mass" == item
                for item in REMAINS_EXTERNAL
            ),
            "program_p_action_is_not_supplied": any(
                "selected action" in item for item in REMAINS_EXTERNAL
            ),
        },
        "conclusion": (
            "nonzero odd M charges conditionally supply P's binary signed-sector "
            "input and source algebra, but no geometry, mass interpretation or action"
        ),
        "scope": "narrow algebraic adapter to Program P's registered JanusCharge interface",
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
