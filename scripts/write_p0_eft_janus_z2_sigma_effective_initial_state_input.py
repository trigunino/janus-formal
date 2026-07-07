from __future__ import annotations

import argparse
import json
from pathlib import Path

from src.janus_lab.z2_sigma_projected_occupation_state import (
    validate_projected_occupation_state_payload,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/projected_occupation_state_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_initial_state_input.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_initial_state_input.json")


def build_payload(*, n_occ: float, provenance: str) -> dict:
    occupation = validate_projected_occupation_state_payload(
        {
            "active_core": "Z2_tunnel_Sigma",
            "source": "explicit_state_initial_data",
            "full_no_fit_prediction_ready": False,
            "N_occ_Z2Sigma": n_occ,
            "N_occ_provenance": provenance,
        }
    )
    return {
        "status": "janus-z2-sigma-effective-initial-state-input",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "effective_initial_state",
        "no_fit_branch_closed": False,
        "full_no_fit_prediction_ready": False,
        "occupation_manifest": occupation,
        "next_writers": [
            "write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation.py",
            "write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state.py",
        ],
        "gate_passed": True,
    }


def write_outputs(payload: dict, *, output_path: Path = OUTPUT_PATH) -> dict:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(payload["occupation_manifest"], indent=2),
        encoding="utf-8",
    )
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Effective Initial State Input",
                "",
                f"Branch: `{payload['branch']}`",
                f"No-fit branch closed: `{payload['no_fit_branch_closed']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
                f"N_occ: `{payload['occupation_manifest']['N_occ_Z2Sigma']}`",
                f"Provenance: `{payload['occupation_manifest']['N_occ_provenance']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Write explicit effective initial-state occupation input for Z2/Sigma."
    )
    parser.add_argument("--n-occ", type=float, required=True)
    parser.add_argument("--provenance", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    args = parser.parse_args()
    print(json.dumps(write_outputs(build_payload(n_occ=args.n_occ, provenance=args.provenance), output_path=args.output), indent=2))


if __name__ == "__main__":
    main()
