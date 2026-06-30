from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_nieh_yan_anomaly_derivation import build_payload as build_eta_payload
from scripts.build_p0_eft_orbifold_holonomy_quantization import build_payload as build_sigma_payload


REPORT_PATH = Path("outputs/reports/global_topology_closure_requirements.md")
JSON_PATH = Path("outputs/reports/global_topology_closure_requirements.json")


def build_payload() -> dict:
    eta = build_eta_payload()
    sigma = build_sigma_payload()
    return {
        "description": "RUN 5 audit of the global topology assumptions still blocking no-fit closure.",
        "local_identities": {
            "eta_H_plus_2_residual": eta["derivation"]["identity_residual_eta_H_plus_2"],
            "three_a_sigma_minus_2_residual": sigma["derivation"][
                "identity_residual_3a_sigma_minus_2"
            ],
        },
        "global_requirements": {
            "aps_trace_normalization": {
                "needed_statement": (
                    "APS/Pin- index fixes the four-component Clifford trace and rank-half "
                    "boundary projector normalization used by the Nieh-Yan trace."
                ),
                "current_status": "open",
                "blocks": "eta_H_derived_from_Holst_Nieh_Yan_trace",
            },
            "orbifold_2_to_1_cover": {
                "needed_statement": (
                    "Global Janus Z2 orbifold Euler/holonomy classification fixes "
                    "Vol_+:Vol_-=2:1 and excludes competing fractions."
                ),
                "current_status": "open",
                "blocks": "a_sigma_derived_from_orbifold_holonomy",
            },
        },
        "theorem_status": {
            "local_eta_identity_closed": True,
            "local_a_sigma_identity_closed": True,
            "run6_aps_pin_interface_scaffolded": True,
            "run6_orbifold_cover_interface_scaffolded": True,
            "run8_orbifold_volume_derivation_scaffolded": True,
            "aps_global_normalization_closed": False,
            "orbifold_global_cover_closed": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
        "verdict": (
            "RUN 5 reduces the remaining no-fit proof to two global topology lemmas. "
            "No numerical or local algebraic blocker remains, but the APS normalization "
            "and Z2 cover ratio are not yet derived from a global index calculation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Global Topology Closure Requirements",
        "",
        payload["description"],
        "",
        "## Local Identities",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["local_identities"].items())
    lines.extend(["", "## Global Requirements"])
    for key, item in payload["global_requirements"].items():
        lines.extend(
            [
                f"- {key}",
                f"  - needed_statement: {item['needed_statement']}",
                f"  - current_status: {item['current_status']}",
                f"  - blocks: {item['blocks']}",
            ]
        )
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
