from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_global_topology_closure_requirements import build_payload as build_run5


REPORT_PATH = Path("outputs/reports/p0_eft_run6_global_topology_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_run6_global_topology_scaffold.json")


def build_payload() -> dict:
    run5 = build_run5()
    return {
        "description": "RUN 6 pure topology scaffold: global assumptions imply local Janus locks.",
        "local_closed": {
            "nieh_yan_eta_H_plus_2_residual": run5["local_identities"][
                "eta_H_plus_2_residual"
            ],
            "orbifold_3a_sigma_minus_2_residual": run5["local_identities"][
                "three_a_sigma_minus_2_residual"
            ],
            "sdss_eboss_branch_status": "accepted in Holst/membrane co-optimisation",
        },
        "axiomatic_global_interfaces": {
            "aps_pin_trace_normalization": {
                "lean_module": "P0EFTAPSPinTraceNormalization",
                "run7_lean_module": "P0EFTAPSPinTraceGlobalDerivation",
                "global_hypothesis": "Pin- APS eta regularization fixes trace rank 4 and rank-half projector",
                "local_consequence": "eta_H + 2 = 0",
            },
            "orbifold_volume_cover": {
                "lean_module": "P0EFTOrbifoldVolumeCoverClassification",
                "run8_lean_module": "P0EFTOrbifoldVolumeDerivation",
                "global_hypothesis": "Janus Z2 Euler/holonomy class fixes Vol_+:Vol_-=2:1",
                "local_consequence": "3*a_sigma - 2 = 0",
            },
        },
        "blocking_conjectures": [
            "derive APS/Pin- trace normalization from the global index calculation",
            "derive the 2:1 volume cover from the global orbifold holonomy classification",
        ],
        "theorem_status": {
            "run6_scaffold_ready": True,
            "numeric_solver_untouched": True,
            "aps_pin_global_theorem_proved": False,
            "orbifold_cover_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 6 Global Topology Scaffold",
        "",
        payload["description"],
        "",
        "## Local Closed",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["local_closed"].items())
    lines.extend(["", "## Axiomatic Global Interfaces"])
    for key, item in payload["axiomatic_global_interfaces"].items():
        lines.extend(
            [
                f"- {key}",
                f"  - lean_module: {item['lean_module']}",
                f"  - global_hypothesis: {item['global_hypothesis']}",
                f"  - local_consequence: {item['local_consequence']}",
            ]
        )
        if "run7_lean_module" in item:
            lines.append(f"  - run7_lean_module: {item['run7_lean_module']}")
        if "run8_lean_module" in item:
            lines.append(f"  - run8_lean_module: {item['run8_lean_module']}")
    lines.extend(["", "## Blocking Conjectures"])
    lines.extend(f"- {item}" for item in payload["blocking_conjectures"])
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.append("")
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
