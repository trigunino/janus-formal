from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_heat_kernel_obligation_map.md")
JSON_PATH = Path("outputs/reports/p0_eft_heat_kernel_obligation_map.json")


def build_payload() -> dict:
    required_inputs = [
        {
            "id": "HK1",
            "name": "bulk field spectrum",
            "needed_for": "sign and magnitude of Wilsonian coefficients",
            "available_now": False,
        },
        {
            "id": "HK2",
            "name": "bulk masses and cutoff scale",
            "needed_for": "local derivative expansion and decoupling",
            "available_now": False,
        },
        {
            "id": "HK3",
            "name": "radion/torsion coupling operator",
            "needed_for": "whether heat-kernel generates curvature-radion terms at all",
            "available_now": False,
        },
        {
            "id": "HK4",
            "name": "orbifold boundary conditions",
            "needed_for": "boundary Seeley-DeWitt coefficients and projection",
            "available_now": False,
        },
        {
            "id": "HK5",
            "name": "degeneracy/no-ghost projection rule",
            "needed_for": "removing non-Horndeski operators from the tower",
            "available_now": True,
        },
    ]
    heat_kernel_chain = [
        "choose elliptic/Dirac-type bulk operator D_Janus",
        "compute log det D_Janus by heat-kernel expansion",
        "extract curvature-radion operators from a2/a4 coefficients",
        "apply orbifold boundary coefficients",
        "project to degenerate Horndeski/double-dual combination",
        "match generated local coefficient to dS contact closure",
    ]
    theorem_status = {
        "obligation_map_written": True,
        "heat_kernel_operator_specified": False,
        "seeley_dewitt_coefficients_computed": False,
        "double_dual_generated": False,
        "non_horndeski_terms_projected": False,
        "prediction_ready": False,
    }
    return {
        "description": "Minimal obligation map for turning the EFT loop route into a real derivation.",
        "status": "heat-kernel-inputs-missing",
        "theorem_status": theorem_status,
        "required_inputs": required_inputs,
        "heat_kernel_chain": heat_kernel_chain,
        "verdict": (
            "No more conceptual input is needed to continue scaffolding. A real derivation now "
            "requires physical input: bulk spectrum, masses/cutoff, radion/torsion couplings, "
            "and orbifold boundary conditions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Heat-Kernel Obligation Map",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Required Inputs"])
    for row in payload["required_inputs"]:
        lines.append(
            f"- {row['id']}: {row['name']} "
            f"(available_now={row['available_now']}) -> {row['needed_for']}"
        )
    lines.extend(["", "## Heat-Kernel Chain"])
    lines.extend(f"- {item}" for item in payload["heat_kernel_chain"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
