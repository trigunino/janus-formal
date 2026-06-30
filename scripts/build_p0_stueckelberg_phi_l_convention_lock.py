from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_phi_l_convention_lock.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_phi_l_convention_lock.json")


def build_payload() -> dict:
    locked_conventions = [
        {
            "name": "single_map_pair",
            "rule": "phi_minus_to_plus and phi_plus_to_minus are inverses on the supported dust domain",
            "needed_for": "mirror residuals are not independent fits",
        },
        {
            "name": "single_lorentz_transport",
            "rule": "the same L defines transported velocity, K_plus/K_minus, and Q_cross",
            "needed_for": "forbid separate lensing and matter transport normalizations",
        },
        {
            "name": "density_volume_measure",
            "rule": "B rho is the receiver-sector effective density once the volume convention is chosen",
            "needed_for": "prevent double counting Q_det/Jacobian/DlogB",
        },
        {
            "name": "projected_dust_variation",
            "rule": "h E_map equals transverse divergence of transported dust stress",
            "needed_for": "source-derived rho h Cuu without a transverse multiplier",
        },
    ]
    failure_modes = [
        "using one map for K and another map for Q_cross",
        "double counting by multiplying by B after already absorbing B into effective density",
        "treating plus and minus projected equations as independent constraints",
        "promoting dust-only projected closure to pressure/Pi closure",
    ]
    decision = {
        "conventions_locked_as_requirements": True,
        "dust_branch_can_be_tested": True,
        "dust_branch_closed": False,
        "prediction_ready": False,
        "reason": (
            "The projected dust identity is usable only with one locked convention set. "
            "These rules make the next derivation falsifiable: either the same phi/L "
            "and volume convention produce both mirror equations, or the branch fails."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_phi_l_convention_lock",
        "status": "convention-lock-for-next-derivation",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "locked_conventions": locked_conventions,
        "failure_modes": failure_modes,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Phi/L Convention Lock",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Locked Conventions",
    ]
    for row in payload["locked_conventions"]:
        lines.append(f"- {row['name']}: {row['rule']}")
        lines.append(f"  - needed for: {row['needed_for']}")
    lines.extend(["", "## Failure Modes"])
    lines.extend(f"- {item}" for item in payload["failure_modes"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Conventions locked as requirements: {decision['conventions_locked_as_requirements']}",
            f"Dust branch can be tested: {decision['dust_branch_can_be_tested']}",
            f"Dust branch closed: {decision['dust_branch_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
