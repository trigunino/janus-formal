from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_same_l_phase_space_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_same_l_phase_space_bridge.json")


def build_payload() -> dict:
    bridge = {
        "configuration_map": "phi: M_other -> M_self from Janus tetrad soldering",
        "cotangent_lift": "Phi(x,p)=(phi(x), (D phi^{-1})^T p)",
        "same_L_condition": "Hamiltonian/geodesic action is preserved under cotangent lift",
        "symplectic_property": "cotangent lift preserves canonical phase-space volume",
    }
    jacobian = {
        "full_phase_space": "|det D Phi| = 1 for canonical cotangent lift",
        "mass_shell_measure": "remaining factor depends on lapse/energy shell normalization",
        "stress_measure": "B4vol still needed for active gravitational source density",
        "result": "Liouville volume closes; active matter volume remains B4vol-dependent",
    }
    theorem_status = {
        "same_L_bridge_defined_as_cotangent_lift": True,
        "liouville_phase_space_jacobian_closed": True,
        "mass_shell_measure_closed": False,
        "active_B4vol_measure_closed": False,
        "stress_tensor_moments_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive mass-shell/lapse normalization for the transported measure",
        "connect B4vol active source measure to the same soldering convention",
        "then compute stress-tensor moments rho, p, Pi",
    ]
    return {
        "description": "Same-L phase-space bridge via cotangent lift and Liouville measure.",
        "status": "liouville-bridge-closed-active-measure-open",
        "bridge": bridge,
        "jacobian": jacobian,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The canonical phase-space bridge closes for Liouville volume: |det D Phi|=1. "
            "The remaining matter closure is the mass-shell/lapse factor and B4vol active source measure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Same-L Phase-Space Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Bridge",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["bridge"].items())
    lines.extend(["", "## Jacobian"])
    lines.extend(f"- {key}: {value}" for key, value in payload["jacobian"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
