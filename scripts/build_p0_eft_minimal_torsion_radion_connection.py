from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_minimal_torsion_radion_connection.md")
JSON_PATH = Path("outputs/reports/p0_eft_minimal_torsion_radion_connection.json")


def build_payload() -> dict:
    ansatz = {
        "name": "axial_trace_torsion_radion_connection",
        "connection_form": "nabla_C = nabla_LC + q_A gamma5 gamma_mu grad^mu chi + q_T gamma_mu grad^mu chi",
        "minimal_reason": "Dirac fields couple naturally to axial torsion; trace torsion captures radion volume/solder variation",
        "free_symbols": ["q_A", "q_T"],
        "source_derived": False,
    }
    projected_options = [
        {
            "choice": "pure axial torsion",
            "condition": "q_T = 0",
            "expected": "parity-sensitive torsion heat-kernel terms",
            "risk": "may violate parity/orbifold-even filter unless paired across sheets",
        },
        {
            "choice": "pure trace torsion",
            "condition": "q_A = 0",
            "expected": "radion volume coupling terms",
            "risk": "may fail to generate double-dual structure",
        },
        {
            "choice": "orbifold-even paired torsion",
            "condition": "q_A^2 and q_T^2 enter; odd terms projected out",
            "expected": "best first local EFT test",
            "risk": "still needs exact heat-kernel coefficient calculation",
        },
    ]
    theorem_status = {
        "minimal_connection_ansatz_written": True,
        "source_derived_from_janus": False,
        "heat_kernel_square_done": False,
        "projection_rule_written": True,
        "prediction_ready": False,
    }
    return {
        "description": "Minimal torsion/radion connection ansatz for the Dirac-Cartan EFT heat-kernel test.",
        "status": "minimal-connection-ansatz-open",
        "theorem_status": theorem_status,
        "ansatz": ansatz,
        "projected_options": projected_options,
        "next_steps": [
            "square the Dirac-Cartan operator for the orbifold-even paired torsion option",
            "extract E_C and Omega_C to identify curvature-radion terms",
            "check if q_A/q_T ratios can be fixed by parity, orientation, or volume soldering",
        ],
        "verdict": (
            "This is enough to start a symbolic heat-kernel square, but q_A/q_T are not Janus-derived yet."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Minimal Torsion-Radion Connection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Ansatz"])
    for key, value in payload["ansatz"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Projected Options"])
    for row in payload["projected_options"]:
        lines.append(f"- {row['choice']}: {row['condition']} -> {row['expected']}")
    lines.extend(["", "## Next Steps"])
    lines.extend(f"- {item}" for item in payload["next_steps"])
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
